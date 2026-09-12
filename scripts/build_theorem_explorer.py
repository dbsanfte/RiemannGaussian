#!/usr/bin/env python3
"""Join Lean's dependency export to evergreen descriptions; build a static site.

No edges or proof claims are inferred from prose. The raw, audited Lean export
is downloadable, including references omitted from the opening overview.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "docs/theorem-explorer"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True) + "\n").encode()


def digest(content):
    return hashlib.sha256(content).hexdigest()


def gzip_bytes(content):
    # GzipFile fixes mtime/name and the OS header across Python versions;
    # gzip.compress(mtime=0) writes different OS bytes in Python 3.10/3.12.
    buffer = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=buffer, mtime=0) as stream:
        stream.write(content)
    return buffer.getvalue()


def at_path(value, path):
    for key in path:
        value = value[key]
    return value


def build():
    raw_bytes = (ROOT / ".lake/theorem-explorer/lean-graph.json").read_bytes()
    raw = json.loads(raw_bytes)
    meta_bytes = (SITE / "metadata.json").read_bytes()
    meta = json.loads(meta_bytes)
    status_bytes = (ROOT / "docs/proof-status.json").read_bytes()
    status = json.loads(status_bytes)
    manifest = json.loads((ROOT / "lake-manifest.json").read_bytes())
    assert raw["leanVersion"] == status["leanVersion"], "Lean versions differ"
    for key in ("projectAxioms", "placeholderDependentDeclarations"):
        assert status[key] == 0, f"Failed project audit: {key}"
    assert status["nonstandardTheoremAxioms"] == [], "Failed transitive project audit"
    assert raw["schemaVersion"] == meta["schemaVersion"] == 1
    index = {n["id"]: i for i, n in enumerate(raw["nodes"])}
    assert len(index) == len(raw["nodes"]), "Duplicate declaration names"
    for name in meta["theorems"]:
        assert name in index, f"Stale theorem metadata: {name}"
    families = {f["id"]: f for f in meta["families"]}
    assert len(families) == len(meta["families"]), "Duplicate family IDs"
    for f in families.values():
        assert re.fullmatch(r"#[0-9a-fA-F]{6}", f["color"])
    for f in meta["moduleFamilies"].values():
        assert f in families, f"Unknown family {f}"

    # Existing toolkit metadata is the source of documentation/audit links.
    by_theorem, by_module = {}, {}
    def theorem_names(obj):
        if isinstance(obj, str) and obj in index:
            yield obj
        elif isinstance(obj, dict):
            for value in obj.values():
                yield from theorem_names(value)
        elif isinstance(obj, list):
            for value in obj:
                yield from theorem_names(value)
    for key, value in status.items():
        if not isinstance(value, dict):
            continue
        doc = value.get("documentation")
        if doc:
            assert (ROOT / doc).is_file(), f"Missing toolkit documentation: {doc}"
        for name in theorem_names(value):
            by_theorem.setdefault(name, []).append({"key": key, "documentation": doc})
            module = raw["nodes"][index[name]]["module"]
            if doc:
                by_module.setdefault(module, set()).add(doc)

    project_sources, source_hashes, modules = {}, {}, {}
    nodes, family_counts = [], {f: 0 for f in families}
    toolchain_sources = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan"))) / "toolchains"
    toolchain_sources /= f"leanprover--lean4---v{raw['leanVersion']}/src/lean"
    packages = [(ROOT / ".lake/packages" / p["name"], p["url"], p["rev"])
                for p in manifest["packages"] if p["type"] == "git"]

    for n in raw["nodes"]:
        assert set(n["axioms"]) <= STANDARD_AXIOMS, f"Failed axiom audit: {n['id']}"
        assert not (n["project"] and n["kind"] == "axiom"), "Project axiom"
        override = meta["theorems"].get(n["id"], {})
        short_module = (n["module"] or "").removeprefix("RiemannGaussian.")
        if not n["project"]:
            family = "library"
        elif "family" in override:
            family = override["family"]
        elif short_module in meta["moduleFamilies"]:
            family = meta["moduleFamilies"][short_module]
        else:
            matches = [(len(prefix), f["id"]) for f in families.values()
                       for prefix in f["modulePrefixes"] if short_module.startswith(prefix)]
            assert matches, f"Assign a logical family to {short_module} in metadata.json"
            family = max(matches)[1]
        assert family in families
        family_counts[family] += 1
        location = n["location"]
        source_module = (location or {}).get("module") or n["module"]
        source_path = source_module.replace(".", "/") + ".lean" if source_module else None
        source = None
        if n["project"] and source_path:
            path = ROOT / source_path
            assert path.is_file(), f"Missing project source: {source_path}"
            if source_path not in project_sources:
                content = path.read_bytes()
                project_sources[source_path] = content.decode()
                source_hashes[source_path] = digest(content)
            if location:
                lines = project_sources[source_path].splitlines()
                assert 1 <= location["line"] <= len(lines), f"Invalid source line: {n['id']}"
                if location["exact"]:
                    token = location["declaration"].split(".")[-1]
                    text = lines[location["line"] - 1]
                    anonymous_instance = token.startswith("inst") and re.search(r"\binstance\s*:", text)
                    assert token in text or anonymous_instance, f"Source declaration moved: {n['id']}"
            source = {"path": source_path, "line": (location or {}).get("line"),
                      "exact": (location or {}).get("exact", False), "project": True,
                      "declaration": (location or {}).get("declaration")}
        elif source_path and location:
            for directory, repo, revision in packages:
                if (directory / source_path).is_file():
                    source = {"url": f"{repo.removesuffix('.git')}/blob/{revision}/{source_path}#L{location['line']}",
                              "path": source_path, "line": location["line"], "exact": location["exact"], "project": False}
                    break
            if not source and (toolchain_sources / source_path).is_file():
                source = {"url": f"https://github.com/leanprover/lean4/blob/v{raw['leanVersion']}/src/lean/{source_path}#L{location['line']}",
                          "path": source_path, "line": location["line"], "exact": location["exact"], "project": False}
        if n["project"]:
            assert source and source["line"], f"Unresolved project source: {n['id']}"
        info = {
            "id": n["id"], "name": n["displayName"], "module": n["module"],
            "kind": n["kind"], "project": n["project"], "family": family,
            "label": override.get("label", n["displayName"].split(".")[-1]),
            "summary": override.get("summary", n["doc"].strip()),
            "statement": n["statement"], "source": source, "axioms": n["axioms"],
            "overview": bool(override.get("overview")),
            "generated": bool(location and not location["exact"]),
            "body": [index[d] for d in n["bodyDependencies"]],
            "typeRefs": [index[d] for d in n["typeDependencies"]],
            "constructors": [index[d] for d in n["constructorDependencies"]],
            "toolkits": by_theorem.get(n["id"], []),
            "documentation": sorted(by_module.get(n["module"], set()))
        }
        if "documentation" in override:
            assert (ROOT / override["documentation"]).is_file()
            info["documentation"].insert(0, override["documentation"])
        nodes.append(info)
        modules.setdefault(n["module"], []).append(index[n["id"]])

    endpoints = []
    for e in meta["endpoints"]:
        names = [at_path(status, path) for path in e["statusPaths"]]
        exported = next(r["theorems"] for r in raw["endpoints"] if r["id"] == e["id"])
        assert sorted(names) == sorted(exported), "Endpoint metadata differs from Lean export"
        endpoints.append({**e, "roots": [index[n] for n in names], "scope": at_path(status, e["scopePath"])})
    assert meta["defaultEndpoint"] in {e["id"] for e in endpoints}
    audit = {
        "schemaVersion": 1, "generator": raw["generator"], "leanVersion": raw["leanVersion"],
        "rawGraphSha256": digest(raw_bytes), "metadataSha256": digest(meta_bytes),
        "projectStatusSha256": digest(status_bytes), "sourceSha256": source_hashes,
        "declarations": len(nodes), "projectDeclarations": sum(n["project"] for n in nodes),
        "projectTheorems": sum(n["project"] and n["kind"] == "theorem" for n in nodes),
        "externalLeaves": sum(not n["project"] for n in nodes),
        "standardAxiomsOnly": True, "allowedAxioms": sorted(STANDARD_AXIOMS),
        "projectAxioms": 0, "nonstandardAxioms": [], "allProjectSourceLocationsResolved": True,
        "edgeMeaning": raw["edgeMeaning"], "externalBoundary": raw["externalBoundary"],
        "endpointAxioms": {nodes[i]["id"]: nodes[i]["axioms"] for e in endpoints for i in e["roots"]},
        "familyCounts": family_counts,
        "verificationScope": "The exporter runs in the compiled Lean root and collects transitive axioms for every node. This file does not itself certify a GitHub Actions run; published deployment provenance links to the exact run separately.",
        "rhImplied": status["rhImplied"]
    }
    data = {
        "schemaVersion": 1, "repository": meta["repository"], "defaultEndpoint": meta["defaultEndpoint"],
        "families": meta["families"], "endpoints": endpoints, "nodes": nodes,
        "leanVersion": raw["leanVersion"], "audit": {k: v for k, v in audit.items() if k != "sourceSha256"},
        "benchmarkScope": status["gaussianPhaseBandToolkit"]["comparisonScope"],
        "limitNote": "RH remains open. The three checked benchmark functions are not an exhaustive world-record audit.",
        "toolkits": {k: v for k, v in status.items() if isinstance(v, dict)}
    }
    document_paths = {p for n in nodes for p in n["documentation"]}
    document_paths.update(e["documentation"] for e in endpoints)
    document_paths.add("docs/theorem-explorer.md")
    documents = {p: (ROOT / p).read_text() for p in sorted(document_paths)}
    return {
        "data.js": b"// Generated; edit metadata.json or the Lean documentation.\nwindow.PROOF_DATA=" + json_bytes(data) + b";\n",
        "sources.js": b"// Exact local sources, for unpublished snapshots and offline source viewing.\nwindow.PROOF_SOURCES=" + json_bytes(project_sources) + b";\n",
        "documents.js": b"// Exact local proof documentation snapshots.\nwindow.PROOF_DOCUMENTS=" + json_bytes(documents) + b";\n",
        "audit.json": json_bytes(audit),
        "lean-graph.json.gz": gzip_bytes(raw_bytes),
        "release.js": b"// CI supplies a commit and run only when publishing this exact source snapshot.\nwindow.PROOF_RELEASE=null;\n",
        ".nojekyll": b""
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Reject stale generated assets")
    parser.add_argument("--site", type=Path, help="Assemble a Pages artifact in this directory")
    parser.add_argument("--revision", help="Exact committed source SHA for a Pages artifact")
    parser.add_argument("--run-url", help="Exact verification workflow run for the Pages artifact")
    parser.add_argument("--node", default="node", help="Node executable for deterministic SVG rendering")
    args = parser.parse_args()
    outputs = build()
    for name, content in outputs.items():
        path = SITE / name
        if args.check:
            assert path.is_file() and path.read_bytes() == content, f"Stale generated asset: {path.relative_to(ROOT)}"
        else:
            path.write_bytes(content)
    preview = subprocess.check_output([args.node, str(ROOT / "scripts/render_theorem_preview.cjs")], cwd=ROOT)
    if args.check:
        assert (SITE / "preview.svg").read_bytes() == preview, "Stale theorem preview"
    else:
        (SITE / "preview.svg").write_bytes(preview)
    if args.site:
        assert args.revision and re.fullmatch(r"[0-9a-f]{40}", args.revision), "Publication requires an exact SHA"
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        assert args.revision == actual, "Publication SHA does not match checkout"
        assert not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=all"], cwd=ROOT), "Publication requires a clean checked tree"
        assert args.run_url and args.run_url.startswith("https://github.com/dbsanfte/RiemannGaussian/actions/runs/")
        artifact_root = (ROOT / ".lake/theorem-explorer").resolve()
        artifact_path = args.site.resolve()
        assert artifact_path != artifact_root and artifact_path.is_relative_to(artifact_root), "Pages artifacts belong in .lake/theorem-explorer/<directory>"
        if args.site.exists():
            shutil.rmtree(args.site)
        args.site.mkdir(parents=True, exist_ok=True)
        for path in SITE.iterdir():
            if path.is_file():
                shutil.copy2(path, args.site / path.name)
        shutil.copy2(ROOT / "docs/proof-status.json", args.site / "proof-status.json")
        release = {"revision": args.revision, "runUrl": args.run_url}
        (args.site / "release.js").write_bytes(b"window.PROOF_RELEASE=" + json_bytes(release) + b";\n")
    print("Theorem explorer assets and source/audit links are consistent.")


if __name__ == "__main__":
    main()
