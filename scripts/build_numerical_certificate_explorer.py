#!/usr/bin/env python3
"""Build the certificate explorer from a frozen, compiled optional proof graph.

Ordinary --check validates fingerprints, full source hashes, proof audits and
deterministic presentation assets. Only explicit --refresh invokes Lake for
the optional target; unchanged compiled certificate components are reused.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

import build_theorem_explorer as explorer
from numerical_certificate import closure, fingerprint

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "docs/numerical-certificate-explorer"
SHARED = ROOT / "docs/theorem-explorer"
RAW = ROOT / ".lake/numerical-certificate-explorer/lean-graph.json"
AUDIT = ROOT / "docs/numerical-certificate-audit.json"
EXPORTER = ROOT / "scripts/ExportNumericalCertificateExplorer.lean"


def lean_command():
    lake = shutil.which("lake")
    if lake:
        return [lake]
    elan = ROOT.parent / ".lean/elan"
    assert (elan / "bin/lake").is_file(), "Install the pinned Lean toolchain"
    return ["env", f"ELAN_HOME={elan}", str(elan / "bin/lake")]


def input_sources():
    return {p.relative_to(ROOT).as_posix(): explorer.digest(p.read_bytes())
            for p in sorted(set(closure("NumericalCertificate").values()))}


def checked_audit():
    audit = json.loads(AUDIT.read_bytes())
    assert audit["target"] == "NumericalCertificate"
    assert audit["inputSha256"] == fingerprint(), "Certificate inputs changed; rerun optional verification"
    assert audit["axiomAudit"] == "passed: only propext, Classical.choice, Quot.sound"
    assert audit["certificateStatus"] == "proved: 6731/10000 for literal simple critical-line zeros"
    return audit


def refresh():
    audit = checked_audit()
    before = fingerprint()
    # Explicitly requested refresh only: Lake validates its cached traces.
    subprocess.run(lean_command() + ["build", "NumericalCertificate", "--wfail"], cwd=ROOT, check=True)
    subprocess.run(lean_command() + ["env", "lean", "-DwarningAsError=true", str(EXPORTER)], cwd=ROOT, check=True)
    assert fingerprint() == before, "Certificate inputs changed during graph export"
    raw = RAW.read_bytes()
    snapshot = {"schemaVersion": 1, "inputSha256": before,
                "rawGraphSha256": explorer.digest(raw),
                "exporterSha256": explorer.digest(EXPORTER.read_bytes()),
                "certificateAuditSha256": explorer.digest(AUDIT.read_bytes()),
                "sourceSha256": input_sources(), "leanVersion": audit["leanVersion"],
                "scope": "Compiled authored dependency graph; generated data are explicit, fully axiom-audited proof boundaries. The complete optional audit checks every generated component."}
    SITE.mkdir(parents=True, exist_ok=True)
    (SITE / "lean-graph.json.gz").write_bytes(explorer.gzip_bytes(raw))
    (SITE / "snapshot.json").write_bytes(explorer.json_bytes(snapshot))


def build():
    audit = checked_audit()
    snapshot = json.loads((SITE / "snapshot.json").read_bytes())
    raw_bytes = explorer.gzip.decompress((SITE / "lean-graph.json.gz").read_bytes())
    assert snapshot["inputSha256"] == audit["inputSha256"], "Stale optional proof graph"
    assert snapshot["rawGraphSha256"] == explorer.digest(raw_bytes), "Proof graph hash mismatch"
    assert snapshot["exporterSha256"] == explorer.digest(EXPORTER.read_bytes()), "Graph exporter changed; refresh explicitly"
    assert snapshot["certificateAuditSha256"] == explorer.digest(AUDIT.read_bytes()), "Optional audit changed; refresh explicitly"
    assert snapshot["sourceSha256"] == input_sources(), "Optional proof source snapshot changed"
    raw = json.loads(raw_bytes)
    assert raw["leanVersion"] == audit["leanVersion"]
    meta = json.loads((SITE / "metadata.json").read_bytes())
    taxonomy = json.loads((SHARED / "metadata.json").read_bytes())
    # One evergreen mathematical-family taxonomy for both explorers.
    meta["families"] = taxonomy["families"]
    meta["moduleFamilies"] = taxonomy["moduleFamilies"]
    verification_path = ROOT / "docs/numerical-certificate/verification.json"
    verification = json.loads(verification_path.read_bytes())
    hosted_path = ROOT / verification["auditPath"]
    hosted = json.loads(hosted_path.read_bytes())
    assert verification["conclusion"] == "success"
    assert verification["inputSha256"] == audit["inputSha256"] == hosted["inputSha256"]
    assert verification["auditSha256"] == explorer.digest(hosted_path.read_bytes())
    for field in ("target", "scope", "schemaVersion", "leanVersion", "certificateStatus", "axiomAudit"):
        assert audit[field] == hosted[field], f"Hosted audit differs: {field}"
    meta["certificateVerification"] = verification
    meta["guideDocument"] = "docs/numerical-certificate.md"
    meta["metadataOrigin"] = "Read from the certificate endpoint metadata and complete optional proof audit."
    for n in raw["nodes"]:
        if n.get("verifiedDataBoundary"):
            label = meta["theorems"].setdefault(n["id"], {})
            label["summary"] = (n["doc"].strip() + " Generated-data proof boundary: its complete "
                                "transitive axioms are checked; all underlying data and cover groups "
                                "are verified by the separately linked optional certificate workflow.")
    status = {"leanVersion": audit["leanVersion"], "projectAxioms": 0,
              "placeholderDependentDeclarations": 0, "nonstandardTheoremAxioms": [],
              "rhImplied": False, "certificate": meta["certificate"],
              "gaussianPhaseBandToolkit": {"comparisonScope": meta["certificate"]["scope"]}}
    with tempfile.TemporaryDirectory(prefix="riemann-certificate-graph-") as directory:
        path = Path(directory) / "graph.json"
        path.write_bytes(raw_bytes)
        outputs = explorer.build(raw_path=path, metadata=meta, status_data=status)
    outputs["certificate-audit.json"] = AUDIT.read_bytes()
    outputs["hosted-audit.json"] = hosted_path.read_bytes()
    outputs["verification.json"] = verification_path.read_bytes()
    outputs["families.json"] = explorer.json_bytes({"source": "docs/theorem-explorer/metadata.json",
        "families": taxonomy["families"], "moduleFamilies": taxonomy["moduleFamilies"]})
    # Share the complete tested interaction code instead of forking a viewer.
    for name in ("app.js", "graph-core.js", "style.css", "source.html", "document.html",
                 "snapshot.js", "snapshot.css"):
        outputs[name] = (SHARED / name).read_bytes()
    html = (SHARED / "index.html").read_text()
    html = html.replace("The zero-free region · RiemannGaussian proof explorer", meta["title"] + " · RiemannGaussian")
    html = html.replace("The mathematics behind the zero-free region", "The proof behind the 67.31% certificate")
    html = html.replace("RiemannGaussian's zero-free region", "RiemannGaussian's numerical zero certificate")
    html = html.replace('href="metadata.json" target="_blank" rel="noopener">Family metadata',
                        'href="families.json" target="_blank" rel="noopener">Family metadata')
    html = html.replace('<a href="audit.json" target="_blank" rel="noopener">Axiom audit</a>',
                        '<a href="audit.json" target="_blank" rel="noopener">Graph audit</a> · '
                        '<a href="certificate-audit.json" target="_blank" rel="noopener">Complete certificate audit</a> · '
                        '<a href="snapshot.json" target="_blank" rel="noopener">Checked inputs</a>')
    html = html.replace("Project dependencies are followed to external Lean/mathlib declarations, which are boundary leaves. Their complete transitive axiom dependencies are still audited. The overview hides detail; the raw export preserves it.",
                        "Authored dependencies are followed to external Lean/mathlib declarations and explicitly marked generated-data proof boundaries. Their complete transitive axioms are audited. The separate optional workflow checks every underlying range, anchor and cover group; ordinary CI checks this frozen snapshot without repeating the exhaustive certificate.")
    outputs["index.html"] = html.encode()
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh", action="store_true", help="Explicitly refresh from the cached optional Lean target")
    parser.add_argument("--check", action="store_true", help="Fast freshness checks; never invokes optional Lean")
    parser.add_argument("--node", default="node")
    args = parser.parse_args()
    assert not (args.refresh and args.check), "Refresh and ordinary checks are distinct actions"
    if args.refresh:
        refresh()
    outputs = build()
    for name, content in outputs.items():
        path = SITE / name
        if args.check:
            assert path.is_file() and path.read_bytes() == content, f"Stale certificate explorer asset: {name}"
        else:
            path.write_bytes(content)
    preview = subprocess.check_output([args.node, str(ROOT / "scripts/render_theorem_preview.cjs"),
                                       "--certificate"], cwd=ROOT)
    if args.check:
        assert (SITE / "preview.svg").read_bytes() == preview, "Stale certificate proof preview"
    else:
        (SITE / "preview.svg").write_bytes(preview)
    subprocess.run([args.node, str(ROOT / "scripts/check_theorem_graph.cjs"), str(SITE)], cwd=ROOT, check=True)
    print("Certificate explorer, compiled proof boundaries, source hashes and optional input fingerprint are consistent.")


if __name__ == "__main__":
    main()
