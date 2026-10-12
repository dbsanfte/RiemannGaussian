#!/usr/bin/env python3
"""Preserve research evidence without Lake caches or dependency checkouts."""
from __future__ import annotations

import argparse
import collections
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import tarfile

FORMAL = Path(__file__).resolve().parents[3]
DEST = Path(__file__).resolve().parent
TEXT = {".json", ".log", ".md", ".py", ".lean", ".txt", ".tex", ".out", ".sha256", ".html", ".npz", ".png"}
DEPENDENCY_ROOTS = {"build", "packages", "plot-venv", "browser-venv", "rh-proof-explorer"}
PRUNE = {".git", ".lake", "__pycache__", "node_modules", "OAI", "Mathlib", "RellichKondrachov", "PrimeNumberTheoremAnd", "preprints"}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def candidate(value: str) -> Path | None:
    if "\n" in value or " " in value:
        return None
    if value.startswith(".lake/"):
        return FORMAL / value
    if value.startswith("/tmp/semiprime"):
        return Path(value)
    if value.startswith(str(FORMAL / ".lake") + "/"):
        return Path(value)
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--create", action="store_true", help="Explicitly write the evidence archive and manifest.")
    args = parser.parse_args()
    if not args.create:
        parser.error("Archive creation requires --create; verification is available in verify.py.")
    refs: dict[Path, set[str]] = collections.defaultdict(set)
    pins: dict[Path, set[str]] = collections.defaultdict(set)
    audit_digests = {}

    def walk(value, audit: str) -> None:
        if isinstance(value, str):
            p = candidate(value)
            if p is not None:
                refs[p].add(audit)
        elif isinstance(value, list):
            for item in value:
                walk(item, audit)
        elif isinstance(value, dict):
            for key, item in value.items():
                p = candidate(key)
                if p is not None and isinstance(item, str) and re.fullmatch(r"[0-9a-f]{64}", item):
                    pins[p].add(item)
                walk(key, audit)
                walk(item, audit)

    for audit in sorted((FORMAL / "docs").glob("*.json")):
        try:
            raw = audit.read_bytes()
            value = json.loads(raw)
        except (OSError, json.JSONDecodeError):
            continue
        name = str(audit.relative_to(FORMAL))
        before = len(refs)
        walk(value, name)
        if len(refs) != before or name.startswith("docs/semiprime"):
            audit_digests[name] = sha(raw)

    reasons: dict[Path, set[str]] = collections.defaultdict(set)
    exclusions = []
    for p, audits in refs.items():
        if not p.exists():
            exclusions.append({"originalPath": str(p), "reason": "missing historical reference", "audits": sorted(audits), "historicalPinHashes": sorted(pins[p])})
            continue
        if not p.is_file():
            continue
        if p.is_symlink():
            exclusions.append({"originalPath": str(p), "reason": "symlink or environment executable", "audits": sorted(audits)})
            continue
        relative = p.relative_to(FORMAL) if p.is_relative_to(FORMAL) else None
        if p.is_relative_to(FORMAL / ".lake/arithmetic-operator-roadmap/openai-math-review") or p.is_relative_to(Path("/tmp/semiprime-openai-math-20261007/preprints")):
            exclusions.append({"originalPath": str(p), "reason": "imported third-party project or paper-source subtree", "audits": sorted(audits), "historicalPinHashes": sorted(pins[p])})
            continue
        if relative is not None and relative.parts[0] == ".lake" and relative.parts[1] in DEPENDENCY_ROOTS:
            exclusions.append({"originalPath": str(p), "reason": "dependency checkout, build cache, environment, or duplicated generated explorer", "audits": sorted(audits), "historicalPinHashes": sorted(pins[p])})
            continue
        if p.suffix not in TEXT:
            exclusions.append({"originalPath": str(p), "reason": "compiled/generated cache or downloaded third-party binary document", "audits": sorted(audits), "historicalPinHashes": sorted(pins[p])})
            continue
        reasons[p].add("existing audit-referenced research evidence")

    # Direct research files only. The nested openai-math-review tree contains
    # an imported project and tens of gigabytes of build products.
    for d in sorted((FORMAL / ".lake").glob("arithmetic-operator-*")):
        if d.is_dir():
            for p in d.iterdir():
                if p.is_file() and not p.is_symlink() and p.suffix in TEXT:
                    reasons[p].add("direct arithmetic-operator research file")
    for p in (FORMAL / ".lake").glob("semiprime*"):
        if p.is_file() and not p.is_symlink() and p.suffix in TEXT:
            reasons[p].add("direct semiprime research evidence")
        elif p.is_dir():
            for q in p.iterdir():
                if q.is_file() and not q.is_symlink() and q.suffix in TEXT:
                    reasons[q].add("direct semiprime research evidence")

    roots = set()
    for audit in (FORMAL / "docs").glob("semiprime*.json"):
        for match in re.finditer(r"/tmp/(semiprime[^/\"\\ ]+)", audit.read_text()):
            p = Path("/tmp") / match.group(1)
            if p.is_dir():
                roots.add(p)
    for d in sorted(roots):
        for current, dirs, files in os.walk(d):
            dirs[:] = [x for x in dirs if x not in PRUNE]
            for filename in files:
                p = Path(current) / filename
                if p.is_file() and not p.is_symlink() and p.suffix in TEXT:
                    reasons[p].add("semiprime authored research, review, or historical registration snapshot")

    roadmap = FORMAL.parent / "arithmetic_operator_research_roadmap.md"
    if not roadmap.is_file():
        raise SystemExit(f"Missing requested roadmap: {roadmap}")
    reasons[roadmap].add("active external workspace roadmap")

    records = []
    credential_patterns = [r"BEGIN (?:RSA |OPENSSH |EC )?PRIVATE KEY", r"\bgh[pousr]_[A-Za-z0-9]{30,}", r"\bgithub_pat_[A-Za-z0-9_]{30,}", r"\bsk-(?:proj-)?[A-Za-z0-9_-]{40,}", r"\bAKIA[0-9A-Z]{16}"]
    archive = DEST / "evidence.tar.gz"
    with archive.open("wb") as out:
        with gzip.GzipFile(filename="", mode="wb", fileobj=out, mtime=0, compresslevel=9) as gz:
            with tarfile.open(fileobj=gz, mode="w|", format=tarfile.PAX_FORMAT) as tf:
                for p in sorted(reasons, key=str):
                    if p == roadmap:
                        member = "workspace/arithmetic_operator_research_roadmap.md"
                    elif p.is_relative_to(FORMAL):
                        member = str(p.relative_to(FORMAL))
                    elif p.is_relative_to(Path("/tmp")):
                        member = "tmp/" + str(p.relative_to(Path("/tmp")))
                    else:
                        raise SystemExit(f"Unexpected research path: {p}")
                    data = p.read_bytes()
                    if len(data) >= 100_000_000:
                        raise SystemExit(f"Unexpected large research file: {p}")
                    if p.suffix not in {".npz", ".png"}:
                        text = data.decode("utf-8", errors="replace")
                        if any(re.search(pattern, text) for pattern in credential_patterns):
                            raise SystemExit(f"Credential-like content requires review before archiving: {p}")
                    digest = sha(data)
                    info = tarfile.TarInfo(member)
                    info.size = len(data)
                    info.mode = 0o644
                    info.mtime = 0
                    tf.addfile(info, io.BytesIO(data))
                    expected = sorted(pins[p])
                    records.append({"member": member, "originalPath": str(p), "bytes": len(data), "sha256": digest, "reasons": sorted(reasons[p]), "referencedBy": sorted(refs[p]), "historicalPinHashes": expected, "historicalPinMatchesCurrentSnapshot": digest in expected if expected else None})

    manifest = {
        "schema": "portable-research-evidence-snapshot-v1",
        "snapshotDate": "2026-10-12",
        "scope": "Research evidence only; no new proof or source-scale arithmetic estimate is asserted.",
        "archive": archive.name,
        "archiveSha256": sha(archive.read_bytes()),
        "archiveBytes": archive.stat().st_size,
        "fileCount": len(records),
        "uncompressedBytes": sum(r["bytes"] for r in records),
        "historicalAuditsRewritten": False,
        "referencedAuditDigestsAtSnapshot": audit_digests,
        "excludedSubtrees": [".lake/build", ".lake/packages", ".lake/*-venv", ".lake/arithmetic-operator-roadmap/openai-math-review", "/tmp/semiprime-openai-math-20261007/preprints"],
        "excludedFileKinds": ["compiled Lean/native outputs", "dependency checkouts", "environment binaries", "downloaded PDF documents", "duplicated generated explorer graphs"],
        "files": records,
        "omittedReferences": sorted(exclusions, key=lambda r: r["originalPath"]),
    }
    (DEST / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({key: manifest[key] for key in ["fileCount", "uncompressedBytes", "archiveBytes", "archiveSha256"]}, indent=2))


if __name__ == "__main__":
    main()
