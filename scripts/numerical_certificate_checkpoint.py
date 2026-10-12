#!/usr/bin/env python3
"""Validate the historical certificate inputs without running its optional proof.

This preserves the published Lean 4.33.1 checkpoint during the ordinary
project's compiler migration. It never certifies the current optional target.
"""

from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "docs/numerical-certificate-explorer"


def checked_inputs(*, archive=None):
    snapshot_bytes = (SITE / "snapshot.json").read_bytes()
    snapshot = json.loads(snapshot_bytes)
    audit = json.loads((ROOT / "docs/numerical-certificate-audit.json").read_bytes())
    if archive is None:
        archive = json.loads(gzip.decompress((SITE / "lean433-inputs.json.gz").read_bytes()))
    assert archive["schemaVersion"] == 1
    assert archive["snapshotSha256"] == hashlib.sha256(snapshot_bytes).hexdigest()
    assert archive["inputSha256"] == snapshot["inputSha256"] == audit["inputSha256"]
    assert archive["leanVersion"] == snapshot["leanVersion"] == audit["leanVersion"]
    hashes, texts = archive["inputFileSha256"], archive["archivedText"]
    assert texts.keys() <= hashes.keys(), "Unpinned archival input"
    for name, digest in snapshot["sourceSha256"].items():
        assert hashes[name] == digest, f"Historical source pin differs: {name}"
    combined = hashlib.sha256()
    for path in sorted(map(Path, hashes)):
        name = path.as_posix()
        assert not path.is_absolute() and ".." not in path.parts, "Invalid archival input path"
        data = texts[name].encode() if name in texts else (ROOT / path).read_bytes()
        assert hashlib.sha256(data).hexdigest() == hashes[name], f"Historical input changed: {name}"
        combined.update(name.encode() + b"\0")
        combined.update(data + b"\0")
    assert combined.hexdigest() == audit["inputSha256"], "Historical certificate fingerprint differs"
    manifest = json.loads(texts.get("lake-manifest.json", (ROOT / "lake-manifest.json").read_text()))
    return {name: content.encode() for name, content in texts.items()}, manifest


if __name__ == "__main__":
    checked_inputs()
    print("Verified the frozen Lean 4.33.1 certificate inputs; current optional verification remains separate.")
