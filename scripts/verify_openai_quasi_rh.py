#!/usr/bin/env python3
"""Check the vendored external proof against its pinned source provenance."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / "vendor/openai-quasi-rh"


def main() -> None:
    pin = json.loads((VENDOR / "upstream-pin.json").read_text())
    expected_sources = {entry["path"] for entry in pin["files"]}
    actual_sources = {
        path.relative_to(VENDOR).as_posix()
        for namespace in ("OAI", "RellichKondrachov", "PrimeNumberTheoremAnd")
        for path in (VENDOR / namespace).rglob("*.lean")
    }
    if actual_sources != expected_sources:
        raise RuntimeError(
            "Vendored proof source set differs from its pin: "
            f"missing={sorted(expected_sources - actual_sources)}, "
            f"extra={sorted(actual_sources - expected_sources)}")
    for entry in pin["files"]:
        path = (VENDOR / entry["path"]).resolve()
        if not path.is_relative_to(VENDOR):
            raise RuntimeError(f"Source path escapes vendor directory: {entry['path']}")
        if hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
            raise RuntimeError(f"Pinned external proof source changed: {entry['path']}")
    for entry in pin["upstreamCompatibilityPatches"]:
        if hashlib.sha256((VENDOR / entry["path"]).read_bytes()).hexdigest() != entry["sha256"]:
            raise RuntimeError(f"Official compatibility patch changed: {entry['path']}")
    for entry in pin["licenses"]:
        if hashlib.sha256((VENDOR / entry["path"]).read_bytes()).hexdigest() != entry["sha256"]:
            raise RuntimeError(f"Pinned license changed: {entry['path']}")
    if (ROOT / "lean-toolchain").read_text().strip() != pin["toolchain"]:
        raise RuntimeError("Project and external baseline toolchains differ.")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(package for package in manifest["packages"]
                   if package["name"] == "mathlib")
    if mathlib["rev"] != pin["mathlibCommit"]:
        raise RuntimeError("Project Mathlib differs from the checked external baseline.")
    for package in manifest["packages"]:
        if package["type"] != "git":
            continue
        directory = ROOT / ".lake/packages" / package["name"]
        revision = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
        if revision != package["rev"]:
            raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
        subprocess.run(["git", "diff", "--quiet", "HEAD", "--"],
                       cwd=directory, check=True)
    print(f"Verified {len(pin['files'])} pinned external proof sources at {pin['commit']}.")


if __name__ == "__main__":
    main()
