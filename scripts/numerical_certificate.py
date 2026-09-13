#!/usr/bin/env python3
"""Enforce the optional certificate boundary and hash its actual local inputs.

This is build bookkeeping, not a mathematical verifier. Lean checks the proofs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
CONFIG = ROOT / "docs/numerical-certificate.json"
IMPORT = re.compile(r"^(?:(?:public|private|meta) )*import ([\w.]+)\s*$", re.M)


def config():
    return json.loads(CONFIG.read_text())


def module_path(name):
    relative = Path(*name.split(".")).with_suffix(".lean")
    for base in (ROOT, ROOT / "vendor/zeta23"):
        if (base / relative).is_file():
            return base / relative
    return None


def closure(root):
    """Traverse local imports, stopping at pinned external packages."""
    result, pending = {}, [root]
    while pending:
        name = pending.pop()
        if name in result:
            continue
        path = module_path(name)
        if path is None:
            if name == "RiemannGaussian" or name.startswith("RiemannGaussian."):
                raise ValueError(f"Missing project module: {name}")
            continue
        result[name] = path
        pending.extend(IMPORT.findall(path.read_text()))
    return result


def partition():
    settings = config()
    normal = closure(settings["defaultTarget"])
    optional = closure(settings["optionalTarget"])
    heavy = {n for n in normal if n.startswith(settings["heavyModulePrefix"])}
    if heavy:
        raise ValueError(f"Default build imports exhaustive certificate data: {sorted(heavy)}")
    sources = {"RiemannGaussian." + ".".join(p.relative_to(ROOT / "RiemannGaussian")
               .with_suffix("").parts) for p in (ROOT / "RiemannGaussian").rglob("*.lean")}
    missing = sources - normal.keys() - optional.keys()
    if missing:
        raise ValueError(f"Unimported source modules: {sorted(missing)}")
    # This project uses a literal, single-line string array for defaultTargets.
    # Reading just that field keeps the build guard dependency-free on Python 3.10.
    defaults = re.search(r"^defaultTargets\s*=\s*(\[[^\n]*\])\s*$",
                         (ROOT / "lakefile.toml").read_text(), re.M)
    if defaults is None or json.loads(defaults[1]) != [settings["defaultTarget"]]:
        raise ValueError("The numerical certificate must not enter defaultTargets")
    return normal, optional


def fingerprint():
    _, optional = partition()
    paths = set(optional.values())
    paths.update(ROOT / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "vendor/zeta23/lakefile.toml", "vendor/zeta23/lake-manifest.json",
        "docs/numerical-certificate.json", "scripts/numerical_certificate.py",
        "scripts/verify_numerical_certificate.py", "scripts/generate_montgomery_taylor_cover.py",
        "RiemannGaussian/CertificateData/MontgomeryTaylorCover/manifest.json",
        "certificates/seven-window/cover-proposal.json.gz",
        "scripts/test_numerical_certificate_build.py",
        "scripts/test_numerical_certificate_scheduler.py", "scripts/test_numerical_certificate_audit.py",
        "scripts/AuditNumericalCertificate.lean", ".github/workflows/numerical_certificate.yml"))
    h = hashlib.sha256()
    for path in sorted(paths):
        h.update(path.relative_to(ROOT).as_posix().encode() + b"\0")
        h.update(path.read_bytes() + b"\0")
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fingerprint", action="store_true")
    args = parser.parse_args()
    normal, optional = partition()
    if args.fingerprint:
        print(fingerprint())
    else:
        print(f"Default build excludes all certificate data; "
              f"{len(optional.keys() - normal.keys())} modules are opt-in only.")


if __name__ == "__main__":
    main()
