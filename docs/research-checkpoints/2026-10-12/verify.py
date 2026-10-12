#!/usr/bin/env python3
"""Verify the portable evidence snapshot; restoration is opt-in."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import tarfile


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--restore-to", type=Path, help="Extract research files to this directory, preserving archive paths.")
    parser.add_argument("--overwrite", action="store_true", help="Explicitly allow replacement of mismatched destination files.")
    args = parser.parse_args()
    if args.overwrite and args.restore_to is None:
        parser.error("--overwrite requires --restore-to")
    base = Path(__file__).resolve().parent
    manifest = json.loads((base / "manifest.json").read_text())
    archive = base / manifest["archive"]
    if digest(archive.read_bytes()) != manifest["archiveSha256"]:
        raise SystemExit("Archive SHA256 mismatch")
    expected = {record["member"]: record for record in manifest["files"]}
    if len(expected) != manifest["fileCount"]:
        raise SystemExit("Duplicate or inconsistent manifest members")
    seen = set()
    verified = []
    with tarfile.open(archive, "r:gz") as tf:
        for member in tf:
            pure = PurePosixPath(member.name)
            if pure.is_absolute() or ".." in pure.parts or not member.isfile() or member.name in seen:
                raise SystemExit(f"Unsafe or duplicate archive member: {member.name}")
            if member.name not in expected:
                raise SystemExit(f"Unexpected archive member: {member.name}")
            stream = tf.extractfile(member)
            if stream is None:
                raise SystemExit(f"Unreadable archive member: {member.name}")
            data = stream.read()
            record = expected[member.name]
            if len(data) != record["bytes"] or digest(data) != record["sha256"]:
                raise SystemExit(f"Member SHA256 or size mismatch: {member.name}")
            seen.add(member.name)
            if args.restore_to is not None:
                target = args.restore_to / member.name
                resolved_root = args.restore_to.resolve()
                if not target.resolve().is_relative_to(resolved_root):
                    raise SystemExit(f"Destination escapes through a symlink: {target}")
                if target.exists() and (not target.is_file() or digest(target.read_bytes()) != record["sha256"]) and not args.overwrite:
                    raise SystemExit(f"Refusing to overwrite mismatched destination: {target}")
                verified.append((target, data))
    if seen != set(expected):
        raise SystemExit("Archive is missing manifest members")
    # Validate every member and every destination before any write.
    for target, data in verified:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    print(f"Verified {len(seen)} files, {manifest['uncompressedBytes']} uncompressed bytes; archive SHA256 {manifest['archiveSha256']}.")
    if args.restore_to is not None:
        print(f"Restored research evidence to {args.restore_to}; external /tmp files are under tmp/, and the external roadmap is under workspace/.")


if __name__ == "__main__":
    main()
