#!/usr/bin/env python3
"""Verify archived evidence, or restore it beneath a separate directory."""
from pathlib import Path, PurePosixPath
import argparse
import fnmatch
import gzip
import hashlib
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--destination', type=Path)
    parser.add_argument('--select', default='*', help='Glob of original paths')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    index = json.loads((root / 'index.json').read_text())
    entries = [item for item in index['entries']
               if fnmatch.fnmatchcase(item['original_path'], args.select)]
    if not entries:
        parser.error('No archived files match the selection.')
    verified = {}
    for item in entries:
        archive = PurePosixPath(item['archive_path'])
        assert not archive.is_absolute() and '..' not in archive.parts
        digest = item['sha256']
        if digest not in verified:
            data = gzip.decompress((root / archive).read_bytes())
            assert hashlib.sha256(data).hexdigest() == digest, archive
            verified[digest] = data
        data = verified[digest]
        assert len(data) == item['bytes'], item['original_path']
        if args.destination is not None:
            original = PurePosixPath(item['original_path'])
            assert original.is_absolute() and '..' not in original.parts
            target = args.destination / Path(*original.parts[1:])
            if target.exists():
                assert target.is_file() and target.read_bytes() == data, target
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
    mirrors = 0
    for item in index['readable_latest_semiprime']:
        if not fnmatch.fnmatchcase(item['original_path'], args.select):
            continue
        relative = PurePosixPath(item['readable_path'])
        assert not relative.is_absolute() and '..' not in relative.parts
        assert hashlib.sha256((root / relative).read_bytes()).hexdigest() == item['sha256']
        mirrors += 1
    print(json.dumps({'files_verified': len(entries), 'objects_verified': len(verified),
                      'readable_copies_verified': mirrors,
                      'restored': args.destination is not None}))


if __name__ == '__main__':
    main()
