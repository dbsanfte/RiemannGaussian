#!/usr/bin/env python3
"""Read-only verification; writes only this packet's validation.json."""
from pathlib import Path
import argparse, hashlib, json
from datetime import datetime, timezone
HERE = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
readj = lambda p: json.loads(p.read_text())
p = argparse.ArgumentParser()
p.add_argument('--repo-root', type=Path)
p.add_argument('--check-originals', action='store_true')
a = p.parse_args()
manifest = readj(HERE / 'manifest.json')
listed = {e['path'] for e in manifest['entries']}
actual = {str(x.relative_to(HERE)) for x in HERE.rglob('*') if x.is_file()}
assert actual - {'manifest.json', 'validation.json'} == listed, 'archive file-set mismatch'
for e in manifest['entries']:
    data = (HERE / e['path']).read_bytes()
    assert len(data) == e['bytes'] and sha(data) == e['sha256'], e['path']
records = readj(HERE / 'provenance/source-provenance.json')['sources']
lookup = {r['original_path']: r for r in records}
pins = readj(HERE / 'provenance/inherited-376-pins.json')
assert len(pins) == 376
for name, expected in pins.items():
    r = lookup[name]
    assert r['sha256'] == expected == r['inherited_pin_sha256'], name
copied = [r for r in records if r['status'] == 'copied_verbatim']
for r in copied:
    data = (HERE / r['archive_path']).read_bytes()
    assert len(data) == r['bytes'] and sha(data) == r['sha256'], r['archive_path']
    assert Path(r['archive_path']).suffix in {'.md','.json','.py','.sh','.csv','.tsv','.yaml','.yml','.txt'}
    assert not any(x in {'sources','literature-sources','fresh-sources','source-cache'} for x in Path(r['archive_path']).parts)
original_count = 0
if a.check_originals:
    for r in records:
        data = Path(r['original_path']).read_bytes()
        assert len(data) == r['bytes'] and sha(data) == r['sha256'], r['original_path']
        original_count += 1
root = a.repo_root
if root is None and (HERE.parents[2] / 'AGENTS.md').is_file():
    root = HERE.parents[2]
frozen_count = 0
frozen_packets = []
if root is not None:
    baseline = readj(HERE / 'provenance/frozen-baseline.json')
    for spec in baseline['frozen_packets']:
        path = root / spec['path']
        raw = path.read_bytes()
        assert sha(raw) == spec['sha256'], str(path)
        doc = json.loads(raw)
        entries = doc.get('entries', doc.get('files'))
        assert len(entries) == spec['entries'], str(path)
        for e in entries:
            data = (path.parent / e['path']).read_bytes()
            assert len(data) == e['bytes'] and sha(data) == e['sha256'], str(path.parent / e['path'])
        frozen_count += len(entries)
        frozen_packets.append({'path': spec['path'], 'entries': len(entries), 'verified': True})
    assert len(frozen_packets) == 15 and frozen_count == 270
result = {
    'validated_at': datetime.now(timezone.utc).isoformat(),
    'manifest_sha256': sha((HERE / 'manifest.json').read_bytes()),
    'packet_entries_verified': len(listed),
    'verbatim_copies_verified': len(copied),
    'inherited_pins_verified': len(pins),
    'original_sources_verified': original_count,
    'frozen_packets': frozen_packets,
    'frozen_entries_verified': frozen_count,
    'standalone_mode': root is None,
    'full_external_papers_copied': False,
    'historical_mutating_validators_executed': False,
    'math_experiments_or_lean_builds_run': False,
    'status': 'PASS',
    'scope': 'Byte/provenance preservation and correction packaging only; current complete scalar bound soft k^(5/4), sixth-exponent objective open; external Hecke consequences conditional.'
}
(HERE / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ['status','packet_entries_verified','verbatim_copies_verified','inherited_pins_verified','original_sources_verified','frozen_entries_verified']}, indent=2))
