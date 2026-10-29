#!/usr/bin/env python3
"""Read-only packet/source validation. This is not a Lean proof check."""
from pathlib import Path
import datetime
import hashlib
import json
import re

packet = Path(__file__).resolve().parent
root = packet.parents[2]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
inventory = json.loads((packet / 'inventory.json').read_text())
progress = json.loads((packet / 'progress.json').read_text())
modules = inventory['modules']
assert len(modules) == len({row['module'] for row in modules})
actual = {str(p.relative_to(root)) for p in (root / 'RiemannGaussian').glob('Semiprime*.lean')}
assert actual == {row['path'] for row in modules}
by_name = {row['module']: row for row in modules}
for row in modules:
    path = root / row['path']
    assert row['module'] == 'RiemannGaussian.' + path.stem
    assert sha(path) == row['sha256'], ('current source hash', row['path'])
for row in inventory['evidence']:
    path = root / row['path']
    assert sha(path) == row['sha256'], ('copied evidence hash', row['path'])
    assert path.stat().st_size == row['bytes']
for row in inventory['archived_sources']:
    assert row['path'] not in actual
    assert sha(root / row['path']) == row['sha256']
# Preserve the published historical groups/records and exact supplied scratch pins.
base = json.loads((root / 'docs/research-evidence/semiprime-publication-20261029/inventory.json').read_text())
for key in ('groups', 'archived_sources', 'supplementary_historical_records', 'missing_or_intentionally_uncopied_records'):
    assert inventory[key] == base[key], ('preserved historical section', key)
assert inventory['evidence'][:len(base['evidence'])] == base['evidence']
for old in base['modules']:
    assert by_name[old['module']]['sha256'] == old['sha256'], ('preserved old source pin', old['module'])
for row in modules:
    assert row['validation']['fresh_lean_build'] is False
assert inventory['summary']['current_semiprime_sources'] == len(modules)
assert inventory['summary']['current_source_bytes'] == sum(row['bytes'] for row in modules)
assert inventory['summary']['current_source_lines'] == sum(row['lines'] for row in modules)
assert sum(inventory['summary']['module_status_counts'].values()) == len(modules)
assert inventory['summary'] == progress['summary']
source_note = json.loads((packet / 'source-note-manifest.json').read_text())
for row in source_note['files']:
    assert sha(packet / row['path']) == row['sha256'], ('original supplied scratch pin', row['path'])
    assert (packet / row['path']).stat().st_size == row['bytes']
assert len(inventory['groups']) == 82
assert inventory['research_goal']['status'] == progress['research_goal']['status'] == 'paused'
assert not inventory['research_goal']['full_goal_complete']
assert progress['curated_stage_order_not_lean_dependencies'] is True
assert len(progress['stages']) == len({row['id'] for row in progress['stages']})
for stage in progress['stages']:
    for anchor in stage['proof_anchors']:
        assert anchor['module'] in by_name, ('stage module', stage['id'], anchor)
        if anchor.get('declaration'):
            name = anchor['declaration'].rsplit('.', 1)[-1]
            source = (root / by_name[anchor['module']]['path']).read_text()
            assert re.search(r'(?m)^\s*(?:private\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|opaque)\s+' + re.escape(name) + r'\b', source), ('declaration token', anchor)
result = {'status': 'SOURCE_AND_EVIDENCE_HASHES_PASS_NOT_A_LEAN_BUILD',
          'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'current_sources': len(modules), 'evidence_files': len(inventory['evidence']),
          'archived_sources': len(inventory['archived_sources']),
          'historical_final_groups': len(inventory['groups']),
          'inventory_sha256': sha(packet / 'inventory.json'),
          'progress_sha256': sha(packet / 'progress.json'),
          'fresh_Lean_or_Lake_build_performed': False,
          'research_goal_resumed': False,
          'publication_build_is_separate_parent_evidence': True}
(packet / 'inventory-hash-check.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, sort_keys=True))
