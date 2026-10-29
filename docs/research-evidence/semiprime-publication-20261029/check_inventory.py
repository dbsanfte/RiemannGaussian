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
