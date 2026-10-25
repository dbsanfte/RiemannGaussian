from pathlib import Path
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path('/home/dbsanfte/riemann/formal')
HERE = Path('/tmp/semiprime-character-endpoint-20261024')
baseline = json.loads((HERE / 'continuation-baseline.json').read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(*args):
    return subprocess.run(['git', *args], cwd=ROOT, text=True,
                          capture_output=True, check=True).stdout


assert git('rev-parse', 'HEAD').strip() == baseline['head']
drafts = {'AGENTS.md': 'agents-append.md',
          'docs/semiprime-factorisation-investigation.md': 'journal-append.md'}
report_pins = json.loads((HERE / 'final-pins.json').read_text())['reports']
for name, expected in report_pins.items():
    assert sha((HERE / name).read_bytes()) == expected, name

reviews = {
    'integration-review.md': ['journal-append.md', 'agents-append.md'],
    'character-review.md': ['character-resultant.md'],
    'character-independent-review.md': ['character-resultant.md'],
    'native-review.md': ['native-pivot-contraction.md'],
    'half-norm-review.md': ['half-norm-cancellation.md'],
}
for name, sources in reviews.items():
    review = (HERE / name).read_text()
    assert any(word in review.lower() for word in ('pass', 'accepted', 'check')), name
    for source in sources:
        assert report_pins[source] in review, (name, source)

source_pins = {'/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md': '4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46', '/tmp/semiprime-tensor-norm-20261024/sylvester-elimination.md': 'f3375df02a067a43230d1f4accddc476bbbe020a64c9145b90757ba5404720c2', '/tmp/semiprime-gauss-period-20261024/period-query-attempt.md': 'b876429f4ca01b324e5dec74d62a27706664942c023a5eb97487252df6152cb9', '/tmp/semiprime-gauss-period-20261024/period-recovery.md': 'bb8fd816c969e00061192201e88c97d0d8e0ed0993dced370f1e7ea670408e3d', '/tmp/semiprime-native-shared-acquisition-20261023/native-polynomial-structure.md': 'f9af812ff9a027324120aff094408306dd9f47a3b9e32e4169132e60da2cd066', '/tmp/semiprime-original-pattern-20261023/mobius-canonical-carry.md': '505862e94056848ff2f13cd213286a629848a8fe37e19ad9ba984ddace09e67a', '/tmp/semiprime-character-endpoint-20261024/sources/patterson-2007.pdf': '789082e8b99dbf97612bbc2e494ee37f237cc54a2a5ff70b5084e33f7cb04824', '/tmp/semiprime-character-endpoint-20261024/sources/subresultants-CASC2021.pdf': 'd22d1b2b5c33d2c3f14631fd28b50fe57fe88800a71800bc629cf5071e2ebf0a'}
for name, expected in source_pins.items():
    assert sha(Path(name).read_bytes()) == expected, name

packets = []
total = 0
for expected in baseline['frozen_packets']:
    path = ROOT / expected['path']
    raw = path.read_bytes()
    assert sha(raw) == expected['sha256'], str(path)
    manifest = json.loads(raw)
    entries = manifest.get('entries', manifest.get('files'))
    assert len(entries) == expected['entries'], str(path)
    for entry in entries:
        member = path.parent / entry['path']
        content = member.read_bytes()
        assert len(content) == entry['bytes'], str(member)
        assert sha(content) == entry['sha256'], str(member)
    total += len(entries)
    packets.append(dict(expected, all_entries_verified=True))
assert total == baseline['frozen_entry_count'] == 270

append_requested = '--append' in sys.argv
pending = []
for old in baseline['shared_document_baselines']:
    path = ROOT / old['path']
    data = path.read_bytes()
    piece = (HERE / drafts[old['path']]).read_bytes()
    assert sha(data[:old['bytes']]) == old['sha256'], old['path']
    if append_requested:
        assert len(data) == old['bytes'], old['path']
        pending.append((path, piece))
    else:
        assert data[old['bytes']:] == piece, old['path']

for path, piece in pending:
    with path.open('ab') as stream:
        stream.write(piece)

documents = []
for old in baseline['shared_document_baselines']:
    data = (ROOT / old['path']).read_bytes()
    piece = (HERE / drafts[old['path']]).read_bytes()
    assert sha(data[:old['bytes']]) == old['sha256'], old['path']
    assert data[old['bytes']:] == piece, old['path']
    documents.append({
        'path': old['path'], 'bytes': len(data), 'lines': data.count(b'\n'),
        'sha256': sha(data), 'original_prefix_preserved': True,
        'append_heading_line': old['lines'] + 2,
        'append_sha256': sha(piece),
    })

git('diff', '--check')
changed = sorted(git('diff', '--name-only').splitlines())
assert changed == sorted(drafts), changed
reports = []
for path in sorted(HERE.glob('*.md')):
    data = path.read_bytes()
    reports.append({'path': str(path), 'bytes': len(data), 'sha256': sha(data)})
result = {
    'validated_at': datetime.now(timezone.utc).isoformat(),
    'head': baseline['head'], 'shared_documents': documents,
    'frozen_packets': packets, 'frozen_entry_count': total,
    'reports': reports, 'review_pins': 'all matched current source/draft bytes',
    'source_pins': source_pins, 'diff_check': 'passed',
    'tracked_changes': changed,
    'classification': 'First two auxiliary pivot supports, including saturation, completely handled in soft m by at most five original slice checks and unit removals. Native inverse tags retain a proved non-q phase; exact half-norm terminal is unit times original degree-J polynomial. Later mixed support unacquired; complete query remains soft m^1.5, sixth-rate and full bit/Lean proof open.',
    'broad_builds_or_example_campaigns': False,
}
(HERE / 'continuation-validation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ('validated_at', 'head', 'shared_documents',
                                      'frozen_entry_count', 'diff_check', 'classification')}, indent=2))
