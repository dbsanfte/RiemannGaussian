from pathlib import Path
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path('/home/dbsanfte/riemann/formal')
HERE = Path('/tmp/semiprime-tensor-norm-20261024')
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
    'sylvester-review.md': ['sylvester-elimination.md'],
    'geometric-review.md': ['geometric-generator.md'],
    'scalar-resultant-review.md': ['scalar-resultant-algorithms.md'],
}
for name, sources in reviews.items():
    review = (HERE / name).read_text()
    assert any(word in review.lower() for word in ('pass', 'accepted', 'check')), name
    for source in sources:
        assert report_pins[source] in review, (name, source)

source_pins = {'/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md': '4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46', '/tmp/semiprime-recurrence-endpoint-20261024/literature-endpoint.md': '762a054cb539cc633f3d8295184a3feb9a8339348bd115396f2e4d340cbad85b', '/tmp/semiprime-recurrence-endpoint-20261024/christoffel-terminal.md': 'c523fc8a1a7a23d667f32714e1671c6eb782b52d423984681402eb8deea01008', '/tmp/semiprime-tensor-norm-20261024/sources/structured.pdf': '9834268a83b91fd33ffa92bfcd3e3aeb3946a573f39051ffce6660a7c6805ef7', '/tmp/semiprime-tensor-norm-20261024/sources/cejsc95.pdf': '9ad39a8b1706be441bcbfd3463a67d762e6cb483d320b9b1bf4b640ff0972dfd'}
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
    'classification': 'Executed compact first Sylvester Schur step and paid all-formal-pivot q-hook normalization in soft m. Endpoint mixed coefficients and scalar norm remain unpaid; transverse geometric carry is not a one-coordinate seam. Adaptive auxiliary-pivot factors have no coverage theorem. Existing complete query remains soft m^1.5; sixth-rate goal active, full bit and Lean composition unfinished.',
    'broad_builds_or_example_campaigns': False,
}
(HERE / 'continuation-validation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ('validated_at', 'head', 'shared_documents',
                                      'frozen_entry_count', 'diff_check', 'classification')}, indent=2))
