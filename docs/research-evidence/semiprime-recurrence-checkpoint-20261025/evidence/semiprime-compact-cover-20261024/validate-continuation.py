from pathlib import Path
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path('/home/dbsanfte/riemann/formal')
HERE = Path('/tmp/semiprime-compact-cover-20261024')
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
    'cover-review.md': ['cover-literature.md'],
    'native-cover-review.md': ['native-cover-combination.md'],
    'smooth-rough-review.md': ['smooth-rough-cover.md'],
    'quadratic-counterexample-review.md': ['quadratic-counterexample.md', 'tinyreplay.py', 'cover-literature.md'],
}
for name, sources in reviews.items():
    review = (HERE / name).read_text()
    assert any(word in review.lower() for word in ('pass', 'accepted', 'check')), name
    for source in sources:
        assert report_pins[source] in review, (name, source)

source_pins = {'/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md': '4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46', '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/unbalanced-extractor.md': 'a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be', '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-acquisition-checkpoint-20261016/reports/group-gap-criterion.md': '6fb196a7d87a81a53e1169810044fa5a946f85f683f79b25f2498e648929a5c9', '/tmp/semiprime-character-endpoint-20261024/native-pivot-contraction.md': '9e363fee81473624d32088c4cba883d60fb3f9194d93f5ba30368c8881318c9a', '/tmp/semiprime-compact-cover-20261024/sources/umans-wang-2025.pdf': '70160d59ac73d443f0c9dbd04246e1c35f824f7a6a40e602cd6fb5125cfa0be5', '/tmp/semiprime-compact-cover-20261024/sources/20-years-ecm.pdf': '79618c17b20775cedeeec0864570ca53060c1f831a29ec2a99253121fba3c2d5'}
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
    'classification': 'Square-LCM projection gives an exact smaller-prime rough-part certificate at unchanged soft-m preprocessing cost. Explicit quadratic recurrence is acquired in soft m but universal coverage is refuted by one exact prepared semiprime counterexample. Native inverse fusion reduces to weighted Fermat rays. Guaranteed query stays soft m^1.5; sixth-rate and full bit/Lean proof open.',
    'broad_builds_or_example_campaigns': False,
}
(HERE / 'continuation-validation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ('validated_at', 'head', 'shared_documents',
                                      'frozen_entry_count', 'diff_check', 'classification')}, indent=2))
