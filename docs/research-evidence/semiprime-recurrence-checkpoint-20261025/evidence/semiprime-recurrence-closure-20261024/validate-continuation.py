from pathlib import Path
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path('/home/dbsanfte/riemann/formal')
HERE = Path('/tmp/semiprime-recurrence-closure-20261024')
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

reviews = {'integration-review.md': ['journal-append.md', 'agents-append.md'], 'frobenius-pairing-review.md': ['frobenius-pairing.md'], 'shared-recurrence-review.md': ['shared-recurrence.md'], 'scalar-closure-review.md': ['scalar-closure.md'], 'trace-closure-review.md': ['trace-closure.md']}

for name, sources in reviews.items():
    review = (HERE / name).read_text()
    assert any(word in review.lower() for word in ('pass', 'accepted', 'check')), name
    for source in sources:
        assert report_pins[source] in review, (name, source)

source_pins = {'/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md': '4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46', '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/unbalanced-extractor.md': 'a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be', '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-query-continuation-20261022/reports/rough-order-cleaning.md': '2c04b959d680ae3e04eed20c71e6ea3faf2b253b5d2c6b1aa940a28aac8142f9', '/tmp/semiprime-native-character-20261024/sources/nguyen-schmidt-2009.pdf': 'b08f0bdc0a9177c38985654db3dafd6768dc1937928f2812769e7f38103b6e09', '/tmp/semiprime-native-character-20261024/sources/lenstra-silverberg-CMorders.pdf': '3ad0d7592e70aeb079c93324c6c20f2343de7a0f82547d2081a874e2fda97dcd', '/tmp/semiprime-native-character-20261024/composite-row-contract.md': '66795af6eae4e0cde23b6e84a6beb7ae18a656e41bdf9f94d739c83f3cbccb74', '/tmp/semiprime-native-character-20261024/character-acquisition.md': '83bd40ae27d975320566827bba50ae73d63464218d2993bfc5b226e60e7749a7', '/tmp/semiprime-native-character-20261024/character-literature.md': '24ec2dd1529a9c36070df12e880347c21c8841e7367eaa711c0bd7cfcf601c02', '/tmp/semiprime-recurrence-closure-20261024/sources/lau-wu-2007.pdf': '4cc9dba73064795de434d6b42baca0743347313b6a242f5439c9ed979ddd4368', '/tmp/semiprime-recurrence-closure-20261024/sources/monagan-resultant.pdf': '94498929a8fdb2dd76fdee3de43b1be19f5c010e2fc39f83ad24cf7a1c39f60c'}
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
    'classification': 'Uniform aligned quadratic character family acquired soft k with automatic saturated original-leaf recovery and no torus-survival premise. All actual scalar leaf sequences have a common acquired order-four recurrence; its executed family expansion costs soft J^2 and does not compute the terminal product. Dickson trace and transported scalar norm attempts retain the existing soft(J+sqrt(JL)) full-query bound. One-sixth acquisition and full bit/Lean proof remain open.',
    'broad_builds_or_example_campaigns': False,
}
(HERE / 'continuation-validation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ('validated_at', 'head', 'shared_documents',
                                      'frozen_entry_count', 'diff_check', 'classification')}, indent=2))
