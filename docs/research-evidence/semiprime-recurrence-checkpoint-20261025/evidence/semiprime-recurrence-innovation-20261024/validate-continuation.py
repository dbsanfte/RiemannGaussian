from pathlib import Path
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path('/home/dbsanfte/riemann/formal')
HERE = Path('/tmp/semiprime-recurrence-innovation-20261024')
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
    'review.md': ['covering-lift-selector.md', 'shared-affine-factorial.md', 'stabilized-aggregate-attempt.md'],
    'adjoint-review.md': ['adjoint-attempt.md'],
    'review-innovation.md': ['literature.md', 'adaptive-precision-followup.md'],
    'root-review.md': ['euclidean-carry-attempt.md', 'endpoint-qdifference-extension.md', 'floor-product-literature.md'],
}
for name, sources in reviews.items():
    review = (HERE / name).read_text()
    assert any(word in review.lower() for word in ('pass', 'accepted')), name
    for source in sources:
        assert report_pins[source] in review, (name, source)

source_pins = {
    '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md': '4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46',
    '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-block-query-20261016/reports/block-transform.md': '825aaaa7d10637eddcf38a7b8e8f2241a70984c4b94c506372e922b845b2fe70',
    '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-block-query-20261016/reports/fast-mixed-matrix-interface.md': '4959b0f33989570507b15eb82e8b93c2020449032ad1612b4d4e92b74f1d5767',
    '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-extraction-query-20261016/reports/coefficient-block-inverse.md': '73685f5580b92375b7d3a9f09265c245125ebee6edf048243a4558b6d5f4e3a2',
    '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-extraction-query-20261016/reports/qshift-power-defect.md': '5e88b2b6b26310e535d959b6a4c3320adb25993c5e878fff8577708076007e5a',
}
source_pins.update({
    '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-adaptive-euclid-20261016/reports/full-ray-tag-trimming.md': '52684f92a92b2b037d687d99708ff3a3473c5b22502990686d308a9fdc902b23',
    '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/unbalanced-extractor.md': 'a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be',
})
source_pins.update({
    '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-colour-retention-20261022/reports/native-quadratic-colour.md': '0ef87fb77032d920019a53efcfe82cf6859bb06250fe473771f44e3f8d4ee363',
    '/tmp/semiprime-native-arithmetic-20261023/native-selector.md': 'e810fce0eb51ed5d4d30ead45e9d232cb467a19851a0c3bba8fbae93f7438249',
})
source_pins.update({
    '/tmp/semiprime-charlier-coverage-20261023/parameter-charlier.md': '5f59aa34e578123ce8acaadbcfbfbe0a3d4ea78baf188aeb9a0cc124541e25b7',
    '/tmp/semiprime-factor-aware-recurrence-20261023/native-witness-initialization.md': 'dc566383085d01367fac68509233fd8cfae01486c0c4ff3044d9c51a98f63cb7',
    '/tmp/semiprime-factor-aware-recurrence-20261023/factor-aware-constructor.md': 'cb9be2321790accc7a240198e362c7ad649ab4abfd1e714fca2eb926ab413624',
})
source_pins.update({
    '/tmp/semiprime-residue-construction-20261023/direct-residue-constructor.md': 'fef14acf2ece2918de5561dd1d37a9c39982ecb97ae658b8d1149210841e42b3',
    '/tmp/semiprime-residue-construction-20261023/complementary-linear-channel.md': 'c623ae1dfc05000ab46fea3f48247764160e579d35e17407b9edd592316a6ec9',
})
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
    'classification': 'Scoped constructive research evidence; no whole-query exponent gain. Public interval contraction and Euclidean carry norms are initialized, but covering selection and cross-row product sharing remain unpaid at soft m. Scalar jets do not initialize the endpoint; native logarithmic derivative has at least h poles. Canonical query remains soft m^1.5, goal active, full bit and Lean composition unfinished.',
    'broad_builds_or_example_campaigns': False,
}
(HERE / 'continuation-validation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ('validated_at', 'head', 'shared_documents',
                                      'frozen_entry_count', 'diff_check', 'classification')}, indent=2))
