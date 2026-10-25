from pathlib import Path
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path('/home/dbsanfte/riemann/formal')
HERE = Path('/tmp/semiprime-quadratic-ideal-20261024')
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

reviews = {'integration-review.md': ['journal-append.md', 'agents-append.md'], 'point-ideal-review.md': ['point-ideal.md'], 'ideal-literature-review.md': ['ideal-literature.md'], 'ideal-seed-query-review.md': ['ideal-seed-query.md'], 'torus-order-supplier-review.md': ['torus-order-supplier.md']}

for name, sources in reviews.items():
    review = (HERE / name).read_text()
    assert any(word in review.lower() for word in ('pass', 'accepted', 'check')), name
    for source in sources:
        assert report_pins[source] in review, (name, source)

source_pins = {'/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md': '4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46', '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/unbalanced-extractor.md': 'a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be', '/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-query-continuation-20261022/reports/rough-order-cleaning.md': '2c04b959d680ae3e04eed20c71e6ea3faf2b253b5d2c6b1aa940a28aac8142f9', '/tmp/semiprime-native-character-20261024/sources/nguyen-schmidt-2009.pdf': 'b08f0bdc0a9177c38985654db3dafd6768dc1937928f2812769e7f38103b6e09', '/tmp/semiprime-native-character-20261024/sources/lenstra-silverberg-CMorders.pdf': '3ad0d7592e70aeb079c93324c6c20f2343de7a0f82547d2081a874e2fda97dcd', '/tmp/semiprime-native-character-20261024/composite-row-contract.md': '66795af6eae4e0cde23b6e84a6beb7ae18a656e41bdf9f94d739c83f3cbccb74', '/tmp/semiprime-native-character-20261024/character-acquisition.md': '83bd40ae27d975320566827bba50ae73d63464218d2993bfc5b226e60e7749a7', '/tmp/semiprime-native-character-20261024/character-literature.md': '24ec2dd1529a9c36070df12e880347c21c8841e7367eaa711c0bd7cfcf601c02', '/tmp/semiprime-recurrence-closure-20261024/sources/lau-wu-2007.pdf': '4cc9dba73064795de434d6b42baca0743347313b6a242f5439c9ed979ddd4368', '/tmp/semiprime-recurrence-closure-20261024/sources/monagan-resultant.pdf': '94498929a8fdb2dd76fdee3de43b1be19f5c010e2fc39f83ad24cf7a1c39f60c', '/tmp/semiprime-recurrence-closure-20261024/frobenius-pairing.md': '215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363', '/tmp/semiprime-recurrence-closure-20261024/shared-recurrence.md': '654218a0e5dde8e0261ea662cf40c8ceb82e5e152cebebb4542b831f0b322562', '/tmp/semiprime-quadratic-product-20261024/sources/amortized.pdf': 'f025997d312ef3037a74d4c3a88854ed3a7bfc10e3a8cb4e2fe780920ecb1f55', '/tmp/semiprime-quadratic-product-20261024/sources/harvey-sutherland.pdf': '5e8ce8d0207260506e057cb4a0d970bbdfe9c6bd897366089cf4648898c2b770', '/tmp/semiprime-quadratic-product-20261024/sources/special-points.pdf': '257beedc4a433fe5ebf5a8abc8db98e057e708c3e862140af6ea90d1874a9aa9', '/tmp/semiprime-quadratic-product-20261024/sources/nusken-ziegler.pdf': 'e27343f0c1d81d05099a46ef61cb6cf1e6a7f3387dd162c04ee54d272445e94a', '/tmp/semiprime-quadratic-product-20261024/sources/hone-sigma.pdf': '6a54921c4c5c8c6beaa029f0800dad666631559954a3c02e73b6c6a26671bba6', '/tmp/semiprime-quadratic-product-20261024/sources/stange-elliptic-nets.pdf': '877952cdb045984d9334674c6e2ed36d405887e74aa931f4d77d98a83703ead4', '/tmp/semiprime-quadratic-ideal-20261024/sources/interpolation-bases.pdf': 'ab2a405bb5f7e86b0efd405ad614f04eb7c0a76da08fef48826dbea81b29e546', '/tmp/semiprime-quadratic-ideal-20261024/sources/generic-ideals.pdf': 'c5d41a8624d882c4180ccd757219035b67216e3d849d8c02269bf9cbc99c1b89', '/tmp/semiprime-quadratic-ideal-20261024/sources/newton2024.pdf': 'f34f1374716e29a8ce8cda4f33306b80f3bc7850c582efdca62d407983184907', '/tmp/semiprime-quadratic-ideal-20261024/sources/madic2025.pdf': 'a6daf5998c6d9bc2012e53a4145513eef033026c49d0c9e30dafa42574f7486a', '/tmp/semiprime-quadratic-product-20261024/shared-evaluation.md': 'd3df0e461a41583dfa60d4272d44174abd4ca3b05a0c730d31ede0dc06903f4b', '/tmp/semiprime-quadratic-product-20261024/colour-fusion-review.md': '0994d290fa53b33505cd70ddef8a6196c95823c573bb4c565f687545f68c4925', '/tmp/semiprime-quadratic-product-20261024/journal-append.md': '94567a8430f1863bcedc52a47874384d513073c43f8c342071a3873ee0070f2a', '/tmp/semiprime-quadratic-product-20261024/division-product-review.md': '5c9eb496bd750ecf956fab3580d3c56ab18bcf6f531e9f7059545d323dc02dc0', '/tmp/semiprime-quadratic-product-20261024/integration-review.md': 'f3a18a432b1cf029ae3cf36a934e6aea1d7564f88906c2ec8f99ca606f43d752', '/tmp/semiprime-quadratic-product-20261024/colour-fusion.md': 'c9d51ce76a7b364d217440f1a73ac0f1262e448421c58691dbb42d632240de80', '/tmp/semiprime-quadratic-product-20261024/shared-evaluation-review.md': '587969b458343ade05f61a6ac63602423f4d896435c3759a79c4510af1f5551d', '/tmp/semiprime-quadratic-product-20261024/agents-append.md': '9a5b4ee7cd5c5397b6db2f29eb1f7525c1a63074487118f3ae3befdb379c4306', '/tmp/semiprime-quadratic-product-20261024/division-product.md': '97ac4f4f1ef8ce9a62ff5dcf2847c8182036bb3e5508c80b6883275d2cbd6031'}
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
    'classification': 'Uniform deterministic soft-k factor-or-large-odd-order supplier for the norm-one quadratic torus, including both local H-powered order bounds, with no projection/coprimality oracle. Controlled row modulus and factor-or-unit separation acquire a true bounded-width auxiliary point ideal in soft k. Low-degree recurrence startup is paid conditionally; the whole long query retains soft(J+sqrt(JL)). One-sixth factoring and full bit/Lean composition remain open.',
    'broad_builds_or_example_campaigns': False,
}
(HERE / 'continuation-validation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ('validated_at', 'head', 'shared_documents',
                                      'frozen_entry_count', 'diff_check', 'classification')}, indent=2))
