"""Freeze the checked executable-counter slice without changing prior evidence."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import time

ROOT = Path('/home/dbsanfte/riemann/formal')
WORK = Path('/tmp/semiprime-executable-counter-20261027')
PACKET = ROOT / 'docs/research-evidence/semiprime-executable-counter-20261027'
BASE = json.loads((WORK / 'preservation-before.json').read_text())
NAMES = json.loads((WORK / 'new-modules.json').read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def preservation():
    for kind in ('protected', 'concurrent'):
        for rel, digest in BASE[kind].items():
            assert sha(ROOT / rel) == digest, (kind, rel)
    for rel, item in BASE['prefixes'].items():
        prefix = (ROOT / rel).read_bytes()[:item['bytes']]
        assert hashlib.sha256(prefix).hexdigest() == item['sha256'], rel

def local_links(path):
    text = re.sub(r'```.*?```', '', path.read_text(), flags=re.S)
    text = re.sub(r'`[^`]*`', '', text)
    return re.findall(r'\]\(([^)]+)\)', text)

def write_json(name, value):
    (PACKET / name).write_text(json.dumps(value, indent=2) + '\n')

def main():
    preservation()
    assert not PACKET.exists(), 'Packet exists; inspect partial state before retrying'
    checks = json.loads((WORK / 'strict-recheck.json').read_text())
    assert set(checks) == set(NAMES)
    audit = (WORK / 'combined-audit.log').read_text()
    assert 'error:' not in audit and 'sorryAx' not in audit
    rows = re.findall(r'AUDIT RiemannGaussian\.(\w+): declarations=(\d+), theorems=(\d+), standard_axioms_only=true', audit)
    assert {row[0] for row in rows} == set(NAMES)
    assert audit.count('-- All linting checks passed!') == len(NAMES)
    modules = {}
    for name, declarations, theorems in rows:
        src = ROOT / 'RiemannGaussian' / (name + '.lean')
        obj = ROOT / '.lake/build/lib/lean/RiemannGaussian' / (name + '.olean')
        item = checks[name]
        assert item['exit_code'] == 0
        assert sha(src) == item['source_sha256']
        assert sha(WORK / (name + '-strict.log')) == item['log_sha256']
        assert sha(WORK / 'strict-objects' / (name + '.olean')) == item['olean_sha256']
        assert sha(obj) == item['olean_sha256'], name + ' root object mismatch'
        modules[name] = dict(source=str(src.relative_to(ROOT)), source_sha256=sha(src),
                            olean_sha256=sha(obj), declarations=int(declarations),
                            theorems=int(theorems), strict_build='PASS', root15_lint='PASS',
                            all_generated_transitive_axioms='standard_only')
    for name in ('review-public-height-sources.json', 'review-jet-array-sources.json', 'source-hashes.json'):
        for path, digest in json.loads((WORK / name).read_text()).items():
            assert sha(Path(path)) == digest, (name, path)
    for name, item in json.loads((WORK / 'review-source-python-hashes.json').read_text()).items():
        assert sha(WORK / name) == item['sha256']
    for name, digest in json.loads((WORK / 'review-public-schedule-enumeration-hashes.json').read_text()).items():
        assert sha(ROOT / 'RiemannGaussian' / (name + '.lean')) == digest
    item = json.loads((WORK / 'review-cardinal-height-source.json').read_text())
    assert sha(Path(item['source'])) == item['sha256']
    for item in json.loads((WORK / 'frozen-dependencies.json').read_text()).values():
        assert sha(Path(item['path'])) == item['sha256']
    for name, count in (('source-tests', 10), ('factor-search-tests', 4)):
        authored = json.loads((WORK / (name + '.json')).read_text())
        independent = json.loads((WORK / (name + '-independent.json')).read_text())
        assert authored == independent and authored['status'] == 'PASS'
        assert len(authored['tests']) == count
    assert subprocess.run(['git', 'diff', '--check'], cwd=ROOT, capture_output=True).returncode == 0
    selected = set()
    for p in WORK.iterdir():
        if not p.is_file():
            continue
        if p.suffix in ('.md', '.json', '.log') and p.name != 'preservation-after.json':
            selected.add(p.name)
        if p.suffix == '.py' or p.name == 'LICENSE.OpenAI-Math':
            selected.add(p.name)
        if p.suffix == '.lean' and (p.name.startswith('Check') or p.name.endswith('-root-audit.lean')
                                   or p.name == 'CombinedExecutableAudit.lean'):
            selected.add(p.name)
    PACKET.mkdir()
    provenance = {}
    def copy(source, target):
        shutil.copyfile(source, PACKET / target)
        provenance[target] = dict(source=str(source), sha256=sha(source))
    for name in sorted(selected):
        copy(WORK / name, name)
    for name in NAMES:
        copy(ROOT / 'RiemannGaussian' / (name + '.lean'), name + '.lean')
    write_json('archive-provenance.json', provenance)
    links = 0
    for md in PACKET.glob('*.md'):
        for target in local_links(md):
            if target.startswith(('http://', 'https://', '#')):
                continue
            assert (md.parent / target.split('#')[0]).exists(), (md.name, target)
            links += 1
    note = '''

## Public factor count and cached counter execution, 2026-10-27

Packet: docs/research-evidence/semiprime-executable-counter-20261027.
Goal ACTIVE; current slice PROGRESS. Guaranteed factoring bit-time still OPEN.

Thirteen NEW modules close actual ordered graph local-table semantics, full
converse and unique extension, public digit/target coverage and ordinary ordered
nontrivial factor count, public E=Theta(L)/w=O(L^.75), scheduled actual rank and
summary budget, exact eventual executable guards, cached jet arrays, streamed
support enumeration and native row/Taylor/cardinal input heights. Public factor
count has NO supplied graph/count/coverage premise; squares/orientations included.
N>0 endpoint counts integer factor pairs, not just prime pairs. Boolean edge E
is distinct from macro FFT word dimension. E<=6400L; w<=512L^.75; occurrence2.

Actual ternary stream equals subset-pair sum, callback count sum_j<=q 2^j choose(E,j),
nodes<=(E+1)Cq, depth E; inclusive entropy and actual width J=q+1. Cached array
quotient is correct and has <=3J^2+J+1 rational operations. Actual inverse outputs,
ALL inverse dot-prefix sums and quotient outputs have derived fraction bounds.
Native rows share delta=2^(R-1)*(Q!)^(Q+1), with constructor-derived bounded
integer numerators/degree, no universal-dimension height factor. Integer Taylor
shifts preserve delta; actual normalized cardinal input shares (Q!)^(QJ), has
coefficient abs<=2^(QJ), constant1, explicit polynomial logarithmic bounds.

NEW source_layout.py implements pinned complete buckets/cleared defect/owner
pullback and selects ACTUAL integer measurement rows. New factor entry reuses
one constructed layout across <=L+1 original-scope prefix counts. Invalid guard
uses labelled trial division; optional cap returns no result. Frozen code intact.
Ten structural/algebra and four adapter checks independently replayed PASS;
small/guard-disabled/synthetic fixtures explicitly diagnostic, not rate evidence.

Concrete rational-operation ledger covers support pairs/summary boxes/head scans/
2^w local expansions/setup/Hermite/prefixes: poly(E)*2^(O(E*(loglogE)^2/sqrtlogE)+w),
hence 2^o(L) with actual public sizes. Ledger is not the complete executed
primitive-bit/space theorem. ALL intermediate corrected-input/global/product/
convolution/Hermite accumulator heights and explicit finite-choice/word-reader/
normalizer/row-selection/control/allocation refinements still need attachment.
Then compose guard+finite fallback+factor recovery into all-input bit theorem.
Python is independently implemented; no extraction/compiler-ID correspondence
is claimed. Native original longquery softK^1.25 remains unchanged.

All13 independently strict compiled; ordinary-root15lint and all897 declarations/
694 theorem constants standard-only PASS; root/isolated objects match final
dependencies. Independent semantic reviews PASS. Prior1553 protected files,
24 concurrent files and2 append-only prefixes preserved. External published
fixed-k SAT endpoint remains previously verified; no repeat/wider build.
No commit/push. Next: complete height/execution composition, not another
representation search or finite factoring campaign.
'''
    for rel in BASE['prefixes']:
        with (ROOT / rel).open('a') as output:
            output.write(note)
    preservation()
    totals = dict(modules=len(modules), declarations=sum(x['declarations'] for x in modules.values()),
                  theorem_constants=sum(x['theorems'] for x in modules.values()))
    assert totals == dict(modules=13, declarations=897, theorem_constants=694)
    write_json('verification.json', dict(status='PASS', timestamp_utc=time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime()),
        goal_status='active', slice_status='PROGRESS', totals=totals, modules=modules,
        strict_flags=['autoImplicit=false', 'warningAsError=true'], all_generated_declarations=True,
        allowed_transitive_axioms=['propext', 'Classical.choice', 'Quot.sound'],
        independent_python_replays={'constructor_tests':10, 'adapter_tests':4, 'identical_results':True},
        preserved={kind:len(value) for kind,value in BASE.items()}, local_markdown_links=links,
        primitive_factoring_bit_time_proved=False, native_softK_acquisition_proved=False,
        commit_or_push=False))
    files = {str(p.relative_to(PACKET)): dict(bytes=p.stat().st_size, sha256=sha(p))
             for p in sorted(PACKET.rglob('*')) if p.is_file() and p.name != 'manifest.json'}
    write_json('manifest.json', dict(status='PASS', files=files))
    for name, item in files.items():
        assert sha(PACKET / name) == item['sha256']
    preservation()
    print(json.dumps(dict(packet=str(PACKET), status='PASS', files=len(files)+1, totals=totals)))

if __name__ == '__main__':
    main()
