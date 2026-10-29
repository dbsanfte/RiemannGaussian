"""Archive the checked bit-counter slice while preserving earlier work."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import time

ROOT = Path('/home/dbsanfte/riemann/formal')
WORK = Path('/tmp/semiprime-bit-counter-20261027')
PACKET = ROOT / 'docs/research-evidence/semiprime-bit-counter-20261027'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def dump(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')

def preserve(base):
    for kind in ('protected', 'concurrent'):
        for rel, digest in base[kind].items():
            assert sha(ROOT / rel) == digest, (kind, rel)
    for rel, item in base['prefixes'].items():
        raw = (ROOT / rel).read_bytes()[:item['bytes']]
        assert hashlib.sha256(raw).hexdigest() == item['sha256'], rel

def main():
    base = json.loads((WORK / 'preservation-before.json').read_text())
    preserve(base)
    assert not PACKET.exists(), 'Inspect existing packet before any retry'
    names = json.loads((WORK / 'new-modules.json').read_text())
    strict = json.loads((WORK / 'strict-recheck.json').read_text())['modules']
    audit = json.loads((WORK / 'combined-audit-result.json').read_text())
    assert set(strict) == set(names) and len(names) == 11
    assert audit['status'] == 'PASS' and audit['declarations'] == 1081
    assert audit['theorem_constants'] == 739 and audit['all_11_namespaces_lint_passed']
    assert sha(WORK / 'CombinedBitCounterAudit.lean') == audit['auditor_sha256']
    assert sha(WORK / 'CombinedBitCounterAudit.log') == audit['log_sha256']
    log = (WORK / 'CombinedBitCounterAudit.log').read_text()
    assert log.count('-- All linting checks passed!') == 11
    assert 'error:' not in log and 'sorryAx' not in log
    assert sha(ROOT / 'RiemannGaussian.lean') == audit['root_facade_source_sha256']
    assert sha(ROOT / '.lake/build/lib/lean/RiemannGaussian.olean') == audit['root_facade_olean_sha256']
    modules = {}
    for name in names:
        src = ROOT / 'RiemannGaussian' / (name + '.lean')
        obj = ROOT / '.lake/build/lib/lean/RiemannGaussian' / (name + '.olean')
        item = strict[name]
        assert item['exit_code'] == 0 and item['isolated_matches_root_olean']
        assert sha(src) == item['source_sha256']
        assert sha(obj) == item['olean_sha256'] == item['root_olean_sha256']
        assert sha(WORK / 'strict-objects' / (name + '.olean')) == item['olean_sha256']
        assert sha(WORK / (name + '-strict.log')) == item['log_sha256']
        code = re.sub(r'/-.*?-/', '', src.read_text(), flags=re.S)
        code = re.sub(r'--[^\n]*', '', code)
        assert not re.search(r'\b(sorry|admit|sorryAx|native_decide)\b', code), name
        modules[name] = dict(source=str(src.relative_to(ROOT)), source_sha256=sha(src),
                            olean_sha256=sha(obj), **audit['per_module']['RiemannGaussian.' + name])
    dependencies = json.loads((WORK / 'strict-dependency-snapshot.json').read_text())
    for name, item in dependencies.items():
        rel = Path(*name.split('.'))
        assert sha(ROOT / rel.with_suffix('.lean')) == item['source_sha256'], name
        assert sha(ROOT / '.lake/build/lib/lean' / rel.with_suffix('.olean')) == item['olean_sha256'], name
    for file in WORK.glob('*.json'):
        data = json.loads(file.read_text())
        if isinstance(data, dict):
            for path, digest in data.items():
                if path.startswith('/') and isinstance(digest, str) and re.fullmatch('[0-9a-f]{64}', digest):
                    assert sha(Path(path)) == digest, (file.name, path)
    for name, digest in json.loads((WORK / 'review-public-count-heights-hashes.json').read_text()).items():
        assert sha(ROOT / 'RiemannGaussian' / (name + '.lean')) == digest
    hv = json.loads((WORK / 'hermite-verification.json').read_text())
    assert sha(Path(hv['source'])) == hv['sha256']
    assert subprocess.run(['git', 'diff', '--check'], cwd=ROOT, capture_output=True).returncode == 0

    selected = []
    for path in sorted(WORK.iterdir()):
        if not path.is_file() or 'probe' in path.name.lower():
            continue
        keep = path.suffix in ('.md', '.json', '.log', '.py') or path.name == 'strict-toolchain.txt'
        keep |= path.suffix == '.lean' and (path.name.startswith('Check')
                or path.name.endswith('-root-audit.lean') or path.name.endswith('-evaluation.lean')
                or path.name == 'CombinedBitCounterAudit.lean')
        if keep:
            if path.suffix == '.log':
                assert 'error:' not in path.read_text(), path.name
            selected.append(path)
    PACKET.mkdir()
    provenance = {}
    for source in selected + [ROOT / 'RiemannGaussian' / (name + '.lean') for name in names]:
        shutil.copyfile(source, PACKET / source.name)
        provenance[source.name] = dict(source=str(source), sha256=sha(source))
    dump(PACKET / 'archive-provenance.json', provenance)
    links = 0
    for md in PACKET.glob('*.md'):
        clean = re.sub(r'```.*?```', '', md.read_text(), flags=re.S)
        clean = re.sub(r'`[^`]*`', '', clean)
        for target in re.findall(r'\]\(([^)]+)\)', clean):
            if target.startswith(('http://', 'https://', '#')):
                continue
            assert (md.parent / target.split('#')[0]).exists(), (md.name, target)
            links += 1

    note = '''

## Native counter bit heights and actual entry execution, 2026-10-27

Packet: docs/research-evidence/semiprime-bit-counter-20261027.
Goal ACTIVE; slice PROGRESS. Whole-family guaranteed factoring bit-time OPEN.

Eleven NEW modules independently strict compiled; ordinary-root15 lint all11
PASS; all1081 generated declarations/739 theorem constants standard3-only.
Root/isolated objects byte-identical,141 local dependency sources/objects stable.
Prior1683 files,24 concurrent files and2 append-only prefixes preserved.

RationalBits executes actual Boolean-word reduction/GCD/exactdivision/copy and
add/mul/neg/inv; cost<=20000(W+1)^3 including rawwidth. DotBits executes one
suffix once and derives all product/sum Fits from common representations;
cost<=len*(40000(W+1)^3+4)+4. Physical word/report model, not wholeTMcompiler.

CounterPacketHeight derives actual source-row corrected ports and raw/node/Taylor
packet bounds over delta^M. FibreAccumulatorHeight proves actual measurement/
forced/group/representative-prefix expansions, records<=labels.card*2^n, varying
groups and recordwise masks. LocalPrefixHeight attaches actual truth subtotals
and selected-port leaf products to same-arity padded integer numerators. Bounds
are cancellation-independent, not small-final-count arguments or fit oracles.

HermiteArrayHeight builds cardinal jets AND full cardinal-at-zero intrinsically,
then cached inverse/quotient/eval/node sum. Common all-node denominator
dL*(dH*dL^J), all relevant suffix/prefix representations, polynomial binary
envelope b+16(Q+J+1)^5. H packet array ACQUISITION is still a separate frontend.

EntryExecution+BitPrimitives+BitCheck execute literal decoder/normalizer, modular
expressions, integercarry and every original vertex predicate, malformedinputs
included. New SubdividedEntry adds actual2bit equality, giving exactly the
FULL counter graph table. Public backendclock<=2^20*(64L+2)^10. Preparation
note pays publicdigit/descriptors,gathers,syntax/literalcells,flatbinaryaccess;
loose2^120*(64L+2)^40 fullbitbound is PAPER-level simulation, not LeanTMcompile.

PublicConstructedCount joins actual scheduled sourcecounter directly to
OrdinaryFactors cardinal under sourceguard. Actual coverage derived from
occurrence2; no count/coverage premise. Includes generic finite-set/Boolean
reindexing, restricted counts, positivity and searchcallbound. Runtime and
original-input recovery execution still separate.

Independent completebit audit found NO additional exponential operation after
two repairs: partialsortedGaussian scratch needs O(K²(logA+logK)+inputbits),
not completedrow's tightminorbound; localtruth expansion needs explicitl1
factorization <=[J(delta+2P)]^arity. Actual conditional-score common denominator
4*r²*b²*D² (epsilon=a/b), actualPython streamingstate polynomial. Numerical
constant16435 explicitly UNPINNED; independent finitegeneratingfunction gives
Cq=exp(o n), preserving candidateN^o1 without that constant. Manual audit
supportsordinarybitargument, not completedformalwholeexecution.

NEXT: explicit computable finite enumerations (wrapper defaultEnumerations still
noncomputable), paid actual originalrow Gaussian/binomial solver, complete H
array/interpreter correspondence, rational/entry/control/storage costcomposition,
then guard+finitefallback+publicprefixrecovery+rate inONEallinput theorem.
Logicalexpandedheightrecords mustNOTbe executed/materialized. Pythonproduction
source_factor_search uses no directcountoracle; optionalcaps excluded. Native
longquery softK^1.25 unchanged. External fixed-k SAT kernel audit stays frozen.
No commit/push, no new semiprime-success campaign, no goal completion.
'''
    for rel in base['prefixes']:
        with (ROOT / rel).open('a') as output:
            output.write(note)
    preserve(base)
    dump(PACKET / 'verification.json', dict(status='PASS',
        timestamp_utc=time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime()),
        goal_status='active', slice_status='PROGRESS',
        totals=dict(modules=11, declarations=1081, theorem_constants=739),
        modules=modules, strict_flags=['autoImplicit=false', 'warningAsError=true'],
        all_generated_declarations=True, ordinary_root_import=True,
        allowed_transitive_axioms=['propext', 'Classical.choice', 'Quot.sound'],
        stable_local_dependencies=len(dependencies),
        preserved={key:len(value) for key,value in base.items()}, local_markdown_links=links,
        primitive_factoring_bit_time_proved=False, native_softK_acquisition_proved=False,
        independent_full_bit_review='Repaired candidate supported; formal execution joins open',
        commit_or_push=False))
    assert subprocess.run(['git', 'diff', '--check'], cwd=ROOT, capture_output=True).returncode == 0
    files = {p.name:dict(bytes=p.stat().st_size, sha256=sha(p))
             for p in sorted(PACKET.iterdir()) if p.is_file() and p.name != 'manifest.json'}
    dump(PACKET / 'manifest.json', dict(status='PASS', files=files))
    for name, item in files.items():
        assert sha(PACKET / name) == item['sha256']
    preserve(base)
    print(json.dumps(dict(status='PASS', packet=str(PACKET), files=len(files)+1,
        modules=11, declarations=1081, theorem_constants=739)))

if __name__ == '__main__':
    main()
