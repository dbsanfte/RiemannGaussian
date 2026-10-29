"""Freeze the checked construction slice, preserving prior and concurrent work."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess, time

ROOT = Path('/home/dbsanfte/riemann/formal')
WORK = Path('/tmp/semiprime-layout-assembly-20261026')
EXTERNAL = Path('/tmp/semiprime-d1-audit-20261026')
PACKET = ROOT / 'docs/research-evidence/semiprime-layout-assembly-20261026'
BASE = json.loads((WORK / 'preservation-before.json').read_text())
NAMES = json.loads((WORK / 'new-modules.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def preserve():
    for kind in ('protected', 'concurrent'):
        for rel, h in BASE[kind].items():
            assert sha(ROOT / rel) == h, rel
    for rel, item in BASE['prefixes'].items():
        assert hashlib.sha256((ROOT / rel).read_bytes()[:item['bytes']]).hexdigest() == item['sha256'], rel
    assert (ROOT / 'lake-manifest.json').read_bytes() == (WORK / 'lake-manifest.json.before').read_bytes()

def local_targets(path):
    text = re.sub(r'```.*?```', '', path.read_text(), flags=re.S)
    text = re.sub(r'`[^`]*`', '', text)
    return re.findall(r'\]\(([^)]+)\)', text)

def dump(name, value):
    (PACKET / name).write_text(json.dumps(value, indent=2) + '\n')

def main():
    preserve()
    assert not PACKET.exists(), 'Packet exists; inspect partial state instead of rerunning'
    checks = json.loads((WORK / 'strict-recheck.json').read_text())
    assert set(checks) == set(NAMES)
    modules = {}
    audit = (WORK / 'combined-audit.log').read_text()
    assert 'error:' not in audit and 'sorryAx' not in audit
    rows = re.findall(r'AUDIT RiemannGaussian\.(\w+): declarations=(\d+), theorems=(\d+), standard_axioms_only=true', audit)
    assert {r[0] for r in rows} == set(NAMES)
    for name, declarations, theorems in rows:
        src = ROOT / 'RiemannGaussian' / (name + '.lean')
        obj = ROOT / '.lake/build/lib/lean/RiemannGaussian' / (name + '.olean')
        rec = checks[name]
        assert rec['exit_code'] == 0
        assert sha(src) == rec['source_sha256']
        assert sha(WORK / (name + '-strict.log')) == rec['log_sha256']
        assert sha(WORK / 'strict-objects' / (name + '.olean')) == rec['olean_sha256']
        assert sha(obj) == rec['olean_sha256'], name + ' root/isolated object mismatch'
        modules[name] = dict(source=str(src.relative_to(ROOT)), source_sha256=sha(src),
            olean_sha256=sha(obj), strict_build='PASS', root_lint='PASS',
            declarations=int(declarations), theorems=int(theorems), transitive_axioms='standard_only')
    for rel, h in json.loads((WORK / 'review-layout-counter-hashes.json').read_text()).items():
        assert sha(ROOT / rel) == h, 'review hash: ' + rel
    graph_review = json.loads((WORK / 'review-macro-graph-source-hashes.json').read_text())
    for path, item in graph_review['files'].items():
        assert sha(Path(path)) == item['sha256'], path
    vendor = ROOT / 'vendor/openai-semiprime'
    pin = json.loads((vendor / 'upstream-pin.json').read_text())
    for rel, rec in pin['files'].items():
        assert sha(vendor / rel) == rec['adapted_sha256']
    assert 'modules=63, declarations=2764, theorems=2023, standard_axioms_only=true' in (WORK / 'vendor-audit.log').read_text()
    external = json.loads((WORK / 'external-final-audit-results.json').read_text())
    assert external['status'] == 'PASS'
    external_decls = json.loads((WORK / 'external-every-declaration.json').read_text())
    assert external_decls['status'] == 'PASS' and external_decls['source_modules'] == 2569
    state = json.loads((EXTERNAL / 'lean-build-state.json').read_text())
    assert state['status'] == 'complete' and len(state['completed']) == 2569 and not state['failed']
    files = ['README.md', 'constructed-counter-proof.md', 'layout-cert-proof.md', 'layout-selection-proof.md',
        'source-rate-proof.md', 'source-height-proof.md', 'macro-graph-proof.md',
        'review-layout-counter.md', 'review-layout-counter-hashes.json',
        'review-macro-graph.md', 'review-macro-graph-source-hashes.json',
        'new-modules.json', 'CombinedLayoutAudit.lean', 'combined-audit.log',
        'CheckCertificates.lean', 'CheckSelection.lean', 'CheckSourceLayout.lean', 'CheckMacroGraph.lean',
        'layout-cert-audit.log', 'layout-cert-build.log', 'layout-selection-audit.log', 'layout-selection-build.log',
        'source-layout-audit.log', 'source-layout-build.log', 'constructed-counter-build.log',
        'source-rate-root-audit.lean', 'source-rate-root-audit.log', 'source-rate-build.log', 'source-rate-verification.json',
        'source-height-root-audit.lean', 'source-height-root-audit.log', 'source-height-build.log', 'source-height-verification.json',
        'graph-audit.log', 'graph-build.log', 'graph-build-metadata.json',
        'PinnedLayoutAudit.lean', 'source-closure.json', 'vendor-verification.json', 'vendor-audit.log', 'vendor-build.log',
        'strict_recheck.py', 'strict-recheck.json', 'archive_layout.py',
        'run_external_final_audit.py', 'external-final-audit.md', 'external-final-audit-results.json',
        'external-audit-plan.json', 'external-comparator-signature-check.json', 'external-comparator-signature.txt',
        'ExternalComparatorEndpoint.lean', 'ExternalComparatorEndpoint.log', 'ExternalComparatorEndpoint.resources.txt',
        'ExternalEveryDeclaration.lean', 'ExternalEveryDeclaration.log', 'ExternalEveryDeclaration.resources.txt',
        'external-complete-artifacts.json', 'external-every-declaration.json', 'external-main-extra-plan.json']
    files += [n + '-strict.log' for n in NAMES]
    for rel in files:
        assert (WORK / rel).is_file(), rel
    assert subprocess.run(['git', 'diff', '--check'], cwd=ROOT, capture_output=True).returncode == 0
    PACKET.mkdir()
    provenance = {}
    def copy(src, name):
        shutil.copyfile(src, PACKET / name)
        provenance[name] = {'source': str(src), 'sha256': sha(src)}
    for rel in files:
        copy(WORK / rel, rel)
    for name in NAMES:
        copy(ROOT / 'RiemannGaussian' / (name + '.lean'), name + '.lean')
    for name in ['upstream-pin.json', 'LICENSE.OpenAI-Math', 'OpenAISemiprime.lean']:
        copy(vendor / name, name)
    copy(ROOT / 'lakefile.toml', 'lakefile.toml.snapshot')
    copy(EXTERNAL / 'lean-closure.json', 'external-lean-closure.json')
    copy(EXTERNAL / 'lean-build-state.json', 'external-lean-build-state.json')
    copy(EXTERNAL / 'build_lean_closure.py', 'build_external_lean_closure.py')
    snapshot = dict(timestamp_utc=time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime()),
        status=state['status'], completed=2569, total=2569, failed=0, commit=state['commit'],
        exact_expected_endpoint_typechecked=True, every_source_declaration_audited=True,
        configured_Main_comparator_run=False, extra_Main_dependency_modules=522,
        primitive_factoring_runtime_proved=False)
    dump('external-build-snapshot.json', snapshot)
    dump('archive-provenance.json', provenance)
    links = 0
    for md in PACKET.glob('*.md'):
        for target in local_targets(md):
            if target.startswith(('http://', 'https://', '#')):
                continue
            assert (md.parent / target.split('#')[0]).exists(), (md.name, target)
            links += 1
    note = '''

## Constructed layout counter and concrete macro graph, 2026-10-27

Packet: docs/research-evidence/semiprime-layout-assembly-20261026.
Goal ACTIVE, current slice PROGRESS. Full uniform factoring bit-time remains OPEN.

SourceLayout constructs actual computed words/complete blocks/universal rows/
identity leftovers/original-owner pullback; derives restoration/degree/head/rank.
SourceLayoutHeight derives W=B*2*(8Q)^(2R), injective copies then bounded owner
fibre sum. LayoutCertificates derives rational span FROM integer-kernel locality;
LayoutSelection selects ACTUAL integer rows, preserving height and rank, and
constructs bounded signed summaries/representatives. ConstructedCounter applies
this to Sigma original ports, producing CounterSearch.Problem and exact prefix
counts/common-witness/noneiff/<=length+1 search WITHOUT supplied layout, row span,
certificate or counting-correctness oracle. Actual summary cardinality is linked
to constructed rows; <=(2*n*W+1)^c with c their true total rank.

SourceLayoutRate proves stronger eventual source load/head/Q-1-width guards,
W<=2^(lambda+2), box<=2^(6lambda), c*logbox<=24nlog2/r from actual rank budget,
and inverse-floor binary-rate envelope. Final network/schedule/primitive-time
composition not inferred. This source complete-block/cleared-defect construction
DIFFERS from frozen Python partial-copy/eigenbasis implementation.

MacroGraph closes actual ORDERED endpoint bijections, per-vertex scopes,
occurrence exactly two/no repeated scope variable, equality subdivision and
exact edge/port/vertex/arity counts. Physical n+1 carry words checked<2^n are
uniquely zero extensions. Missing: actual local entry predicates composed into
factor-pair semantics, padding/top-bit/target/public-N parameter proof, and
bit/space execution. Boolean-variable n differs from macro FFT word dimension.

Seven strict new modules: SourceLayout, SourceLayoutHeight, SourceLayoutRate,
LayoutCertificates, LayoutSelection, MacroGraph, ConstructedCounter. Root15lint,
all generated declaration transitive axioms, isolated/root object hashes PASS.
Standard propext/Classical.choice/Quot.sound only. Independent semantic reviews
PASS. Noncomputable finite/Boolean/basis choices still need execution refinement;
integer constraint height is not a bound on all rational intermediates.

NEW optional vendor/openai-semiprime: 63 upstream generic modules at
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, Apache2 license. ONLY import module
prefix/path OAI->OpenAISemiprime changed; namespaces/proofs unchanged. All63
source transformations verified; all2764 declarations/2023 theorems standard-only.
Optional library registered in lakefile; default targets/root imports/manifest
unchanged. Do not conflate source reuse with certification of Python code.

EXTERNAL full2569module Final source closure COMPLETE strict PASS; exact
comparator expected theorem signature typechecked against Final; EVERY original
declaration audited standard-only. Main configured wrapper not run:522 extra
dependencies. Actual theorem is primitive bit-tape exact count/SAT for EACH FIXED
k, older n(loglogn)^2/sqrt(logn) rate, polynomial visited space. It is not the
generic growing-arity tensor/AppendixD.1 theorem or a factoring complexity proof.

NEXT: actual graph predicate->factor count plus public size/arity/schedule
bridge; executable selected-row/word enumerations, cached jet/contraction/Hermite
loops and full primitive rational bit/space costs; compose factor recovery and
fallback into uniform all-input bound. Native longquery softK^1.25 unchanged.
Preserved1394 prior files,24 concurrent,2 append-only prefixes. No commit/push.
'''
    preserve()
    for rel in ('AGENTS.md', 'docs/semiprime-factorisation-investigation.md'):
        with (ROOT / rel).open('a') as out:
            out.write(note)
    preserve()
    result = subprocess.run(['git', 'diff', '--check'], cwd=ROOT, text=True, capture_output=True)
    assert result.returncode == 0, result.stdout + result.stderr
    dump('review.json', dict(goal_status='active', goal_complete=False, current_slice='progress',
        modules=modules, actual_layout_counter_connected=True, actual_ordered_graph_proved=True,
        graph_predicate_to_factor_count_proved=False, public_input_rate_composed=False,
        primitive_factoring_runtime_proved=False, native_long_query_improved=False,
        external_build=snapshot, preservation={**{k: len(v) for k, v in BASE.items()}, 'status': 'PASS'},
        local_links=links, git_diff_check='PASS', new_finite_campaign=False, commit_or_push=False))
    manifest = {p.name: sha(p) for p in sorted(PACKET.iterdir()) if p.is_file() and p.name != 'manifest.json'}
    dump('manifest.json', dict(algorithm='sha256', excludes_self=True, files=manifest))
    for rel, h in manifest.items():
        assert sha(PACKET / rel) == h
    preserve()
    print(json.dumps(dict(packet=str(PACKET), files=len(manifest)+1, modules=len(modules),
        preservation='PASS', external_final='PASS', goal_status='active'), indent=2))

if __name__ == '__main__':
    main()
