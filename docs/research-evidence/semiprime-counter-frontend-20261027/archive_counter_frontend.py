"""Seal the checked coefficient-to-count slice without altering earlier evidence."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess,time
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-counter-frontend-20261027')
PACKET=ROOT/'docs/research-evidence/semiprime-counter-frontend-20261027'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
def preserve(base):
    for k in ('protected','concurrent'):
        for rel,digest in base[k].items():assert sha(ROOT/rel)==digest,(k,rel)
    for rel,x in base['prefixes'].items():
        assert hashlib.sha256((ROOT/rel).read_bytes()[:x['bytes']]).hexdigest()==x['sha256'],rel

def resolve_pin(k):
    if k.startswith('/'):return Path(k)
    if k.startswith('RiemannGaussian/'):return ROOT/k
    if k.startswith('Semiprime') and '.' not in k:return ROOT/'RiemannGaussian'/(k+'.lean')
    return WORK/k

def main():
    base=json.loads((WORK/'preservation-before.json').read_text());preserve(base)
    assert not PACKET.exists(),'Inspect existing packet before retrying'
    mods=json.loads((WORK/'all-modules.json').read_text())
    strictdata=json.loads((WORK/'all-strict-recheck.json').read_text());assert strictdata['complete']
    strict=strictdata['modules'];assert set(strict)==set(mods) and len(mods)==17
    log=(WORK/'CombinedCounterFrontendAudit.log').read_text()
    assert log.count('-- All linting checks passed!')==len(mods)
    assert 'error:' not in log and 'sorryAx' not in log
    audits={m:{'declarations':int(d),'theorem_constants':int(t)} for m,d,t in
        re.findall(r'^AUDIT RiemannGaussian\.(\w+): declarations=(\d+), theorems=(\d+), standard_axioms_only=true$',log,re.M)}
    assert set(audits)==set(mods)
    totals={'modules':len(mods),'declarations':sum(x['declarations'] for x in audits.values()),
            'theorem_constants':sum(x['theorem_constants'] for x in audits.values())}
    assert f"TOTAL modules={len(mods)}, declarations={totals['declarations']}, theorems={totals['theorem_constants']}, standard_axioms_only=true" in log
    modules={}
    for name in mods:
        src=ROOT/'RiemannGaussian'/(name+'.lean');obj=ROOT/'.lake/build/lib/lean/RiemannGaussian'/(name+'.olean')
        x=strict[name];assert x['exit_code']==0 and x['isolated_matches_root_olean']
        assert sha(src)==x['source_sha256'],name
        assert sha(obj)==x['root_olean_sha256']==x['olean_sha256']==sha(WORK/'strict-objects'/(name+'.olean')),name
        assert sha(WORK/(name+'-strict.log'))==x['log_sha256'],name
        code=re.sub(r'/-.*?-/', '',src.read_text(),flags=re.S);code=re.sub(r'--[^\n]*','',code)
        assert not re.search(r'\b(sorry|admit|sorryAx|native_decide)\b',code),name
        modules[name]={'source':str(src.relative_to(ROOT)),'source_sha256':sha(src),'olean_sha256':sha(obj),**audits[name]}
    deps=json.loads((WORK/'strict-dependency-snapshot.json').read_text())
    for m,x in deps.items():
        rel=Path(*m.split('.'));assert sha(ROOT/rel.with_suffix('.lean'))==x['source_sha256'],m
        assert sha(ROOT/'.lake/build/lib/lean'/rel.with_suffix('.olean'))==x['olean_sha256'],m
    for name in ['review-acquired-counter-hashes.json','review-controller-source-hashes.json',
                 'review-enumeration-source-hashes.json','row-hashes.json']:
        x=json.loads((WORK/name).read_text());pins=x['sha256'] if isinstance(x.get('sha256'),dict) else x
        for k,v in pins.items():
            if isinstance(v,str) and re.fullmatch('[0-9a-f]{64}',v):assert sha(resolve_pin(k))==v,(name,k)
    for name in ['arrayops-verification.json','local-verification.json','group-verification.json']:
        x=json.loads((WORK/name).read_text());assert sha(Path(x['source']))==x['sha256'],name
    assert (WORK/'acquired-counter-smoke.log').read_text().strip()=='(1, 2428)\n2\n0'
    assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
    selected=set()
    for p in WORK.iterdir():
        if p.is_file() and p.suffix in ('.md','.json'):selected.add(p)
    names=['CombinedCounterFrontendAudit.lean','CombinedCounterFrontendAudit.log',
        'CombinedNativeFrontendAudit.lean','combined-native-frontend-audit.log',
        'CombinedFrontendAudit.lean','combined-frontend-audit.log',
        'strict_recheck_all.py','strict_recheck.py','archive_counter_frontend.py','strict-recheck-all-run.log',
        'AcquiredCounterSmoke.lean','acquired-counter-smoke.log','RuntimeDesignSmoke.lean',
        'ReviewRuntimeDesignSmoke.lean','review-runtime-signatures.log','review-runtime-smoke.log',
        'CheckRows.lean','row-audit.log','row-controls.lean','row-controls.log','row-build.log','row-tracked-build.log',
        'arrayops-root-audit.lean','arrayops-root-audit.log','local-root-audit.lean','local-root-audit.log',
        'group-root-audit.lean','group-root-audit.log',
        'ComputablePackingSmoke.lean','computable-packing-smoke.log','FrontendSmoke.lean','frontend-smoke.log']
    for name in names:selected.add(WORK/name)
    for name in mods:selected.add(WORK/(name+'-strict.log'))
    selected.update(WORK.glob('*-isolated.log'))
    for p in selected:
        assert p.exists(),p.name
        if p.suffix=='.log':assert 'error:' not in p.read_text() and 'Traceback' not in p.read_text(),p.name
    PACKET.mkdir();provenance={}
    for p in sorted(selected)+[ROOT/'RiemannGaussian'/(name+'.lean') for name in mods]:
        assert p.name not in provenance,p.name
        shutil.copyfile(p,PACKET/p.name);provenance[p.name]={'source':str(p),'sha256':sha(p)}
    dump(PACKET/'archive-provenance.json',provenance)
    links=0
    for p in PACKET.glob('*.md'):
        clean=re.sub(r'```.*?```','',p.read_text(),flags=re.S);clean=re.sub(r'`[^`]*`','',clean)
        for target in re.findall(r'\]\(([^)]+)\)',clean):
            if target.startswith(('http://','https://','#')):continue
            assert (p.parent/target.split('#')[0]).exists(),(p.name,target)
            links+=1
    note=f'''

## Executed coefficient-to-count frontend, 2026-10-27

Packet: docs/research-evidence/semiprime-counter-frontend-20261027.
Goal ACTIVE; slice PROGRESS. Whole-family guaranteed factoring bit-time OPEN.

{totals['modules']} new modules strict+ordinary-root15lint PASS; all{totals['declarations']} generated declarations/
{totals['theorem_constants']} theorem constants transitive-standard3-only. Independent strict objects
match root objects; {len(deps)} local dependency sources/objects stable. Prior1797 files,
24 concurrent files and2 append-only prefixes preserved. No commit/push.

Explicit finite enumerations construct source alphabets and packing adapters;
r^Q/r^(2Q) lists are polynomial ONLY under scheduled D. MixedRadix scans full
summary codes without materializing Y tuples. Computed original-row RREF selector
closes span/LI/rank/inSpan; tracked SAME state costs <=8m(n+1)^2 rational calls
and <=mn pivot tests. Minor/scratch bit bounds remain constructive paper-level.
ExecutedNodeDesign computes selected original integer rows and native locality;
lazy fields may recompute polynomial preprocessing, so cache or pay explicitly.

RepresentativeExecution/FibreArrayExecution/PacketArrayExecution execute actual
false-first reps, forced measurement scans, separate local group products,
full summary sweep and signed support traversal. NativeLocal shifts SOURCE
coefficient arrays by Horner, caches corrected ports, streams paid truth entries.
NativeGroup supplies actual groupValue; no group/fibre/H output oracle remains
at the coefficient-array interface. AcquiredHermite invokes each node once,
copies J coefficients and retains all callback work in actual scalar recovery.
NodeArrayExecution.count_correct reaches originalContraction using only source
coefficient correctness, native row design, degree/restoration and precision.

Executable caller audit caught proof-only polynomial rows leaking into the
first runtime API. Repaired RuntimeDesign has ONLY finite data; fibre/node/count
signatures contain no Polynomial/Data index. Actual Lean eval yields1/2/0 on
one-variable table controls (diagnostic executability, not asymptotic evidence).
Independent review explicitly records prior missed issue and repaired interface.

Work envelope remains poly(dimensions)*Cq*Y*2^H*2^W plus Hermite polynomial cost.
No global2^n traversal or retained huge summary/fibre/truth table. Displayed work
is scalar/read/selected-control ledger, NOT primitive bits: div/mod, finite-set
ops, closure/index access, source/design supplier generation and physical rational
arithmetic still need composition. Suffix truth tensors need generic restricted-
table height bounds, not verbatim full-T mask theorem. CandidateN^o1 unchanged;
original long query softK^1.25 unchanged. External fixed-k SAT audit frozen.

NEXT: complete actual source coefficient arrays/binomial solve; materialize
computed design; attach EVERY new interpreter prefix height and primitive
bit/control/storage execution; instantiate public graph/entry/prefix recovery;
compose guard+finite fallback+rate in ONE all-input factoring bit theorem.
'''
    for rel in base['prefixes']:
        with (ROOT/rel).open('a') as f:f.write(note)
    preserve(base)
    verification={'status':'PASS','timestamp_utc':time.strftime('%Y-%m-%d %H:%M:%S UTC',time.gmtime()),
      'goal_status':'active','slice_status':'PROGRESS','totals':totals,'modules':modules,
      'strict_flags':['autoImplicit=false','warningAsError=true'],'all_generated_declarations':True,
      'ordinary_root_import':True,'linters_per_namespace':15,
      'allowed_transitive_axioms':['propext','Classical.choice','Quot.sound'],
      'root_facade_source_sha256':sha(ROOT/'RiemannGaussian.lean'),
      'root_facade_olean_sha256':sha(ROOT/'.lake/build/lib/lean/RiemannGaussian.olean'),
      'auditor_sha256':sha(WORK/'CombinedCounterFrontendAudit.lean'),
      'audit_log_sha256':sha(WORK/'CombinedCounterFrontendAudit.log'),
      'stable_local_dependencies':len(deps),'preserved':{k:len(v) for k,v in base.items()},
      'local_markdown_links':links,'runtime_polynomial_index_removed':True,
      'coefficient_to_count_execution_proved':True,'primitive_factoring_bit_time_proved':False,
      'native_softK_acquisition_proved':False,'commit_or_push':False}
    dump(PACKET/'verification.json',verification)
    assert subprocess.run(['git','diff','--check'],cwd=ROOT,capture_output=True).returncode==0
    manifest={p.name:{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(PACKET.iterdir()) if p.is_file() and p.name!='manifest.json'}
    dump(PACKET/'manifest.json',{'status':'PASS','files':manifest})
    for name,x in manifest.items():assert sha(PACKET/name)==x['sha256']
    preserve(base)
    print(json.dumps({'status':'PASS','packet':str(PACKET),'files':len(manifest)+1,'totals':totals}))
if __name__=='__main__':main()
