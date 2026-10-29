#!/usr/bin/env python3
"""Audit existing pinned artifacts; never invokes a build of their closure."""
import argparse, hashlib, json, os, pathlib, subprocess, time
BASE=pathlib.Path('/tmp/semiprime-d1-audit-20261026')
OUT=pathlib.Path('/tmp/semiprime-layout-assembly-20261026')
SOURCE=BASE/'openai-math/lean'
BUILD=BASE/'lean-build'
LEAN='/home/dbsanfte/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
LAKE='/home/dbsanfte/.elan/bin/lake'
FORMAL=pathlib.Path('/home/dbsanfte/riemann/formal')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def generate(modules,target,path,report):
    names=',\n    '.join('`'+m for m in sorted(modules))
    text=f'''import {target}
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 20000
-- Iterate original source-module constants, including generated/private names.
run_cmd do
  let selected : NameSet := #[{names}].foldl (fun s n => s.insert n) {{}}
  let env ← getEnv
  let mut modules : Nat := 0
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut rows : Array Json := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]
    unless selected.contains moduleName do continue
    modules := modules+1
    let mut count : Nat := 0
    let mut proofs : Nat := 0
    for ci in env.header.moduleData[i]!.constants do
      count := count+1
      if ci.isAxiom then throwError "Source-defined axiom: {{ci.name}}"
      if ci.isTheorem then proofs := proofs+1
      for ax in (← Lean.collectAxioms ci.name) do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Unexpected transitive axiom in {{ci.name}}: {{ax}}"
    declarations := declarations+count
    theorems := theorems+proofs
    rows := rows.push (Json.mkObj [("module", toJson moduleName.toString),
      ("declarations", toJson count), ("theorems", toJson proofs)])
    if modules % 128 == 0 then
      logInfo m!"Audited {{modules}} source modules, {{declarations}} declarations."
  unless modules == {len(modules)} do
    throwError "Wrong source-module count: {{modules}}, expected {len(modules)}"
  unless theorems > 0 do throwError "No source theorem checked"
  let report := Json.mkObj [("status", toJson "PASS"),
    ("source_modules", toJson modules), ("declarations", toJson declarations),
    ("theorems", toJson theorems), ("per_module", Json.arr rows)]
  liftIO (IO.FS.writeFile "{report}" report.pretty)
  logInfo m!"PASS: {{modules}} source modules, {{declarations}} declarations, {{theorems}} theorem constants; standard axioms only."
'''
    path.write_text(text)

def endpoint():
    comparator=SOURCE/'ComparatorChallenges/SubexponentialSAT.lean'
    text=comparator.read_text(); beg=text.index('theorem exact_count_and_sat (')
    end=text.index(' := by',beg)
    signature=text[beg:end].replace('theorem exact_count_and_sat (','theorem externalAuditComparatorEndpoint (',1)
    content='import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final\n'
    content+='namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace\n'
    content+=signature+' := by\n  exact exact_count_and_sat k hk\n'
    content+='#print axioms externalAuditComparatorEndpoint\nend OAI.Algorithms.SubexponentialSAT.SqrtLogSpace\n'
    (OUT/'ExternalComparatorEndpoint.lean').write_text(content)
    (OUT/'external-comparator-signature.txt').write_text(text[beg:end]+'\n')

def env():
    raw=subprocess.check_output([LAKE,'env','printenv','LEAN_PATH'],cwd=FORMAL,text=True).strip()
    paths=[p for p in raw.split(':') if '/.lake/packages/' in p or '/.elan/toolchains/' in p]
    assert paths, 'No matching package cache paths'
    return dict(os.environ,LEAN_PATH=':'.join([str(BUILD)]+paths))

def compile_file(path,log,timeout):
    started=time.time()
    with log.open('w') as out:
        done=subprocess.run(['/usr/bin/time','-v','-o',str(log.with_suffix('.resources.txt')),LEAN,'-R',str(OUT),'-DautoImplicit=false','-DwarningAsError=true','-j1',str(path)],
             cwd=OUT,env=env(),stdout=out,stderr=subprocess.STDOUT,timeout=timeout)
    return {'exit_code':done.returncode,'seconds':round(time.time()-started,3),'log':str(log)}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--run',action='store_true');ap.add_argument('--preflight',action='store_true');ap.add_argument('--timeout',type=int,default=3600);args=ap.parse_args()
    OUT.mkdir(exist_ok=True)
    closure=json.loads((BASE/'lean-closure.json').read_text())
    state=json.loads((BASE/'lean-build-state.json').read_text())
    assert closure['head']==subprocess.check_output(['git','rev-parse','HEAD'],cwd=SOURCE,text=True).strip()
    assert not closure['missing']
    assert state['commit']==closure['head']
    assert state['compiler']==LEAN
    modules=closure['modules']
    generate(modules,closure['target'],OUT/'ExternalEveryDeclaration.lean',OUT/'external-every-declaration.json')
    endpoint()
    manifest={'runner_sha256':sha(pathlib.Path(__file__)),'commit':closure['head'],'target':closure['target'],'source_modules':len(modules),
        'comparator_config':json.loads((SOURCE/'ComparatorChallenges/SubexponentialSAT.json').read_text()),
        'generated':{p.name:sha(p) for p in [OUT/'ExternalEveryDeclaration.lean',OUT/'ExternalComparatorEndpoint.lean']},
        'snapshot':{'status':state['status'],'completed':len(state['completed']),'failed':len(state['failed'])}}
    (OUT/'external-audit-plan.json').write_text(json.dumps(manifest,indent=2)+'\n')
    if args.preflight:
        mod='OAI.Algorithms.SubexponentialSAT.Factor'
        assert mod in state['completed']
        generate([mod],mod,OUT/'ExternalAuditPreflight.lean',OUT/'external-preflight.json')
        result=compile_file(OUT/'ExternalAuditPreflight.lean',OUT/'external-preflight.log',args.timeout)
        print(json.dumps(result));return result['exit_code']
    if not args.run:
        print(json.dumps({'status':'prepared','live_build':manifest['snapshot']}));return 0
    if state['status']!='complete' or state['failed'] or set(state['completed'])!=set(modules):
        print(json.dumps({'status':'NOT_READY','live_build':manifest['snapshot']}));return 2
    tree=subprocess.check_output(['git','ls-tree','-r','--full-tree','HEAD','lean'],cwd=SOURCE.parent,text=True)
    pinned_blobs={line.split('\t',1)[1]:line.split()[2] for line in tree.splitlines()}
    for rel in ['ComparatorChallenges/SubexponentialSAT.lean','ComparatorChallenges/SubexponentialSAT.json','docs/378.md']:
        data=(SOURCE/rel).read_bytes()
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==pinned_blobs['lean/'+rel],rel
    files=[]
    for mod in sorted(modules):
        rel=pathlib.Path(*mod.split('.'));src=(SOURCE/rel).with_suffix('.lean');obj=(BUILD/rel).with_suffix('.olean');r=state['completed'][mod]
        assert r['exit_code']==0,mod
        assert sha(src)==r['source_sha256'],mod
        data=src.read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert blob==pinned_blobs['lean/'+str(src.relative_to(SOURCE))],mod
        assert sha(obj)==r['olean_sha256'],mod
        files.append({'module':mod,'source_sha256':sha(src),'source_commit_blob_sha1':blob,'olean_sha256':sha(obj)})
    (OUT/'external-complete-artifacts.json').write_text(json.dumps(files,indent=2)+'\n')
    for stale in ['external-every-declaration.json','external-final-audit-results.json']:
        (OUT/stale).unlink(missing_ok=True)
    results={}
    for stem in ['ExternalComparatorEndpoint','ExternalEveryDeclaration']:
        results[stem]=compile_file(OUT/(stem+'.lean'),OUT/(stem+'.log'),args.timeout)
        if results[stem]['exit_code']:break
    results['status']='PASS' if len(results)==2 and all(v['exit_code']==0 for v in results.values()) else 'FAIL'
    (OUT/'external-final-audit-results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results));return int(results['status']!='PASS')
if __name__=='__main__':raise SystemExit(main())
