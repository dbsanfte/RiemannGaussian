"""Pre-sealed supplied divisor-coupling identity calibration; no scores."""
import ast,hashlib,json,pathlib,subprocess,sys
import cancellation_divisor_coupling as P
import check_cancellation_divisor_coupling as C
ROOT=pathlib.Path(__file__).resolve().parent
TESTS=['test_cancellation_divisor_coupling','test_check_cancellation_divisor_coupling','test_run_cancellation_divisor_coupling_calibration']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v):
 with p.open('x')as f:json.dump(v,f,sort_keys=True,indent=2,allow_nan=False);f.write('\n')
def sources():
 pending=['run_cancellation_divisor_coupling_calibration',*TESTS];seen=set()
 while pending:
  name=pending.pop();f=ROOT/(name+'.py')
  if name in seen or not f.is_file():continue
  seen.add(name)
  for node in ast.walk(ast.parse(f.read_text())):
   if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
   elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
 return sorted(n+'.py'for n in seen)
def fixtures():
 return [dict(id='unit',H=1,weights=['1']),dict(id='signed_unit',H=1,weights=['-3/2']),dict(id='zero_unit',H=1,weights=['0']),dict(id='mixed_complete',H=6,weights=['2/3','-1','0','5/7','-2','1/4']),dict(id='zero_head',H=5,weights=['0','1','-1/2','0','3']),dict(id='all_zero',H=4,weights=['0']*4)]
def run(directory):
 if not __debug__:raise RuntimeError('assertions enabled required')
 d=pathlib.Path(directory).resolve();d.mkdir(parents=True,exist_ok=False);(d/'frozen_source').mkdir()
 prior=ROOT/'cancellation-arithmetic-results/divisor-localizer-probe-001';verification=json.loads((prior/'independent_verification.json').read_text())
 if verification['all_passed']is not True:raise ValueError('parent not verified')
 original=json.loads((prior/'source_seal.json').read_text())
 def validate_prior():
  for n,h in original.items():
   if sha(ROOT/n)!=h or sha(prior/'frozen_source'/n)!=h:raise ValueError('prior source changed '+n)
 validate_prior();inputs={n:sha(prior/n)for n in ['source_seal.json','independent_verification.json','receipt.json']};code={n:sha(ROOT/n)for n in sources()}
 for n in code:(d/'frozen_source'/n).write_bytes((ROOT/n).read_bytes())
 spec=dict(schema=1,fixtures=fixtures(),source_sha256=code,parent_path=str(prior.relative_to(ROOT)),parent_input_sha256=inputs,tests=TESTS,method='supplied complete polynomial identity calibration; independent checker; no actual arithmetic response or bound search',global_bound_proved=False,RH_proved=False)
 write(d/'spec.json',spec);write(d/'seal.json',dict(spec_sha256=sha(d/'spec.json')))
 def validate():
  validate_prior()
  for n,h in inputs.items():
   if sha(prior/n)!=h:raise ValueError('parent input changed')
  for n,h in code.items():
   if sha(ROOT/n)!=h or sha(d/'frozen_source'/n)!=h:raise ValueError('calibration source changed '+n)
  if json.loads((d/'seal.json').read_text())['spec_sha256']!=sha(d/'spec.json'):raise ValueError('spec changed')
 t=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=60);write(d/'tests.json',dict(returncode=t.returncode,stdout=t.stdout,stderr=t.stderr))
 if t.returncode:raise ValueError('tests failed')
 validate();rows=[]
 for f in spec['fixtures']:
  out=P.build_coupling(f['H'],f['weights']);check=C.check_coupling(f['H'],f['weights'],out);rows.append(dict(fixture=f,producer=out,independent_check=check))
 if not all(r['independent_check']['verified']for r in rows):raise ValueError('independent fixture failed')
 write(d/'results.json',dict(fixtures=rows,all_passed=True,supplied_identity_not_discovery=True,global_bound_proved=False,RH_proved=False));validate()
 write(d/'independent_verification.json',dict(all_passed=True,fixtures_verified=len(rows),input_sha256={n:sha(d/n)for n in ['spec.json','seal.json','tests.json','results.json']},complete_cross_terms_verified=True,actual_sign_values_substituted=False,global_bound_proved=False,RH_proved=False))
 write(d/'manifest.json',dict(schema=1,files={str(p.relative_to(d)):sha(p)for p in sorted(d.rglob('*'))if p.is_file()},global_bound_proved=False,RH_proved=False));return dict(all_passed=True,fixtures=len(rows),sources=len(code))
if __name__=='__main__':print(json.dumps(run(sys.argv[1])))
