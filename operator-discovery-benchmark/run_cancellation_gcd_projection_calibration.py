"""Seal then run supplied gcd-projection identity fixtures, not discovery."""
import json,hashlib,pathlib,subprocess,sys
import cancellation_gcd_inverse_projection as P
import check_cancellation_gcd_inverse_projection as C
ROOT=pathlib.Path(__file__).resolve().parent
CODE=['run_cancellation_gcd_projection_calibration.py','cancellation_gcd_inverse_projection.py','test_cancellation_gcd_inverse_projection.py','check_cancellation_gcd_inverse_projection.py','test_check_cancellation_gcd_inverse_projection.py','cancellation_gcd_inverse_projection_independent_review.txt','grouped_arithmetic_language.py','arithmetic_cycle_language.py','cancellation_gram_language.py','check_cancellation_factor_blocks.py','check_grouped_arithmetic.py','check_arithmetic_cycle_certificate.py']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v):
 with p.open('x')as f:json.dump(v,f,sort_keys=True,indent=2,allow_nan=False)
def fixtures():
 return [dict(id='unit',H=1,kernel=[['1']],psd=True),dict(id='ones',H=4,kernel=[['1']*4 for _ in range(4)],psd=True),dict(id='reverse_prefix_Gram',H=4,kernel=[[str(5-max(a,b))for b in range(1,5)]for a in range(1,5)],psd=True),dict(id='asymmetric',H=3,kernel=[['1','-2','0'],['3','0','1/2'],['0','-1','2']],psd=False),dict(id='indefinite_diagonal',H=4,kernel=[['1'if a==b==0 else '-1'if a==b==1 else '0'for b in range(4)]for a in range(4)],psd=False),dict(id='zero',H=5,kernel=[['0']*5 for _ in range(5)],psd=True)]
def run(directory):
 d=pathlib.Path(directory);d.mkdir(exist_ok=False);(d/'frozen_source').mkdir();factor=ROOT/'cancellation-arithmetic-results/pilot-001/factor-probe-001';original=json.load(open(factor/'source_seal.json'))['hashes']
 for n,h in original.items():
  if sha(ROOT/n)!=h or sha(factor/'frozen_source'/n)!=h:raise ValueError('frozen factor source changed')
 sources={n:sha(ROOT/n)for n in CODE}
 for n in CODE:(d/'frozen_source'/n).write_bytes((ROOT/n).read_bytes())
 spec=dict(schema=1,fixtures=fixtures(),code=sources,previous_factor_source_seal_sha256=sha(factor/'source_seal.json'),method='supplied identity calibration; complete independent checker implementation in same process; no actual Mobius responses or bound search',global_bound_proved=False,RH_proved=False)
 write(d/'spec.json',spec);write(d/'seal.json',dict(spec_sha256=sha(d/'spec.json')))
 t=subprocess.run([sys.executable,'-B','-m','unittest','test_cancellation_gcd_inverse_projection','test_check_cancellation_gcd_inverse_projection'],cwd=ROOT,capture_output=True,text=True,timeout=60)
 write(d/'tests.json',dict(returncode=t.returncode,stdout=t.stdout,stderr=t.stderr))
 if t.returncode:raise ValueError('calibration tests failed')
 rows=[]
 for fixture in spec['fixtures']:
  output=P.build_projection(fixture['H'],fixture['kernel'],psd_kernel=fixture['psd']);check=C.check_projection(fixture['H'],fixture['kernel'],output)
  rows.append(dict(fixture=fixture,producer=output,independent_check=check))
 write(d/'results.json',dict(fixtures=rows,all_passed=all(r['independent_check']['verified']for r in rows),supplied_identity_not_discovery=True,global_bound_proved=False,RH_proved=False))
 if any(sha(ROOT/n)!=h or sha(d/'frozen_source'/n)!=h for n,h in sources.items()):raise ValueError('calibration sources changed')
 if sha(factor/'source_seal.json')!=spec['previous_factor_source_seal_sha256']:raise ValueError('factor seal changed')
 for n,h in original.items():
  if sha(ROOT/n)!=h or sha(factor/'frozen_source'/n)!=h:raise ValueError('factor source changed during calibration')
 write(d/'independent_verification.json',dict(all_passed=True,checker_sha256=sources['check_cancellation_gcd_inverse_projection.py'],input_sha256={n:sha(d/n)for n in ('spec.json','seal.json','tests.json','results.json')},fixtures_verified=6,signed_expression_is_PSD_certificate=False,global_bound_proved=False,RH_proved=False))
 write(d/'manifest.json',dict(schema=1,files={str(p.relative_to(d)):sha(p)for p in d.rglob('*')if p.is_file()},global_bound_proved=False,RH_proved=False))
 return dict(all_passed=True,fixtures=6,tests=6)
if __name__=='__main__':print(json.dumps(run(sys.argv[1])))
