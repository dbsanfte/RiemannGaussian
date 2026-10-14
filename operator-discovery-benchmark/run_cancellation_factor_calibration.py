"""Archive supplied factor identities; no discovery, fitting or bound search."""
from pathlib import Path
import json,hashlib,subprocess,sys
import cancellation_factor_blocks as producer
import check_cancellation_factor_blocks as independent
BASE=Path(__file__).resolve().parent
OWN=['cancellation_factor_blocks.py','test_cancellation_factor_blocks.py','check_cancellation_factor_blocks.py','test_check_cancellation_factor_blocks.py','cancellation_factor_block_groups.py','test_cancellation_factor_block_groups.py','run_cancellation_factor_calibration.py']
TESTS=['test_cancellation_factor_blocks','test_check_cancellation_factor_blocks','test_cancellation_factor_block_groups']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def run(directory):
 directory=Path(directory)
 if directory.exists():raise FileExistsError('new calibration archive required')
 parent=BASE/'cancellation-arithmetic-results/pilot-001/source_seal.json';parentdata=json.loads(parent.read_text());hashes=parentdata.get('hashes',parentdata.get('code_sha256'))
 if not isinstance(hashes,dict):raise ValueError('parent source seal schema')
 for n,h in hashes.items():
  if sha(BASE/n)!=h:raise ValueError('parent source dependency changed: '+n)
 directory.mkdir(parents=True);frozen=directory/'frozen_source';frozen.mkdir()
 names=sorted(set(hashes)|set(OWN));snapshot={}
 for n in names:
  data=(BASE/n).read_bytes();(frozen/n).write_bytes(data);snapshot[n]=hashlib.sha256(data).hexdigest()
 fixtures=[dict(q=q,X=X,coprime=c,target='mu',horizon=2*X) for q,X in [(2,8),(3,27),(6,64)] for c in [False,True]]
 spec=dict(schema=1,scope='SUPPLIED exact factor identity calibration; no discovery or solver scores',source_sha256=snapshot,parent_source_seal=dict(path=str(parent.relative_to(BASE)),sha256=sha(parent)),tests=TESTS,expected_test_count=10,fixtures=fixtures,multiplier=[dict(m=[1],c='1'),dict(m=[2],c='-1')],cutoff_coefficient='3/2',kernel=[dict(coefficient='3/5',a_power=1,b_power=0,x_power=0),dict(coefficient='-2/7',a_power=0,b_power=1,x_power=0)],global_bound_proved=False,RH_proved=False)
 write(directory/'protocol.json',spec);write(directory/'source_seal.json',dict(hashes=snapshot));write(directory/'seal.json',dict(protocol_sha256=sha(directory/'protocol.json'),source_seal_sha256=sha(directory/'source_seal.json'),frozen_before_fixtures=True))
 result=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS,'-q'],cwd=BASE,text=True,capture_output=True)
 write(directory/'tests.json',dict(modules=TESTS,returncode=result.returncode,stdout=result.stdout,stderr=result.stderr))
 if result.returncode or 'Ran 10 tests' not in result.stderr+result.stdout:raise ValueError('calibration contracts failed')
 outputs=[]
 for case in fixtures:
  cut=dict(lower=dict(coefficient='0',power='0'),upper=dict(coefficient='3/2',power='1/'+str(case['q'])))
  blockspec=dict(kind='factor_bilinear',product_scale='2',coprime=case['coprime'],cuts=dict(left=cut,right=cut),kernel=spec['kernel'])
  b=producer.build_block(blockspec,case['X'],case['horizon'],target=case['target'],multiplier=spec['multiplier']);audit=independent.check_block(b)
  outputs.append(dict(case=case,block=b,independent_check=audit))
 for n,h in snapshot.items():
  if sha(BASE/n)!=h or sha(frozen/n)!=h:raise ValueError('source changed during calibration')
 write(directory/'fixtures.json',dict(fixtures=outputs,supplied_calibration=True,discovery=False,solver_scores=False,global_bound_proved=False,RH_proved=False))
 write(directory/'verification.json',dict(all_passed=True,fixtures_checked=6,tests_passed=10,complete_complements_and_multiplicities=True,input_sha256={n:sha(directory/n)for n in ['protocol.json','source_seal.json','seal.json','tests.json','fixtures.json']},producer_arithmetic_imported_by_checker=False,supplied_calibration=True,discovery=False,global_bound_proved=False,RH_proved=False))
 return directory
if __name__=='__main__':print(run(sys.argv[1]))
