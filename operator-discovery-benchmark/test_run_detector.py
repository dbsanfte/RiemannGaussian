"""Development-only tiny subprocess workflow checks; no frozen runs modified."""
import json,subprocess,sys,tempfile,unittest,hashlib
from pathlib import Path
BASE=Path(__file__).resolve().parent
class Tests(unittest.TestCase):
 def command(self,args):return subprocess.run([sys.executable,'-B',str(BASE/'run_detector.py'),*args],cwd=BASE,capture_output=True,text=True,timeout=90)
 def test_optimized_python_rejected(self):
  r=subprocess.run([sys.executable,'-O',str(BASE/'run_detector.py'),'--help'],cwd=BASE,capture_output=True,text=True,timeout=10)
  self.assertNotEqual(r.returncode,0);self.assertIn('assertions enabled',r.stderr)
 def test_tiny_multicore_seals_and_no_overwrite(self):
  with tempfile.TemporaryDirectory() as temp:
   root=Path(temp);inp=root/'input.json';out=root/'newrun'
   programs=[dict(target='mu',q=6,C=32,claim='critical',constraint='zero_cubic',dictionary_mode='extended',allow_constant_slack=False),dict(target='mu',q=2,C=1,claim='unsigned_calibration',constraint='none',dictionary_mode='extended',allow_constant_slack=True)]
   inp.write_text(json.dumps(dict(programs=programs,training_scales=[1,2],final_scales=[3],limits=dict(time_limit=15))))
   args=['search','--input',str(inp),'--out',str(out),'--workers','2','--worker-memory-mib','1024','--memory-budget-mib','2048','--timeout','60','--time-limit','15']
   r=self.command(args);self.assertEqual(r.returncode,0,r.stderr+r.stdout)
   read=lambda n:json.loads((out/n).read_text())
   self.assertEqual(len(read('training_receipts.json')['results']),2)
   self.assertEqual([v['index'] for v in read('training_receipts.json')['results']],[0,1])
   first=read('jobs/train-0000.json');self.assertIs(first['program']['allow_constant_slack'],False)
   if first.get('synthesis',{}).get('status')=='finite_certificate':self.assertEqual(first['synthesis']['constant_slacks'],[])
   self.assertFalse(read('receipt.json')['refitted']);self.assertTrue(read('receipt.json')['grams_fixed_zero'])
   tamper=subprocess.run([sys.executable,'-B','-c',"import run_detector;run_detector.execute_job("+repr(dict(directory=str(out),phase='final',index=999,candidate_seal_sha256='0'*64))+")"],cwd=BASE,capture_output=True,text=True,timeout=15)
   self.assertEqual(tamper.returncode,0,tamper.stderr)
   rejected=read('jobs/final-0999.json');self.assertEqual(rejected['status'],'rejected');self.assertIn('candidate seal changed',rejected['reason'])
   before=(out/'receipt.json').read_bytes();again=self.command(args);self.assertNotEqual(again.returncode,0);self.assertEqual(before,(out/'receipt.json').read_bytes())
   protocol=out/'protocol.json';data=json.loads(protocol.read_text());data['final_scales']=[4];protocol.write_text(json.dumps(data))
   probe=subprocess.run([sys.executable,'-B','-c','import run_detector;run_detector.validate_sources('+repr(str(out))+')'],cwd=BASE,capture_output=True,text=True,timeout=10)
   self.assertNotEqual(probe.returncode,0);self.assertIn('run seal changed',probe.stderr)
 def test_slack_policy_rejects_missing_and_nonboolean(self):
  with tempfile.TemporaryDirectory() as temp:
   root=Path(temp)
   for value in [None,1,'true']:
    program=dict(target='mu',q=2,C=1,claim='unsigned_calibration',constraint='none',dictionary_mode='extended')
    if value is not None:program['allow_constant_slack']=value
    inp=root/('input'+str(value)+'.json');inp.write_text(json.dumps(dict(programs=[program],training_scales=[1],final_scales=[2])))
    out=root/('out'+str(value));r=self.command(['search','--input',str(inp),'--out',str(out)])
    self.assertNotEqual(r.returncode,0);self.assertIn('explicit boolean slack policy',r.stderr);self.assertFalse(out.exists())
if __name__=='__main__':unittest.main()
