"""Pre-score source/seal and entrypoint tests; no synthesis is run."""
import json,subprocess,sys,tempfile,unittest
from pathlib import Path
BASE=Path(__file__).resolve().parent
class Tests(unittest.TestCase):
 def command(self,*args,opt=False):
  return subprocess.run([sys.executable,*(['-O']if opt else []),str(BASE/'run_cell_gram_search.py'),*args],cwd=BASE,capture_output=True,text=True,timeout=30)
 def test_optimized_runtime_rejected_before_write(self):
  with tempfile.TemporaryDirectory()as td:
   out=Path(td)/'run';r=self.command('freeze',str(out),opt=True)
   self.assertNotEqual(r.returncode,0);self.assertFalse(out.exists());self.assertIn('assertions enabled',r.stderr)
 def test_fresh_seal_contract_no_overwrite_and_tamper(self):
  import check_cell_gram_search as C
  with tempfile.TemporaryDirectory()as td:
   out=Path(td)/'run';r=self.command('freeze',str(out));self.assertEqual(r.returncode,0,r.stderr)
   read=lambda n:json.loads((out/n).read_text())
   self.assertEqual(read('protocol.json')['programs'],C.PROGRAMS)
   self.assertEqual(read('protocol.json')['limits'],C.LIMITS)
   self.assertEqual(read('protocol.json')['solver_limits'],C.SOLVER_LIMITS)
   self.assertEqual(read('protocol.json')['dual_limits'],C.DUAL_LIMITS)
   self.assertEqual(read('protocol.json')['training_scales'],[1,2,3,5]);self.assertFalse(read('protocol.json')['final_refit'])
   self.assertEqual(len(read('protocol.json')['gram_specs']),20)
   self.assertEqual(sorted(read('protocol.json')['gram_specs'].values()),[2]*18+[5]*2)
   self.assertEqual(set(read('source_seal.json')),set(C.source_names()))
   self.assertIn('detector_resource_search.json',read('input.json')['input_sha256'])
   self.assertIn('cancellation-arithmetic-results/publication-004/manifest.json',read('input.json')['input_sha256'])
   self.assertIn('cancellation-arithmetic-results/divisor-cell-gram-probe-001/independent_verification.json',read('input.json')['input_sha256'])
   self.assertFalse((out/'training.json').exists())
   self.assertFalse(any((out/'jobs').iterdir()))
   before=(out/'protocol.json').read_bytes();r=self.command('freeze',str(out));self.assertNotEqual(r.returncode,0);self.assertEqual(before,(out/'protocol.json').read_bytes())
   data=read('protocol.json');data['final_scales']=[9];(out/'protocol.json').write_text(json.dumps(data))
   r=subprocess.run([sys.executable,'-c','import run_cell_gram_search as R;R.validate('+repr(str(out))+')'],cwd=BASE,capture_output=True,text=True,timeout=15)
   self.assertNotEqual(r.returncode,0);self.assertIn('seal changed',r.stderr)
if __name__=='__main__':unittest.main()
