"""Pre-score source/seal and entrypoint tests; no synthesis is run."""
import json,subprocess,sys,tempfile,unittest
from pathlib import Path
BASE=Path(__file__).resolve().parent
class Tests(unittest.TestCase):
 def command(self,*args,opt=False):
  return subprocess.run([sys.executable,*(['-O']if opt else []),str(BASE/'run_joint_gram_search.py'),*args],cwd=BASE,capture_output=True,text=True,timeout=30)
 def test_optimized_runtime_rejected_before_write(self):
  with tempfile.TemporaryDirectory()as td:
   out=Path(td)/'run';r=self.command('freeze',str(out),opt=True)
   self.assertNotEqual(r.returncode,0);self.assertFalse(out.exists());self.assertIn('assertions enabled',r.stderr)
 def test_fresh_seal_contract_no_overwrite_and_tamper(self):
  import check_joint_gram_search as C
  with tempfile.TemporaryDirectory()as td:
   out=Path(td)/'run';r=self.command('freeze',str(out));self.assertEqual(r.returncode,0,r.stderr)
   read=lambda n:json.loads((out/n).read_text())
   self.assertEqual(read('protocol.json')['programs'],C.PROGRAMS)
   self.assertEqual(read('protocol.json')['limits'],C.LIMITS)
   self.assertEqual(read('protocol.json')['solver_limits'],C.SOLVER_LIMITS)
   self.assertEqual(read('protocol.json')['dual_limits'],C.DUAL_LIMITS)
   self.assertEqual(read('protocol.json')['training_scales'],[1,2,3,5]);self.assertFalse(read('protocol.json')['final_refit'])
   self.assertEqual(len(read('protocol.json')['gram_specs']),4)
   self.assertEqual(sorted(read('protocol.json')['gram_specs'].values()),[5]*2+[10]*2)
   self.assertEqual(set(read('source_seal.json')),set(C.source_names()))
   self.assertIn('detector_resource_search.json',read('input.json')['input_sha256'])
   self.assertIn('cancellation-arithmetic-results/publication-005/manifest.json',read('input.json')['input_sha256'])
   self.assertIn('cancellation-arithmetic-results/cell-joint-gram-probe-001/independent_verification.json',read('input.json')['input_sha256'])
   self.assertIn('cancellation-arithmetic-results/divisor-cell-probe-001/jobs/train-001.json',read('input.json')['input_sha256'])
   self.assertFalse((out/'training.json').exists())
   self.assertFalse(any((out/'jobs').iterdir()))
   before=(out/'protocol.json').read_bytes();r=self.command('freeze',str(out));self.assertNotEqual(r.returncode,0);self.assertEqual(before,(out/'protocol.json').read_bytes())
   data=read('protocol.json');data['final_scales']=[9];(out/'protocol.json').write_text(json.dumps(data))
   r=subprocess.run([sys.executable,'-c','import run_joint_gram_search as R;R.validate('+repr(str(out))+')'],cwd=BASE,capture_output=True,text=True,timeout=15)
   self.assertNotEqual(r.returncode,0);self.assertIn('seal changed',r.stderr)
 def checkpoint_fixture(self):
  import cancellation_shared_gram_synthesis as S
  import cancellation_shared_gram_synthesis_v2 as V
  inst=[dict(target='mu',horizon=1,lhs=[dict(m=[1,1],c='1')],square_groups=[],relation_groups=[])]
  blocks=[{'g':[[[dict(m=[],c='1')],[dict(m=[1],c='1')]]]}];specs={'g':2}
  columns,lhs,ms,shape,offset,_,_=S.prepare(inst,blocks,gram_specs=specs)
  cp=V.proposal_checkpoint(inst,blocks,specs,columns,lhs,ms,shape,offset,[0]*len(columns),list(range(offset,len(columns))),{},max_checkpoint_bytes=8388608,row_normalization=True)
  cp['row_order_hash']=S.digest(cp['monomials']);cp['layout_hash']=S.digest(cp['column_layout'])
  cp['reconstruction_limits']=dict(max_exact_work=450000000,max_exact_cells=4000000,max_denominator=1000000,max_coefficient_bits=4096,max_operations=200000000,time_limit=180)
  return cp,inst,blocks,specs
 def test_checkpoint_independent_constant_cross_reconstruction(self):
  import check_joint_gram_search as C
  cp,inst,blocks,specs=self.checkpoint_fixture()
  self.assertTrue(C.verify_checkpoint(cp,inst,blocks,specs)['verified'])
  self.assertIn(dict(instance=0,m=[]),cp['monomials'])
  self.assertIn(dict(instance=0,m=[1]),cp['monomials'])
 def test_checkpoint_rejects_target_layout_vector_mutations(self):
  import copy
  import check_joint_gram_search as C
  cp,inst,blocks,specs=self.checkpoint_fixture()
  for field,value in [('exact_target_hash','0'*64),('float_vector',[float('nan')]*len(cp['float_vector'])),('active_support',[]),('monomials',[])]:
   changed=copy.deepcopy(cp);changed[field]=value
   with self.assertRaises(ValueError):C.verify_checkpoint(changed,inst,blocks,specs)
if __name__=='__main__':unittest.main()
