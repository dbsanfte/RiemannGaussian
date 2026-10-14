"""Pre-probe integrity/resource/missing-domain checks on toy diagnostics."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
import check_complete_gram_probe_run_v2 as C
import run_complete_gram_moment_probe_v2 as R


def toy(missing=False):
 x=[dict(m=[1],c='1')];z=[dict(m=[2],c='1')];atoms=[x,z]+[[]]*12
 blocks=[{k:[copy.deepcopy(atoms)]for k in C.B.gram_specs()}]
 dual=dict(monomials=[dict(instance=0,m=m)for m in [[],[1,1],[1,2],[2,2]]],weights=['1','1','1','0'])
 if missing:dual['monomials'].pop(2);dual['weights'].pop(2)
 return C.M.moment_probe([dict(horizon=2)],blocks,dual)


class WholeProbe(unittest.TestCase):
 def test_unknown_domain_never_zero_extended(self):
  expected=toy(True);checked=C.verify_probe(copy.deepcopy(expected),expected)
  self.assertEqual(set(checked['region_statuses'].values()),{'unknown_missing_coordinates'})
  modified=copy.deepcopy(expected)
  for row in modified['regions'].values():row.update(status='PSD_extension',missing=[],matrix=[['0']*14 for _ in range(14)])
  with self.assertRaises(ValueError):C.verify_probe(modified,expected)
  expected=toy();self.assertEqual(set(C.verify_probe(expected,expected)['region_statuses'].values()),{'witness_invalid_for_complete_cone'})
  modified=copy.deepcopy(expected);modified['regions']['full_parent']['full_square_polynomial_dot']='0'
  with self.assertRaises(ValueError):C.verify_probe(modified,expected)

 def test_whole_retained_resource_failure_and_artifact_tamper(self):
  with tempfile.TemporaryDirectory()as td:
   d=R.freeze(Path(td)/'probe')
   R.R.write(d/'tests.json',dict(returncode=0,stdout='',stderr='Ran 1 test in 0.001s\n\nOK\n'))
   cost=dict(workers=1,requested_workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False)
   R.R.write(d/'execution.json',dict(cost=cost,results=[dict(index=0,status='missing_resource',reason='toy resource failure')]))
   R.R.write(d/'receipt.json',dict(files_sha256={str(p.relative_to(d)):R.R.sha(p)for p in d.rglob('*.json')},source_count=len(R.R.read(d/'source_seal.json')),**R.FLAGS))
   result=C.audit(d)
   self.assertTrue(result['all_passed']);self.assertFalse(result['independent_full_moment_replay_passed'])
   self.assertEqual(result['process_status'],'missing_resource')
   value=R.R.read(d/'tests.json');value['returncode']=1;(d/'tests.json').write_text(json.dumps(value))
   with self.assertRaises(ValueError):C.audit(d)

 def test_execution_enforcement_and_no_global_claim(self):
  record=dict(status='missing_resource',reason='toy',cost=dict(elapsed_seconds=0),no_new_float_search=True,**C.FLAGS)
  cost=dict(workers=1,requested_workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False)
  execution=dict(cost=cost,results=[dict(index=0,status='available',value=dict(file='result.json',sha256='a'*64,status=record['status'],cost=record['cost'],**C.FLAGS))])
  self.assertEqual(C.verify_execution(execution,record,'a'*64)['record_status'],'missing_resource')
  for field,value in [('worker_memory_limit_enforced',False),('workers',2)]:
   changed=copy.deepcopy(execution);changed['cost'][field]=value
   with self.assertRaises(ValueError):C.verify_execution(changed,record,'a'*64)
  record['RH_proved']=True
  with self.assertRaises(ValueError):C.verify_execution(execution,record,'a'*64)


if __name__=='__main__':unittest.main()
