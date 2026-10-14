"""Parallel coverage and lossless finite replay on toy arithmetic only."""
from pathlib import Path
import json
import time
import unittest

import centered_mobius_interval_041 as I
import run_centered_mobius_041 as R


class ParallelReplay(unittest.TestCase):
    def test_fork_partition_keeps_every_signed_case_once(self):
        coefficients=I.independent_coefficients(255,'1/3',prime_power=lambda p:'1/2')
        state=I.center_from_coefficients(coefficients,2,'2/3','1/4')
        programs=[dict(id=str(m),m=m,**{'lambda':dict(kind='rational',value='1')},rho='1',delta='1/4',C='1')
                  for m in (2,3)]
        scales={2:[1,4,9,31],3:[1,5,17,32]}
        parallel=R.parallel_audit(state,programs,scales,workers=2)
        direct=I.audit(state,programs,scales)
        self.assertEqual(parallel['rows'],sorted(direct['rows'],key=lambda row:(row['id'],row['X'])))
        self.assertEqual(parallel['cached_base_grams'],8)
        self.assertEqual(len(parallel['workers']),2)
        self.assertTrue(parallel['complete_coverage_verified'])
        self.assertFalse(parallel['uniform_signed_bound_proved'])
        # Exact serialized endpoints, not floats, survive process transport.
        self.assertEqual(json.loads(json.dumps(parallel))['rows'],parallel['rows'])

    def test_fixed_postselection_case_generator_is_complete_and_in_range(self):
        programs=[{'m':2},{'m':7}]
        spec=R.final_scales(programs,1048575)
        for m,scales in spec['scales_by_m'].items():
            self.assertEqual(len(scales),21)
            self.assertEqual(scales,sorted(set(scales)))
            self.assertTrue(all(2*m*X-1<=1048575 for X in scales))
            self.assertTrue(all(X>65536 for X in spec['irregular_scales_by_m'][m]))
        self.assertEqual(spec,R.final_scales(programs,1048575))


if __name__=='__main__':
    start=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(ParallelReplay))
    row=dict(returncode=0 if result.wasSuccessful() else 1,tests=result.testsRun,
             failures=len(result.failures),errors=len(result.errors),elapsed_seconds=time.monotonic()-start,
             exposure='toy prime parameter1/2, injected center1/4, finite independent Gram cases only')
    path=Path(__file__).with_name('centered_mobius_runner_041_development.json')
    receipt=json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1',invocations=[])
    receipt['invocations'].append(row);path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(row));raise SystemExit(row['returncode'])
