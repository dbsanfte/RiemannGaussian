"""Fresh subprocess plus three actual spawned workers, tiny geometry only."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

ROOT=Path(__file__).resolve().parent
RECEIPT=ROOT/'mobius_arithmetic_launch_086_development.json'
WRAPPER='run_mobius_arithmetic_bank_retry_086'


class NativeLaunchTests(unittest.TestCase):
    outcomes=[]

    def fresh(self,mode):
        with tempfile.TemporaryDirectory(prefix='mobius086launch_test_') as directory:
            destination=Path(directory)/'result.json'
            command=[sys.executable,'-B',str(ROOT/'audit_mobius_arithmetic_native_launch_086.py'),'--child',mode,str(destination)]
            child=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=120)
            result=json.loads(destination.read_text()) if destination.exists() else {'status':'FAIL','reason':'missing fresh subprocess result'}
            result.update(child_exit_code=child.returncode,stdout=child.stdout,stderr=child.stderr)
            self.outcomes.append(result)
            self.assertEqual(child.returncode,0,result)
            self.assertEqual(result['status'],'PASS',result)
            return result

    def test_full_runner_import_and_three_spawned_workers_real_tiny_MILP(self):
        result=self.fresh(WRAPPER)
        self.assertEqual(result['worker_count'],3)
        self.assertEqual(len({r['pid'] for r in result['workers']}),3)
        self.assertEqual(result['real_MILP_proposals'],12)
        self.assertEqual(result['independent_tiny_lower_admissions'],12)
        self.assertFalse(result['fresh_draw_computed'])
        self.assertTrue(all(not row['unknown_Mobius_values_used'] for row in result['workers']))

    def test_actual_loaded_pool_and_environment_faults_rejected(self):
        result=self.fresh('guard:'+WRAPPER)
        self.assertTrue(result['environment_fault_rejected'])
        self.assertTrue(result['actual_loaded_pool_fault_rejected'])
        self.assertEqual(result['direct_byte_preserved_sources'],703)


if __name__=='__main__':
    started=time.monotonic()
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(NativeLaunchTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    attempt=dict(status='PASS' if result.wasSuccessful() else 'FAIL',tests_run=result.testsRun,
                 elapsed_seconds=time.monotonic()-started,errors=len(result.errors),failures=len(result.failures),
                 full_fresh_subprocess_outcomes=NativeLaunchTests.outcomes,scientific_geometry_evaluated=False,
                 tiny_development_geometry_evaluated=True,fresh_draw_computed=False,
                 frozen_sources_modified=False,old_science_replayed=False)
    receipt=json.loads(RECEIPT.read_text()) if RECEIPT.exists() else dict(schema='native-launch-regression-086-v1',attempts=[])
    receipt['attempts'].append(attempt)
    receipt['status']=attempt['status']
    RECEIPT.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    raise SystemExit(0 if result.wasSuccessful() else 1)
