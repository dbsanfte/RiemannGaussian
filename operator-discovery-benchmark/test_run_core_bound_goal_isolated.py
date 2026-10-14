from pathlib import Path
import tempfile
import unittest

import run_core_bound_goal_isolated as R


class IsolatedHarnessTests(unittest.TestCase):
    def test_one_owner_cannot_lower_the_other_owner_memory_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'limit_one.py').write_text('import resource,unittest\n'
                'resource.setrlimit(resource.RLIMIT_AS,(64*1024**2,64*1024**2))\n'
                'class Test(unittest.TestCase):\n'
                ' def test_own_limit(self): self.assertEqual(resource.getrlimit(resource.RLIMIT_AS)[0],64*1024**2)\n'
                'def tearDownModule(): print("fixture_operations=7")\n')
            (root/'limit_two.py').write_text('import resource,unittest\n'
                'class Test(unittest.TestCase):\n'
                ' def test_original_limit(self): self.assertEqual(resource.getrlimit(resource.RLIMIT_AS)[0],2*1024**3)\n'
                'def tearDownModule(): print("fixture_operations=11")\n')
            runs = R.run_owned_suites(root, [dict(owner='one', modules=['limit_one']), dict(owner='two', modules=['limit_two'])])
            self.assertEqual([r['returncode'] for r in runs], [0, 0])
            self.assertEqual([r['operations'] for r in runs], [7, 11])
            self.assertEqual([r['owner'] for r in runs], ['one', 'two'])

    def test_retry_counts_failed_work_and_refuses_a_different_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            R.write(root/'terminal_failure.json', dict(error='frozen owned tests failed'))
            R.write(root/'frozen_tests.json', dict(returncode=1, operations=42))
            self.assertEqual(R.prior_failure_cost(root)['total_operations'], 2000042)
            R.write(root/'search.json', dict(status='unexpected completed search'))
            with self.assertRaises(ValueError):
                R.prior_failure_cost(root)


if __name__ == '__main__':
    unittest.main()
