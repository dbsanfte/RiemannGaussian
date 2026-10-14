import json
from pathlib import Path
import tempfile
import unittest
import run_primitive_state_solver_trace as R


class TraceRunner(unittest.TestCase):
    def test_parallel_contract_and_source_closure(self):
        self.assertEqual(R.PARALLEL['workers'],2)
        self.assertEqual(R.PARALLEL['workers']*R.PARALLEL['worker_memory_bytes'],R.PARALLEL['memory_budget_bytes'])
        self.assertEqual(R.TRACE_LIMITS['cooperative_seconds'],900)
        self.assertEqual(R.TRACE_LIMITS['max_work'],450000000)
        self.assertIn('primitive_state_solver_trace.py',R.sources())

    def test_bounded_atomic_write(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'r.json';R.bounded_write(p,{'x':1},32)
            self.assertEqual(json.loads(p.read_text()),{'x':1})
            with self.assertRaises(OverflowError):R.bounded_write(p,{'x':'a'*100},32)
            self.assertEqual(json.loads(p.read_text()),{'x':1})
            with self.assertRaises(ValueError):R.bounded_write(p,{'x':float('nan')},100)


if __name__=='__main__':unittest.main()
