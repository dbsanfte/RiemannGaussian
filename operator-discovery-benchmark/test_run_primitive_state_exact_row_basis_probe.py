from fractions import Fraction as F
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import run_primitive_state_exact_row_basis_probe as H

class RunnerTests(unittest.TestCase):
    def fixture(self):return ([{'a':F(1),'b':F(2)},{'a':F(-1),'b':F(-2)}],{'a':F(3),'b':F(6)},['a','b'],[0],{1:{0:F(-1)}})
    def process(self,path,limits=None):return H.process_equations(*self.fixture(),directory=path,deadline=time.monotonic()+10,compilation_work_reserve=1,limits=limits)
    def test_exact_pipeline_tiny_no_source_build(self):
        with tempfile.TemporaryDirectory() as d,patch.object(H.P,'build',side_effect=AssertionError('research build forbidden')):
            out=self.process(d)
            self.assertEqual(out['status'],'basis_verified');self.assertTrue(out['equation_reduction_verified'])
            self.assertEqual(out['selected_original_row_indices'],[0]);self.assertLess(out['ledger']['total_work_reserve'],450000000)
            self.assertEqual(set(out['artifacts']),{'projection','projection-check','basis','basis-check'})
            self.assertTrue(all(out[k]is False for k in H.FLAGS))
            checkpoint=json.loads((Path(d)/'progress.json').read_text());self.assertEqual(checkpoint['phase'],'basis_verified')
    def test_unknown_projection_keeps_full_allocation(self):
        limits=dict(H.LIMITS,projection_operations=1)
        with tempfile.TemporaryDirectory() as d,patch.object(H.BASIS,'reduce_rows',side_effect=AssertionError('basis gate')):
            out=self.process(d,limits)
            self.assertEqual(out['status'],'unknown');self.assertFalse(out['equation_reduction_verified']);self.assertIsNone(out['selected_original_row_indices'])
            entry=next(e for e in out['ledger']['entries'] if e['stage']=='projection_producer')
            self.assertEqual(entry['reserve'],1);self.assertEqual(entry['precision'],'allocated_unverified')
            self.assertNotIn('basis',out['artifacts'])
    def test_unknown_basis_keeps_full_allocation(self):
        limits=dict(H.LIMITS,basis_operations=1)
        with tempfile.TemporaryDirectory() as d:
            out=self.process(d,limits);self.assertEqual(out['status'],'unknown')
            entry=next(e for e in out['ledger']['entries'] if e['stage']=='basis_producer')
            self.assertEqual(entry['reserve'],1);self.assertEqual(entry['precision'],'allocated_unverified')
            self.assertFalse(out['equation_reduction_verified']);self.assertIsNone(out['selected_original_row_indices'])
    def test_interrupted_projection_check_keeps_allocations_and_receipt(self):
        with tempfile.TemporaryDirectory() as d,patch.object(H.PROJECT_CHECK,'verify_projection',side_effect=TimeoutError('synthetic deadline')):
            out=self.process(d);self.assertEqual(out['status'],'missing_resource');self.assertIn('projection',out['artifacts'])
            entries={e['stage']:e for e in out['ledger']['entries']}
            self.assertEqual(entries['projection_producer']['reserve'],H.LIMITS['projection_operations'])
            self.assertEqual(entries['projection_checker']['reserve'],entries['projection_checker']['allocation'])
            self.assertFalse(out['equation_reduction_verified'])
    def test_bad_checker_gate_cannot_promote(self):
        fake=dict(verified=True,complete=True,projection_authorized=False,audit_operations=1,independent_audit_work_reserve=1)
        with tempfile.TemporaryDirectory() as d,patch.object(H.PROJECT_CHECK,'verify_projection',return_value=fake),patch.object(H.BASIS,'reduce_rows',side_effect=AssertionError('basis gate')):
            out=self.process(d);self.assertEqual(out['status'],'rejected');self.assertFalse(out['equation_reduction_verified'])
    def test_unverified_checker_never_reduces_ledger_reserve(self):
        fake=dict(verified=False,complete=True,projection_authorized=True,audit_operations=1,independent_audit_work_reserve=1)
        with tempfile.TemporaryDirectory() as d,patch.object(H.PROJECT_CHECK,'verify_projection',return_value=fake):
            out=self.process(d);self.assertEqual(out['status'],'rejected')
            entry=next(e for e in out['ledger']['entries'] if e['stage']=='projection_checker')
            self.assertEqual(entry['precision'],'allocated_unverified');self.assertEqual(entry['reserve'],entry['allocation'])
    def test_failed_terminal_checkpoint_revokes_authorization(self):
        original=H.bounded_write
        def write(path,value,cap):
            if Path(path).name=='progress.json' and value.get('phase')=='basis_verified':raise OverflowError('terminal byte cap')
            return original(path,value,cap)
        with tempfile.TemporaryDirectory() as d,patch.object(H,'bounded_write',side_effect=write):
            out=self.process(d);self.assertEqual(out['status'],'missing_resource')
            self.assertFalse(out['equation_reduction_verified']);self.assertIsNone(out['selected_original_row_indices'])
            checkpoint=json.loads((Path(d)/'progress.json').read_text());self.assertFalse(checkpoint['equation_reduction_verified'])
    def test_strict_limits_and_ledger(self):
        for name in H.LIMITS:
            for value in (0,True):
                with self.assertRaises(ValueError):H.validate_limits(dict(H.LIMITS,**{name:value}))
        for limits in (dict(H.LIMITS,max_work=450000001),dict(H.LIMITS,cooperative_seconds=901),dict(H.LIMITS,projection_operations=300000000)):
            with self.assertRaises(ValueError):H.validate_limits(limits)
        ledger=H.WorkLedger(100,1);entry=ledger.allocate('producer',50)
        with self.assertRaises(OverflowError):ledger.allocate('checker',50)
        with self.assertRaises(ValueError):ledger.precise(entry,51,1)
        self.assertEqual(ledger.snapshot()['total_work_reserve'],51)
    def test_deadline_keeps_no_reduction(self):
        with tempfile.TemporaryDirectory() as d:
            out=H.process_equations(*self.fixture(),directory=d,deadline=time.monotonic()-1,compilation_work_reserve=1)
            self.assertEqual(out['status'],'missing_resource');self.assertFalse(out['equation_reduction_verified'])
    def test_artifact_cap(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(OverflowError):H.bounded_write(Path(d)/'x.json',{'x':'a'*100},10)
            self.assertFalse((Path(d)/'x.json').exists())
    def test_static_frozen_geometry_and_no_solver(self):
        self.assertEqual(H.SCALES,[1,2,3,5]);self.assertEqual(H.PROGRAM['q'],6);self.assertEqual(H.PROGRAM['C'],32)
        self.assertEqual(H.PARALLEL['workers'],1);self.assertEqual(H.PARALLEL['memory_budget_bytes'],3*1024**3)
        self.assertIn('test_check_primitive_state_exact_row_basis_probe',H.TESTS)
        self.assertIn('run_primitive_state_solver_trace.py',H.sources())

if __name__=='__main__':unittest.main()
