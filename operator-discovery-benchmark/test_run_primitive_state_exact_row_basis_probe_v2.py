import copy
from fractions import Fraction as F
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import run_primitive_state_exact_row_basis_probe_v2 as H

class V2RunnerTests(unittest.TestCase):
    def test_only_receipt_cap_changed(self):
        changed={k:(H.V1.LIMITS[k],H.LIMITS[k]) for k in H.LIMITS if H.V1.LIMITS[k]!=H.LIMITS[k]}
        self.assertEqual(changed,{'max_receipt_bytes':(8388608,33554432)})
        self.assertEqual(H.PROGRAM,H.V1.PROGRAM);self.assertEqual(H.PARALLEL,H.V1.PARALLEL)
        self.assertEqual(H.TESTS[:len(H.V1.TESTS)],H.V1.TESTS)
        for key,value in [('basis_operations',174999999),('cooperative_seconds',899),('max_receipt_bytes',8388608)]:
            with self.assertRaises(ValueError):H.validate_cap_only_limits(dict(H.LIMITS,**{key:value}))
    def test_pipeline_uses_explicit32mib_and_leaves_v1_globals(self):
        before=copy.deepcopy(H.V1.LIMITS)
        with tempfile.TemporaryDirectory() as d,patch.object(H.V1.P,'build',side_effect=AssertionError('no research builds')):
            result=H.process_equations([{'a':F(1)},{'a':F(-1)}],{'a':F(2)},['a'],[0],{1:{0:F(-1)}},
                directory=d,deadline=time.monotonic()+10,compilation_work_reserve=1)
            self.assertEqual(result['status'],'basis_verified')
            for name in ['projection','basis']:
                receipt=json.loads((Path(d)/(name+'.json')).read_text())
                self.assertEqual(receipt['limits']['max_receipt_bytes'],33554432)
            self.assertTrue(all(result[k]is False for k in H.FLAGS))
        self.assertEqual(H.V1.LIMITS,before)
    def test_forwarder_does_not_select_another_algorithm(self):
        sentinel=object()
        with patch.object(H.V1,'process_equations',return_value=sentinel) as method:
            self.assertIs(H.process_equations('synthetic'),sentinel)
            self.assertEqual(method.call_args.args,('synthetic',));self.assertEqual(method.call_args.kwargs,{'limits':H.LIMITS})
    def test_protocol_binds_continuation_and_parent(self):
        hashes=dict(seal='1'*64,receipt='2'*64,review='3'*64);p=H.protocol(hashes)
        self.assertEqual(p['parent_publication'],'publication-013');self.assertEqual(p['schema'],'primitive-state-exact-row-basis-probe-v2')
        self.assertEqual(p['continuation']['changed_limits'],{'max_receipt_bytes':{'prior':8388608,'current':33554432}})
        self.assertEqual(p['continuation']['prior_run_review_sha256'],'3'*64)
        self.assertFalse(p['solver_called'])
        with self.assertRaises(ValueError):H.protocol({'seal':'1'*64})
        self.assertIn(H.PRIOR_PATH+'/jobs/basis.json',H.INPUTS);self.assertIn(H.PRIOR_PATH+'/independent_verification.json',H.INPUTS)
    def test_prior_contract_check_reads_hashes_without_recursive_publication(self):
        original=H.bounded_read
        with patch.object(H.R,'read',return_value={'files':{}}):
            H.validate_prior()
        with patch.object(H.R,'read',return_value={'files':{}}),patch.object(H,'bounded_read',return_value={'schema':'changed'}):
            with self.assertRaises(ValueError):H.validate_prior()
        with self.assertRaises(ValueError):H.protocol(dict(seal='g'*64,receipt='2'*64,review='3'*64))
    def test_source_comparison_rejects_changed_source_and_missing_fields(self):
        prior={k:'bound-'+k for k in H.SOURCE_BINDINGS};current=dict(prior)
        self.assertTrue(all(H.compare_original_source(current,prior).values()))
        current['exact_columns_hash']='other'
        with self.assertRaises(ValueError):H.compare_original_source(current,prior)
        del current['exact_columns_hash']
        with self.assertRaises(ValueError):H.compare_original_source(current,prior)
    def test_intrinsic_projection_and_basis_order_comparison(self):
        old={k:'hash-'+k for k in H.PROJECTION_BINDINGS};old.update(retained_indices=[0],recipes=[[1,[[0,'-1']]]])
        new=dict(old,limits={'max_receipt_bytes':33554432})
        basis=dict(source_hash='full',ordering='declared',row_order=[0,1])
        comparison=H.compare_stage_receipts(new,old,basis,basis)
        self.assertTrue(comparison['basis_row_order']);self.assertTrue(all(comparison['projection_intrinsic_hashes'].values()))
        for key in H.PROJECTION_BINDINGS:
            with self.assertRaises(ValueError):H.compare_stage_receipts(dict(new,**{key:'tampered'}),old,basis,basis)
        with self.assertRaises(ValueError):H.compare_stage_receipts(new,old,dict(basis,row_order=[1,0]),basis)
        self.assertFalse(H.compare_stage_receipts(new,old,None,basis)['basis_receipt_available'])
    def test_bounded_continuation_read(self):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'p.json';path.write_text('{"value":1}')
            self.assertEqual(H.bounded_read(path,100),{'value':1})
            with self.assertRaises(OverflowError):H.bounded_read(path,2)
    def test_worker_has_no_receipt_replay_comparison_stage(self):
        self.assertNotIn('compare_stage_receipts',H.worker.__code__.co_names)
        self.assertNotIn('compare_original_source',H.worker.__code__.co_names)
        self.assertNotIn('bounded_read',H.worker.__code__.co_names)
        self.assertEqual(H.protocol(dict(seal='1'*64,receipt='2'*64,review='3'*64))['continuation']['comparison_location'],
            'independent whole-stage audit; worker pipeline unchanged')
    def test_source_closure_includes_both_runner_generations(self):
        names=H.sources()
        self.assertIn('run_primitive_state_exact_row_basis_probe.py',names)
        self.assertIn('run_primitive_state_exact_row_basis_probe_v2.py',names)
        self.assertIn('primitive_state_exact_row_basis.py',names)
        self.assertIn('test_check_primitive_state_exact_row_basis_probe.py',names)

if __name__=='__main__':unittest.main()
