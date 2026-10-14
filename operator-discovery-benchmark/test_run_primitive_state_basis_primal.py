import copy
from fractions import Fraction as F
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import run_primitive_state_basis_primal as H

class RunnerTests(unittest.TestCase):
    def args(self):return ([{'a':F(1)}],{'a':F(2)},['a'],[0,0],0,{'gram':1},[0])
    def test_tiny_direct_native_pipeline_and_conservative_ledger(self):
        with tempfile.TemporaryDirectory() as d:
            result=H.process_primal(*self.args(),directory=d,deadline=time.monotonic()+10,compilation_work_reserve=1)
            self.assertEqual(result['status'],'trace_verified');self.assertFalse(result['numerical_verification_pending'])
            entry=next(e for e in result['ledger']['entries'] if e['stage']=='native_producer')
            self.assertEqual(entry['reserve'],50000000);self.assertEqual(entry['precision'],'allocated_unverified')
            self.assertTrue((Path(d)/'primal-trace.json').exists());self.assertTrue((Path(d)/'primal-check.json').exists())
    def test_interrupted_native_check_preserves_vector_and_pending_reserve(self):
        with tempfile.TemporaryDirectory() as d,patch.object(H.CHECK,'verify_trace',side_effect=TimeoutError('synthetic audit deadline')):
            result=H.process_primal(*self.args(),directory=d,deadline=time.monotonic()+10,compilation_work_reserve=1)
            self.assertEqual(result['status'],'missing_resource');self.assertTrue(result['numerical_verification_pending'])
            trace=json.loads((Path(d)/'primal-trace.json').read_text());self.assertIsNotNone(trace['original_vector'])
            check_entry=next(e for e in result['ledger']['entries'] if e['stage']=='native_checker')
            self.assertEqual(check_entry['reserve'],check_entry['allocation'])
    def evidence(self):
        indices=list(range(779));report=dict(equation_reduction_verified=False,original_variables=1957,original_finite_equations=5641,
            full_optimization_variables_and_cones_unchanged=True,mathematical_cone_and_target_unchanged=True)
        review=dict(equation_reduction_verified=False,all_passed=True)
        progress=dict(phase='basis_verified',status='basis_verified',selected_original_row_indices=indices)
        return report,review,progress
    def test_old_failed_evidence_never_licenses_equations(self):
        args=self.evidence();self.assertEqual(H.validate_evidence(*args),list(range(779)))
        with self.assertRaises(ValueError):H.validate_evidence(dict(args[0],equation_reduction_verified=True),args[1],args[2])
        with self.assertRaises(ValueError):H.validate_evidence(args[0],args[1],dict(args[2],selected_original_row_indices=[True]*779))
    def test_full_worker_lifecycle_to_costmetadata_and_terminalserialization(self):
        from contextlib import ExitStack
        built=dict(instance={},gram_blocks={},storage_blocks={});aux=dict(built);columns=[{} for _ in range(1957)]
        evidence=dict(selected_original_indices=list(range(779)),authorization='requires fresh replay')
        fake_replay=dict(fresh_exact_basis_authorized=True,exact_replay_artifacts={'projection-replay':{},'basis-replay':{}},selected_original_indices=list(range(779)))
        def numerical(*args,**kwargs):
            self.assertIs(kwargs['ledger'].__class__,H.SOURCE.WorkLedger)
            return dict(status='trace_verified',artifacts={},numerical_verification_pending=False,ledger=kwargs['ledger'].snapshot(),**H.FLAGS)
        with tempfile.TemporaryDirectory() as d,ExitStack() as stack:
            (Path(d)/'jobs').mkdir()
            stack.enter_context(patch.object(H,'require_verified_runtime'))
            stack.enter_context(patch.object(H,'validate',return_value=evidence))
            stack.enter_context(patch.object(H.SOURCE.P,'build',return_value=built))
            stack.enter_context(patch.object(H.SOURCE.P,'auxiliary',return_value=aux))
            stack.enter_context(patch.object(H.SOURCE.TRACE,'metadata',return_value={}))
            stack.enter_context(patch.object(H.SOURCE.S,'prepare',return_value=(columns,{},list(range(5641)),(366,613),1597,[],{'full_child':15,'full_parent':15,'storage_K':15})))
            stack.enter_context(patch.object(H.SOURCE.S,'compilation_charge',return_value=1))
            stack.enter_context(patch.object(H,'fresh_basis_replay',return_value=fake_replay))
            stack.enter_context(patch.object(H,'process_primal',side_effect=numerical))
            result=H.worker(dict(directory=d,phase='primal',index=0))
            record=json.loads((Path(d)/'jobs/primal.json').read_text())
            self.assertEqual(result['status'],'trace_verified');self.assertTrue(record['fresh_exact_basis_authorized'])
            self.assertIsInstance(record['cost']['pid'],int);self.assertGreaterEqual(record['cost']['peak_rss_kib'],0)
            self.assertIsInstance(record['cost']['observed_threads_at_completion'],int);self.assertFalse(record['certified'])
    def test_fresh_complete_saved_tapes_replayed_without_elimination(self):
        # A diagonal synthetic full15 source has779 exact independent rows.
        # It uses no arithmetic source builder and no numerical solve.
        columns=[{} for _ in range(1957)];domain=list(range(779))
        for i in range(366):columns[i]={i:F(1)}
        for k in range(413):columns[366+2*k]={366+k:F(1)};columns[367+2*k]={366+k:F(-1)}
        shape=[366,613];specs={'full_child':15,'full_parent':15,'storage_K':15}
        retained,recipes=H.SOURCE.PROJECT.full15_recipes(shape,1597,specs,1957)
        rows,rhs,projection=H.SOURCE.PROJECT.project_equations(columns,{},domain,retained,recipes,
            deadline=time.monotonic()+10,max_operations=50000000,max_receipt_bytes=33554432)
        selected,targets,basis=H.SOURCE.BASIS.reduce_rows(rows,rhs,len(retained),deadline=time.monotonic()+10,
            max_operations=175000000,max_receipt_bytes=33554432)
        with tempfile.TemporaryDirectory() as d:
            base=Path(d);saved=base/H.BASIS_RUN/'jobs';saved.mkdir(parents=True)
            for name,value in [('projection',projection),('basis',basis)]: (saved/(name+'.json')).write_text(json.dumps(value))
            with patch.object(H,'BASE',base),patch.object(H.SOURCE.BASIS,'reduce_rows',side_effect=AssertionError('no elimination rerun')):
                ledger=H.SOURCE.WorkLedger(450000000,1)
                result=H.fresh_basis_replay(columns,{},domain,shape,1597,specs,list(range(779)),directory=base/'newjob',deadline=time.monotonic()+10,ledger=ledger)
                self.assertTrue(result['fresh_exact_basis_authorized'])
                self.assertEqual(set(result['exact_replay_artifacts']),{'projection-replay','basis-replay'})
                entry=next(e for e in ledger.entries if e['stage']=='basis_replay');self.assertEqual(entry['precision'],'independently_verified')
                basis['source_hash']='tampered';(saved/'basis.json').write_text(json.dumps(basis))
                with self.assertRaises(ValueError):H.fresh_basis_replay(columns,{},domain,shape,1597,specs,list(range(779)),directory=base/'badjob',deadline=time.monotonic()+10,ledger=H.SOURCE.WorkLedger(450000000,1))
    def test_resource_contract_and_closure(self):
        self.assertEqual(H.LIMITS['basis_replay_operations'],125000000);self.assertEqual(H.LIMITS['exact_receipt_bytes'],33554432)
        self.assertEqual(H.PARALLEL['workers'],1);self.assertEqual(H.PARALLEL['worker_memory_bytes'],3*1024**3)
        self.assertIn('primitive_state_basis_primal.py',H.sources());self.assertIn(H.BASIS_PATH+'/jobs/progress.json',H.INPUTS)

    def test_real_solver_contract_and_protocol_construction(self):
        import check_primitive_state_basis_primal_run as C
        protocol=H.protocol({'synthetic':'pending fresh replay'})
        C.verify_protocol(protocol)
        self.assertEqual(protocol['solver_contract']['fixed_options']['max_threads'],1)
        self.assertNotIn('time_limit',protocol['solver_contract']['fixed_options'])
        self.assertEqual(set(protocol['solver_contract']['versions']),{'clarabel','scipy','numpy'})

if __name__=='__main__':unittest.main()
