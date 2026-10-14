import copy
import unittest
from unittest.mock import patch
import cancellation_anchored_storage as A
import cancellation_anchored_storage_dual as D
import cancellation_anchored_storage_synthesis as S
import check_anchored_storage_search as I


class Search(unittest.TestCase):
    def fixture(self, primal=False):
        inst=dict(target='mu',horizon=1,lhs=[dict(m=[1,1],c='-1')],square_groups=[],relation_groups=[])
        atoms=[[dict(m=[1],c='1')]]+[[] for _ in range(13)]
        blocks=[dict(full_child=[] if primal else [atoms],full_parent=[atoms] if primal else [])]
        storage=[A.storage_transport(row) for row in blocks]
        return [inst],blocks,storage,A.gram_specs()

    def test_complete_dual_and_reduced_equations(self):
        instances,blocks,storage,specs=self.fixture()
        result=D.propose(instances,blocks,storage,gram_specs=specs,max_rows=2500,time_limit=180)
        self.assertEqual(result['status'],'exact_separator')
        checkpoint=result['proposal_checkpoint']
        self.assertTrue(I.verify_dual_checkpoint(checkpoint,instances,blocks,storage,specs)['verified'])
        self.assertTrue(I.verify_compressed_dual(instances,blocks,storage,specs,result)['verified'])
        self.assertEqual(len(result['storage_cross_redundancy']),91)
        for key,value in [('storage_block_hashes',['bad']),('row_order_hash','bad'),
                          ('support',[999999]),('restricted_column_indices',[]),
                          ('compilation_work_reserve',0)]:
            bad=copy.deepcopy(checkpoint);bad[key]=value
            with self.assertRaises(ValueError):
                I.verify_dual_checkpoint(bad,instances,blocks,storage,specs)
        bad=copy.deepcopy(result);bad['diagnostics']['row_compression']['total_work_proxy']+=1
        with self.assertRaises(ValueError):
            I.verify_compressed_dual(instances,blocks,storage,specs,bad)

    def test_primal_checkpoint_and_nonzero_storage(self):
        instances,blocks,storage,specs=self.fixture(primal=True)
        result=S.synthesize(instances,blocks,storage,gram_specs=specs,
                            max_exact_cells=4000000,row_normalization=True,time_limit=180)
        self.assertEqual(result['status'],'finite_PSD_certificate')
        self.assertTrue(I.verify_primal_checkpoint(result['proposal_checkpoint'],instances,blocks,storage,specs)['verified'])
        self.assertNotEqual(result['grams']['storage_K'][0][0],'0')
        bad=copy.deepcopy(result['proposal_checkpoint']);bad['storage_block_hashes']=['wrong']
        with self.assertRaises(ValueError):I.verify_primal_checkpoint(bad,instances,blocks,storage,specs)

    def test_stage_decisions(self):
        self.assertEqual(I.expected_plan('exact_separator'),[])
        self.assertEqual(I.expected_plan('uncertified'),[dict(phase='primal',program=I.PROGRAM)])
        self.assertEqual([r['X'] for r in I.expected_plan('missing_resource','finite_PSD_certificate')],[8,13])

    def test_cumulative_correction_receipts(self):
        instances,blocks,storage,specs=self.fixture(primal=True)
        original=S.N.exact_support_solution;calls=[]
        def first_face_unavailable(*args,**kwargs):
            value=original(*args,**kwargs);calls.append(True)
            return None if len(calls)==1 else value
        with patch.object(S.N,'exact_support_solution',side_effect=first_face_unavailable):
            result=S.synthesize(instances,blocks,storage,gram_specs=specs,
                                max_exact_cells=4000000,row_normalization=True,time_limit=180)
        self.assertEqual(result['status'],'finite_PSD_certificate')
        checkpoint=result['proposal_checkpoint']
        checked=I.verify_primal_checkpoint(checkpoint,instances,blocks,storage,specs)
        self.assertEqual(checked['work_receipts']['compression_receipts_replayed'],2)
        self.assertEqual(result['diagnostics']['total_charged_work_proxy'],checked['work_receipts']['cumulative_charged_proxy'])
        bad=copy.deepcopy(checkpoint);bad['native_attempt_receipts'][0]['charge_after']+=1
        with self.assertRaises(ValueError):I.verify_primal_checkpoint(bad,instances,blocks,storage,specs)

    def test_actual_resource_policy(self):
        execution=dict(cost=dict(workers=1,requested_workers=1,worker_memory_bytes=6*1024**3,
            memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,
            numerical_threads_per_worker=1,serial_fallback=False),results=[dict(index=0,status='available')])
        self.assertTrue(I.verify_runtime(execution,1))
        execution['cost']['worker_memory_limit_enforced']=False
        with self.assertRaises(ValueError):I.verify_runtime(execution,1)

    def test_frozen_contract_matches_runner(self):
        import run_anchored_storage_search as R
        for key in ['PROGRAM','LIMITS','SOLVER_LIMITS','DUAL_LIMITS','PARALLEL','TESTS']:
            self.assertEqual(getattr(I,key),getattr(R,key))
        self.assertEqual(set(I.source_names()),set(R.sources()))

    def test_fixed_candidate_includes_storage(self):
        training=dict(status='finite_PSD_certificate',synthesis=dict(weights={'x':'1'},grams={'storage_K':[['1']]}))
        result=dict(status='finite_PSD_certificate',program=I.PROGRAM,scales=[8],refitted=False,synthesis=copy.deepcopy(training['synthesis']))
        self.assertTrue(I.verify_fixed_transfer(training,result))
        result['synthesis']['grams']['storage_K'][0][0]='2'
        with self.assertRaises(ValueError):I.verify_fixed_transfer(training,result)


if __name__=='__main__':
    unittest.main()
