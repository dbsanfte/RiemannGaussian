import unittest
from unittest.mock import patch
from fractions import Fraction as F
import cancellation_affine_storage as A
import cancellation_affine_storage_synthesis as S
import check_cancellation_affine_storage as I
import grouped_arithmetic_language as L
from test_cancellation_affine_storage_dual import fixture
from test_cancellation_affine_storage import zero_grams


class AffinePrimalTests(unittest.TestCase):
    def test_exact_zero_embedding_and_transformed_signed_target(self):
        instances,blocks,storage=fixture()
        instances[0]['lhs']=L.dump_poly({(1,1):F(-3)})
        grams=zero_grams();grams['storage_K'][1][1]='1'
        weights=dict(square_weights=[],relation_weights=[])
        record=S.instantiate_certificate(instances[0],weights,grams,blocks[0],storage[0])
        self.assertEqual(record['transformed_lhs'],[])
        self.assertEqual(record['storage_proof']['parent_multiplier'],'-4')
        self.assertEqual(L.load_poly(record['storage_proof']['polynomial']),{(1,1):F(-3)})
        out=dict(status='finite_PSD_certificate',grams=grams,weights=weights,gram_specs=A.gram_specs(),
            certificates=[record],constant_slacks=['0'],source_hashes=list(map(S.digest,instances)),
            gram_block_hashes=list(map(S.digest,blocks)),storage_block_hashes=list(map(S.digest,storage)),
            global_bound_proved=False,RH_proved=False)
        self.assertTrue(I.verify_primal(instances,blocks,storage,A.gram_specs(),out)['verified'])
        instances[0]['lhs']=L.dump_poly({(1,1):F(1)})
        grams=zero_grams();grams['full_child'][1][1]='1'
        record=S.instantiate_certificate(instances[0],weights,grams,blocks[0],storage[0])
        self.assertEqual(record['transformed_lhs'],record['original_lhs'])
        self.assertEqual(record['storage_proof']['polynomial'],[])

    def test_synthetic_primal_exact_psd_cumulative_receipts(self):
        instances,blocks,storage=fixture();saved=[]
        instances[0]['lhs']=L.dump_poly({(1,1):F(-3)})
        out=S.synthesize(instances,blocks,storage,time_limit=20,row_normalization=True,on_checkpoint=saved.append)
        self.assertEqual(out['status'],'finite_PSD_certificate',out)
        self.assertTrue(I.verify_primal(instances,blocks,storage,A.gram_specs(),out)['verified'])
        self.assertEqual(out['grams']['storage_K'][1][1],'1')
        self.assertEqual(saved[0]['schema'],'affine-storage-SDP-proposal-v1')
        self.assertFalse(saved[0]['native_attempt_receipts'])
        self.assertTrue(saved[1]['native_attempt_receipts'])
        attempts=out['diagnostics']['native_attempt_receipts']
        self.assertTrue(attempts[-1]['native_returned'])
        self.assertEqual(attempts[-1]['charge_after'],out['diagnostics']['total_charged_work_proxy'])
        self.assertLessEqual(attempts[-1]['charge_after'],450000000)
        out=S.synthesize(instances,blocks,storage,time_limit=20,verification_callback=lambda *args:dict(verified=False))
        self.assertEqual(out['status'],'uncertified');self.assertIn('did not verify',out['reason'])

    def test_native_budget_failure_and_checkpoint_callback(self):
        instances,blocks,storage=fixture();saved=[]
        instances[0]['lhs']=L.dump_poly({(1,1):F(-3)})
        with patch.object(S.N,'exact_support_solution',side_effect=AssertionError('must not reconstruct')):
            out=S.synthesize(instances,blocks,storage,time_limit=20,max_exact_work=1,on_checkpoint=saved.append)
        self.assertEqual(out['status'],'missing_resource')
        self.assertTrue(saved);self.assertIn('failure',out['proposal_checkpoint'])
        self.assertEqual(saved[0]['storage_block_hashes'],list(map(S.digest,storage)))
        def failed(cp):raise OSError('checkpoint unavailable')
        with patch.object(S.N,'exact_support_solution',side_effect=AssertionError('must not reconstruct')):
            out=S.synthesize(instances,blocks,storage,time_limit=20,on_checkpoint=failed)
        self.assertEqual(out['status'],'uncertified');self.assertIn('callback failed',out['reason'])


if __name__=='__main__':unittest.main()
