import copy
import unittest
from fractions import Fraction as F
from unittest.mock import patch
import grouped_arithmetic_language as L
import cancellation_affine_storage as A
import cancellation_affine_storage_synthesis as S
import cancellation_affine_storage_dual as D
import check_cancellation_affine_storage as I


def fixture():
    row=[L.dump_poly({():F(1)}),L.dump_poly({(1,):F(1)})]+[[] for _ in range(13)]
    blocks=[dict(full_child=[row],full_parent=[copy.deepcopy(row)])]
    storage=[A.storage_transport(blocks[0])]
    instances=[dict(target='mu',horizon=3,lhs=L.dump_poly({(3,3):F(-1)}),square_groups=[],relation_groups=[])]
    return instances,blocks,storage


class AffineDualTests(unittest.TestCase):
    def test_exact_complete_separator_leaf_receipts_and_callback(self):
        instances,blocks,storage=fixture();saved=[]
        out=D.propose(instances,blocks,storage,time_limit=20,on_checkpoint=saved.append)
        self.assertTrue(out.get('certified'),out)
        self.assertTrue(I.verify_dual(instances,blocks,storage,A.gram_specs(),out)['verified'])
        self.assertEqual(len(out['gram_columns_dot_y']),360)
        self.assertEqual(len(out['storage_cross_redundancy']),105)
        self.assertEqual(saved[0]['schema'],'affine-storage-dual-proposal-v1')
        self.assertEqual(saved[0]['phase'],'prepared_domain')
        self.assertEqual(saved[-1]['phase'],'independent_admission')
        self.assertIsNone(saved[0]['support'])
        self.assertTrue(saved[1]['support'])
        receipt=out['diagnostics']['leaf_elimination']
        self.assertEqual(receipt['status'],'full_original_equality_verified')
        self.assertLessEqual(receipt['total_work_proxy'],450000000)
        self.assertTrue(out['proposal_checkpoint']['native_receipts'])
        self.assertEqual(out['proposal_checkpoint']['native_receipt'],receipt)
        wrong=copy.deepcopy(out);wrong['gram_duals']['storage_K']['matrix'][0][0]='1'
        with self.assertRaises(ValueError):I.verify_dual(instances,blocks,storage,A.gram_specs(),wrong)

    def test_full105_cross_redundancy_and_tamper(self):
        instances,blocks,storage=fixture()
        cols,lhs,ms,shape,offset,_,specs=S.prepare(instances,blocks,storage)
        nn,rr,layout=D.classify(cols,shape,offset,specs)
        reduced,rnn,rrr,keep,proof=D.restricted_columns(cols,offset,nn,rr,layout)
        self.assertEqual(len(cols)-len(reduced),105)
        self.assertEqual(set(rnn+rrr),set(range(len(reduced))))
        self.assertEqual(proof[0]['parent_multiplier'],'-4')
        cols[proof[0]['storage_column']]={(0,1,2):F(1)}
        with self.assertRaises(ValueError):D.restricted_columns(cols,offset,nn,rr,layout)

    def test_failure_retains_intermediate_native_receipt(self):
        instances,blocks,storage=fixture();saved=[]
        def stopped(*args,**kwargs):
            receipt=dict(status='prepared_remaining_system',preprocessing_actual_work=3)
            kwargs['on_checkpoint'](receipt)
            return dict(status='missing_resource',certified=False,reason='forced charged cap',diagnostics={'leaf_elimination':receipt})
        with patch.object(D.N,'reconstruct_dual_fixed_support',side_effect=stopped):
            out=D.propose(instances,blocks,storage,time_limit=20,on_checkpoint=saved.append)
        self.assertEqual(out['status'],'missing_resource')
        self.assertEqual(out['proposal_checkpoint']['native_reason'],'forced charged cap')
        self.assertEqual(out['proposal_checkpoint']['native_receipt']['preprocessing_actual_work'],3)
        self.assertTrue(any(item['status']=='prepared_remaining_system' for item in out['proposal_checkpoint']['native_receipts']))

    def test_bad_callbacks_and_limits_prevent_research(self):
        instances,blocks,storage=fixture()
        def failed(checkpoint):raise OSError('checkpoint unavailable')
        with patch.object(D,'support_proposal',side_effect=AssertionError('must not solve')):
            out=D.propose(instances,blocks,storage,on_checkpoint=failed)
            self.assertEqual(out['status'],'uncertified');self.assertIn('callback failed',out['reason'])
            out=D.propose(instances,blocks,storage,max_checkpoint_bytes=1)
            self.assertEqual(out['status'],'missing_resource');self.assertIsNone(out['proposal_checkpoint'])
            out=D.propose(instances,blocks,storage,max_work=450000001)
            self.assertEqual(out['status'],'uncertified');self.assertIn('authorized',out['reason'])
        with patch.object(D,'support_proposal',return_value=(None,dict(solver_status=2))):
            out=D.propose(instances,blocks,storage)
        self.assertEqual(out['status'],'uncertified');self.assertFalse(out['certified'])
        out=D.propose(instances,blocks,storage,time_limit=20,verification_callback=lambda *args:dict(verified=False))
        self.assertEqual(out['status'],'uncertified');self.assertFalse(out['certified'])
        self.assertIn('did not verify',out['reason'])


if __name__=='__main__':unittest.main()
