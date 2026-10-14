import copy
import unittest
from fractions import Fraction as F
from unittest.mock import patch
import grouped_arithmetic_language as L
import cancellation_anchored_storage as A
import cancellation_anchored_storage_synthesis as S
import cancellation_anchored_storage_dual as D
import check_cancellation_anchored_storage as I

def fixture():
    row=[L.dump_poly({(1,):F(1)})]+[[] for _ in range(13)]
    blocks=[dict(full_child=[row],full_parent=[copy.deepcopy(row)])]
    storage=[A.storage_transport(blocks[0])]
    inst=[dict(target='mu',horizon=3,lhs=L.dump_poly({(3,3):F(-1)}),square_groups=[],relation_groups=[])]
    return inst,blocks,storage

class AnchoredDualTests(unittest.TestCase):
    def test_exact_full_cone_separator_and_checkpoints(self):
        inst,blocks,storage=fixture();saved=[]
        r=D.propose(inst,blocks,storage,time_limit=20,on_checkpoint=saved.append)
        self.assertTrue(r.get('certified'),r)
        self.assertTrue(I.verify_dual(inst,blocks,storage,A.gram_specs(),r)['verified'])
        self.assertEqual(saved[0]['phase'],'prepared_domain')
        self.assertIsNone(saved[0]['support'])
        self.assertEqual(saved[-1]['phase'],'independent_admission')
        self.assertEqual(saved[0]['storage_block_hashes'],list(map(S.digest,storage)))
        self.assertEqual(len(r['gram_columns_dot_y']),315)
        self.assertEqual(len(r['storage_cross_redundancy']),91)
        self.assertLessEqual(r['diagnostics']['row_compression']['total_work_proxy'],450000000)
        r['gram_duals']['storage_K']['matrix'][1][1]='1'
        with self.assertRaises(ValueError):I.verify_dual(inst,blocks,storage,A.gram_specs(),r)

    def test_cross_reduction_coefficientwise(self):
        inst,blocks,storage=fixture()
        cols,lhs,ms,shape,offset,_,specs=S.prepare(inst,blocks,storage)
        nn,rr,layout=D.classify(cols,shape,offset,specs)
        reduced,rnn,rrr,keep,proof=D.restricted_columns(cols,offset,nn,rr,layout)
        self.assertEqual(len(cols)-len(reduced),91)
        self.assertEqual(set(rnn+rrr),set(range(len(reduced))))
        pos=proof[0]['storage_column'];cols[pos]={(0,1,2):F(1)}
        with self.assertRaises(ValueError):D.restricted_columns(cols,offset,nn,rr,layout)

    def test_resource_failure_preserves_bounded_checkpoint(self):
        inst,blocks,storage=fixture();saved=[]
        with patch.object(D.N,'reconstruct_dual_fixed_support',return_value=dict(status='missing_resource',certified=False,reason='forced resource cap',diagnostics={})):
            r=D.propose(inst,blocks,storage,time_limit=20,on_checkpoint=saved.append)
        self.assertEqual(r['status'],'missing_resource')
        self.assertEqual(r['proposal_checkpoint']['native_reason'],'forced resource cap')
        self.assertIsNone(saved[0]['support'])
        self.assertTrue(saved[1]['support'])

    def test_checkpoint_callback_and_byte_cap_stop_work(self):
        inst,blocks,storage=fixture()
        def fail(cp):raise OSError('checkpoint unavailable')
        with patch.object(D,'support_proposal',side_effect=AssertionError('must not solve')):
            r=D.propose(inst,blocks,storage,time_limit=20,on_checkpoint=fail)
            self.assertEqual(r['status'],'uncertified')
            self.assertIn('checkpoint callback failed',r['reason'])
            r=D.propose(inst,blocks,storage,time_limit=20,max_checkpoint_bytes=1)
            self.assertEqual(r['status'],'missing_resource')
            self.assertIsNone(r['proposal_checkpoint'])

    def test_no_float_infeasibility_claim_or_overbudget_relaxation(self):
        inst,blocks,storage=fixture()
        with patch.object(D,'support_proposal',return_value=(None,dict(solver_status=2))):
            r=D.propose(inst,blocks,storage,time_limit=20)
        self.assertEqual(r['status'],'uncertified');self.assertFalse(r['certified'])
        r=D.propose(inst,blocks,storage,max_work=450000001)
        self.assertEqual(r['status'],'uncertified');self.assertIn('authorized',r['reason'])

if __name__=='__main__':unittest.main()
