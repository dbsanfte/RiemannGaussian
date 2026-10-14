import copy
import unittest
from fractions import Fraction as F
from unittest.mock import patch
import cancellation_anchored_storage_synthesis as S
import cancellation_anchored_storage as A
import check_cancellation_anchored_storage as I
import grouped_arithmetic_language as L
from test_cancellation_anchored_storage_dual import fixture

class AnchoredPrimalTests(unittest.TestCase):
    def test_K_zero_embeds_original_finite_certificate(self):
        inst,blocks,storage=fixture();inst[0]['lhs']=L.dump_poly({(1,1):F(1)})
        grams={k:[['0']*14 for _ in range(14)] for k in A.gram_specs()}
        grams['full_child'][0][0]='1'
        weights=dict(square_weights=[],relation_weights=[])
        record=S.instantiate_certificate(inst[0],weights,grams,blocks[0],storage[0])
        self.assertEqual(record['original_lhs'],record['transformed_lhs'])
        self.assertEqual(record['storage_proof']['polynomial'],[])
        result=dict(status='finite_PSD_certificate',grams=grams,weights=weights,gram_specs=A.gram_specs(),
            certificates=[record],constant_slacks=['0'],source_hashes=list(map(S.digest,inst)),
            gram_block_hashes=list(map(S.digest,blocks)),storage_block_hashes=list(map(S.digest,storage)),
            global_bound_proved=False,RH_proved=False)
        self.assertTrue(I.verify_primal(inst,blocks,storage,A.gram_specs(),result)['verified'])

    def test_nonzero_storage_exact_transformed_target(self):
        inst,blocks,storage=fixture();saved=[]
        inst[0]['lhs']=L.dump_poly({(1,1):F(-3)})
        r=S.synthesize(inst,blocks,storage,time_limit=20,on_checkpoint=saved.append,row_normalization=True)
        self.assertEqual(r['status'],'finite_PSD_certificate',r)
        self.assertEqual(r['grams']['storage_K'][0][0],'1')
        self.assertEqual(r['certificates'][0]['transformed_lhs'],[])
        self.assertTrue(I.verify_primal(inst,blocks,storage,A.gram_specs(),r)['verified'])
        self.assertFalse(r['certificates'][0]['storage_proof'].get('nonnegative_SOS',False))
        self.assertEqual(saved[0]['reconstruction_attempts'],[])
        self.assertTrue(saved[1]['reconstruction_attempts'])
        self.assertLessEqual(r['diagnostics']['total_charged_work_proxy'],450000000)
        wrong=copy.deepcopy(r);wrong['certificates'][0]['storage_proof']['parent_multiplier']='4'
        with self.assertRaises(ValueError):I.verify_primal(inst,blocks,storage,A.gram_specs(),wrong)
        wrong=copy.deepcopy(r);wrong['certificates'][0]['storage_proof']['kind']='nonnegative_SOS'
        with self.assertRaises(ValueError):I.verify_primal(inst,blocks,storage,A.gram_specs(),wrong)

    def test_budget_gate_checkpoint_precedes_native(self):
        inst,blocks,storage=fixture();inst[0]['lhs']=L.dump_poly({(1,1):F(-3)});saved=[]
        with patch.object(S.N,'exact_support_solution',side_effect=AssertionError('must not run')):
            r=S.synthesize(inst,blocks,storage,time_limit=20,max_exact_work=1,on_checkpoint=saved.append)
        self.assertEqual(r['status'],'missing_resource');self.assertTrue(saved)
        self.assertEqual(saved[0]['storage_block_hashes'],list(map(S.digest,storage)))
        self.assertIn('failure',r['proposal_checkpoint'])

    def test_callback_failure_honest(self):
        inst,blocks,storage=fixture();inst[0]['lhs']=L.dump_poly({(1,1):F(-3)})
        def fail(cp):raise OSError('checkpoint unavailable')
        with patch.object(S.N,'exact_support_solution',side_effect=AssertionError('must not run')):
            r=S.synthesize(inst,blocks,storage,time_limit=20,on_checkpoint=fail)
        self.assertEqual(r['status'],'uncertified');self.assertIn('callback failed',r['reason'])

if __name__=='__main__':unittest.main()
