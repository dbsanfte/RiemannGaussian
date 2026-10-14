import copy
import unittest
import cancellation_anchored_storage_dual as D
import run_anchored_storage_leaf_replay as R
import check_anchored_storage_leaf_replay as I
from test_anchored_storage_leaf_replay import fixture


class ReplayAudit(unittest.TestCase):
    def test_full_equation_backsubstitution_and_cone_admission(self):
        instances,blocks,storage,specs=fixture()
        old=D.propose(instances,blocks,storage,gram_specs=specs)
        support=old['saved_support']
        result=R.replay(instances,blocks,storage,specs,support)
        self.assertTrue(I.verify_leaf_dual(instances,blocks,storage,specs,result,support)['verified'])
        bad=copy.deepcopy(result);bad['exact_support_weights'][0]='-1'
        with self.assertRaises(ValueError):I.verify_leaf_dual(instances,blocks,storage,specs,bad,support)
        bad=copy.deepcopy(result);bad['diagnostics']['leaf_elimination']['total_work_proxy']+=1
        with self.assertRaises(ValueError):I.verify_leaf_dual(instances,blocks,storage,specs,bad,support)
        bad=copy.deepcopy(result);bad['storage_block_hashes']=['wrong']
        with self.assertRaises(ValueError):I.verify_leaf_dual(instances,blocks,storage,specs,bad,support)

    def test_frozen_protocol_contract(self):
        for key in ['LIMITS','PREPARE_LIMITS','PARALLEL']:
            self.assertEqual(getattr(R,key),getattr(I,key))
        self.assertEqual(R.sources(),I.source_names())


if __name__=='__main__':unittest.main()
