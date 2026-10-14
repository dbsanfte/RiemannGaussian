import copy
import unittest
import cancellation_anchored_storage as A
import cancellation_anchored_storage_dual as D
import run_anchored_storage_leaf_replay as R


def fixture():
    inst=dict(target='mu',horizon=1,lhs=[dict(m=[1,1],c='-1')],square_groups=[],relation_groups=[])
    atoms=[[dict(m=[1],c='1')]]+[[] for _ in range(13)]
    blocks=[dict(full_child=[atoms],full_parent=[])]
    storage=[A.storage_transport(blocks[0])]
    return [inst],blocks,storage,A.gram_specs()


class Replay(unittest.TestCase):
    def test_saved_support_reconstructs_complete_storage_cone(self):
        instances,blocks,storage,specs=fixture()
        original=D.propose(instances,blocks,storage,gram_specs=specs)
        self.assertEqual(original['status'],'exact_separator')
        support=copy.deepcopy(original['saved_support'])
        result=R.replay(instances,blocks,storage,specs,support)
        self.assertEqual(result['status'],'exact_separator')
        self.assertEqual(result['saved_support'],support)
        self.assertEqual(set(result['gram_duals']),set(specs))
        self.assertTrue(result['independent_check']['verified'])
        self.assertFalse(result['RH_proved'])

    def test_resources_unchanged(self):
        self.assertEqual(R.LIMITS['max_work'],450000000)
        self.assertEqual(R.PARALLEL['worker_memory_bytes'],6*1024**3)
        self.assertEqual(R.PARALLEL['memory_budget_bytes'],6*1024**3)
        self.assertEqual(R.PARALLEL['workers'],1)


if __name__=='__main__':unittest.main()
