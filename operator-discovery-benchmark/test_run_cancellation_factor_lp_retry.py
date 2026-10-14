import unittest
from unittest.mock import patch
import run_cancellation_factor_lp_retry as R

class RetryTests(unittest.TestCase):
    def test_same_subcone_and_missing_preserved(self):
        instance={'target':'mu','horizon':1,'lhs':[],'square_groups':[],'relation_groups':[]}
        failure={'status':'missing_resource','reason':'test cap','global_bound_proved':False}
        with patch.object(R.P,'build',return_value={'instance':instance,'factor_archive':[]}),patch.object(R.P,'constraints',return_value=[]),patch.object(R.S,'synthesize',return_value=failure)as solve:
            a=R.train({'constraint':'none'},[1],{'time_limit':180})
        self.assertEqual(a['synthesis'],failure)
        self.assertTrue(a['grams_fixed_zero'])
        self.assertNotIn('gram_blocks',solve.call_args.kwargs)
        self.assertEqual(solve.call_args.kwargs['time_limit'],180)
        self.assertEqual(R.transfer(a,[7,11],{})['observations'],[])
    def test_reject_false_admission(self):
        instance={'target':'mu','horizon':1,'lhs':[],'square_groups':[],'relation_groups':[]}
        with patch.object(R.P,'build',return_value={'instance':instance,'factor_archive':[]}),patch.object(R.P,'constraints',return_value=[]),patch.object(R.S,'synthesize',return_value={'status':'finite_certificate','weights':{'square_weights':[],'relation_weights':[]},'certificates':[],'constant_slacks':[]}):
            a=R.train({'constraint':'none'},[1],{})
        self.assertEqual(a['synthesis']['status'],'no_certificate_found')
        self.assertIn('certificate count',a['synthesis']['reason'])
    def test_parent_inputs_exclude_live_dual(self):
        names=R.inputs('parent/factor-probe-001')
        self.assertIn('training.json',names)
        self.assertNotIn('dual.json',names)
        self.assertIn('supplied_embedding_audit',names)

if __name__=='__main__':unittest.main()
