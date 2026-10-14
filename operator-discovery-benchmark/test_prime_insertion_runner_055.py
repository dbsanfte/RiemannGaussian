from copy import deepcopy
from fractions import Fraction as Q
import unittest
import run_prime_insertion_055 as R
import prime_insertion_search_055 as S

METERS=[]
def meter():
    m=S.Meter();METERS.append(m);return m


class RunnerTests(unittest.TestCase):
    def selected(self):
        return {'id':'synthetic','form':{'id':'form','coefficients':[1,-1],'lambda':'1',
            'support':[0,1],'baseline':False},'delta':'1','C':'1'}

    def test_complete_two_child_coverage_and_unpaid_scope(self):
        row=self.selected()
        entries=[{'id':row['id'],'N':n,'parity':r,'status':'FINITE_PASS'} for n in R.FINAL for r in (0,1)]
        result=R.summarize(row,entries)
        self.assertEqual(result['status'],'OPEN_AFTER_FINITE_DRIFT_TESTS')
        self.assertFalse(result['uniform_target_bound_proved'])
        with self.assertRaises(ValueError):R.summarize(row,entries[:-1])
        entries[0]['status']='FINITE_REFUTATION'
        result=R.summarize(row,entries)
        self.assertEqual(result['status'],'REFUTED_FIXED_DRIFT')
        self.assertFalse(result['RH_refuted'])

    def test_independent_negative_cross_energy_and_exact_boundary_pass(self):
        row=self.selected()
        values=[(Q(1),Q(1)),(Q(2),Q(2))]
        self.assertEqual(R.independent_energy(row['form'],values,2),(Q(1),Q(1)))
        table={2:values,4:values}
        result=R.check_transition(row,2,0,table,table,meter())
        self.assertEqual(result['status'],'FINITE_PASS')
        self.assertEqual(result['checked_drift'],{'lower':'-1/2','upper':'-1/2'})

    def test_strict_new_drift_failure_and_source_containment_guard(self):
        row=self.selected()
        table={2:[(Q(0),Q(0)),(Q(0),Q(0))],
            5:[(Q(5),Q(5)),(Q(0),Q(0))]}
        result=R.check_transition(row,2,1,table,table,meter())
        self.assertEqual(result['status'],'FINITE_REFUTATION')
        bad=deepcopy(table);bad[5][0]=(Q(6),Q(6))
        with self.assertRaises(ValueError):R.check_transition(row,2,1,table,bad,meter())

    def test_parent_split_is_fresh_but_source_channels_can_overlap(self):
        self.assertFalse(set(R.TRAIN)&set(R.FINAL))
        self.assertTrue(set(R.sample_numbers(R.TRAIN))&set(R.sample_numbers(R.FINAL)))
        lo,hi=R.independent_forcing(128,'1/7','3')
        self.assertLessEqual(lo,Q(3,2));self.assertGreaterEqual(hi,Q(3,2))


def tearDownModule():print('SYNTHETIC_WORK operations='+str(sum(m.operations for m in METERS)))


if __name__=='__main__':unittest.main()
