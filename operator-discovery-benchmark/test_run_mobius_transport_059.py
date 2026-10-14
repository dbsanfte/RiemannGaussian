"""Tiny end-to-end source/plan/independent-bound integration only."""
import unittest
from fractions import Fraction as Q

import run_mobius_transport_059 as R
import mobius_transport_search_059 as S
import check_mobius_transport_059 as C

OPERATIONS = 0


class RunnerTests(unittest.TestCase):
    def test_complete_tiny_argument_and_bound_assessment(self):
        global OPERATIONS
        parameters={'alpha':'1/257','gamma':'1','tau':'1/2','primes':[2,5],'p':2,'q':5}
        programs=[{'id':'tiny','policy':{'steps':[S._scan('profile'),S._scan()]},'family':'profile_scan'},
                  {'id':'tiny_shared','policy':{'steps':[{'kind':'kernel_scan',
                   'kernels':S.source_kernel_expressions(2,5),'order':'asc','method':'stack'},S._scan()]},
                   'family':'shared_kernel_scan'}]
        selected=[{'id':p['id']+'_bound','program_id':p['id'],'claim':{'C':'8','beta':'1/2'}} for p in programs]
        result=R.independent_final(parameters,programs,selected,13)
        OPERATIONS+=sum(result['operations'].values())
        self.assertEqual(result['claims'][0]['assessment']['status'],'PASS')
        self.assertFalse(result['claims'][0]['uniform_cost_bound_proved'])
        self.assertTrue(result['plans'][0]['pairs'] or result['plans'][0]['unmatched'])
        self.assertEqual(len(result['source_sign_ablation']),2)
        self.assertTrue(all(r['assessment']['status']=='PASS' for r in result['claims']))
        self.assertTrue(all(r['float_absolute_difference_from_checked_midpoint']<1e-12 for r in result['claims']))
        self.assertLessEqual(Q(result['independent']['signed_sum']['lower']),Q(result['independent']['signed_sum']['upper']))

    def test_generic_dominance_certificate_independent_admission(self):
        global OPERATIONS
        policy={'steps':[S._scan('profile_block',theta='1/257'),S._scan('profile','desc','fifo')]}
        meter=C.Meter()
        result=C.verify_profile_dominance(policy,R.dominance_certificate(policy),meter)
        OPERATIONS+=meter.operations
        self.assertTrue(result['verified'])
        bad={'steps':[S._scan()]}
        before=meter.operations
        with self.assertRaises(ValueError): C.verify_profile_dominance(bad,R.dominance_certificate(bad),meter)
        OPERATIONS+=meter.operations-before


if __name__ == '__main__': unittest.main()
