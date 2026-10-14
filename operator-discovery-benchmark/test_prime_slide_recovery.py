"""Exact recovery algebra and adverse scope tests; no source-table experiment."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest

import prime_slide_discovery as P
import prime_slide_recovery as R

METERS=[]
def meter():
    result=P.Meter();METERS.append(result);return result
def tearDownModule():
    print('SYNTHETIC_WORK module=test_prime_slide_recovery operations='+str(sum(m.operations for m in METERS)))


class RecoveryTests(unittest.TestCase):
    def test_every_source_and_power_at_unrelated_exact_parameters(self):
        m=meter();modes=R.raw_modes(6,m)
        for t in (Q(2,7),Q(3,5),Q(4,9)):
            au=[Q(1)]+[t**e-t**(e-1) for e in range(1,7)]
            av=[Q(1)]+[t**(2*e)-t**(2*e-2) for e in range(1,7)]
            sources=([sum(au[j]*av[e-j] for j in range(e+1)) for e in range(7)],au,av)
            for source in sources:
                for e,(a,b) in enumerate(modes):
                    m.charge(20+2*(len(a)+len(b)))
                    value=sum(c*t**d for d,c in a.items())*source[0]+sum(c*t**d for d,c in b.items())*source[1]
                    self.assertEqual(value,source[e])

    def test_two_leg_signed_reduction_reconstructs_every_tensor(self):
        m=meter();engine=P.Engine(m)
        for actions,coefficients in (([(0,0),(2,3),(3,3)],[1,-2,1]),([(0,6),(4,2)],[1,-1])):
            row=P.record(0,'fixture',P.make_same(actions,coefficients),engine)
            reduction=R.reduce_program(row['program'],m)
            self.assertTrue(R.verify_reduction(row,reduction,m))
            bad=deepcopy(reduction);bad[0]['polynomial'][0][1]+=5
            with self.assertRaises(ArithmeticError):R.verify_reduction(row,bad,m)

    def test_prefix_six_recovery_has_unsuppressed_complete_complement(self):
        m=meter();engine=P.Engine(m)
        row=P.record(1,'fixture',P.make_same([(0,e) for e in range(7)],[1]*7),engine)
        result=R.analyse_row(row,m)
        self.assertEqual(result['reduced_basis'],[
            dict(left=0,right=0,polynomial=[[5,1],[6,1],[11,-1]]),
            dict(left=0,right=1,polynomial=[[5,1],[6,1],[7,1],[8,1],[9,1],[10,1]])])
        self.assertEqual(result['least_basis_weight'],'5/3')
        self.assertEqual(result['lifted_constant_tensor'],[-1]*9)
        self.assertEqual(len(result['pullbacks']),6)
        self.assertEqual(result['pullbacks'][0]['right_prefix'],'inside n-prefix, nonsmooth')
        self.assertTrue(all(p['right_prefix']=='outside n-prefix' for p in result['pullbacks'][1:]))
        self.assertFalse(result['original_target_recovered'])

    def test_local_obstruction_does_not_exclude_nonlocal_recovery(self):
        m=meter();engine=P.Engine(m)
        rows=[P.record(e,'fixture',P.make_same([(0,j) for j in range(e+1)],[1]*(e+1)),engine) for e in (5,6)]
        result=R.bounded_local_recovery_obstruction(rows,m)
        self.assertEqual(result['prime_weight'],'4/3');self.assertEqual(result['polynomial_l1_sum'],6)
        self.assertEqual(result['status'],'bounded_local_linear_recovery_excluded')
        self.assertIn('signed integrated cancellation',result['not_excluded'])
        baseline=P.record(0,'fixture',P.make_same([(0,0)],[1]),engine)
        self.assertEqual(R.bounded_local_recovery_obstruction(rows+[baseline],m)['status'],
                         'no_positive_order_obstruction_certified')

    def test_feedback_keeps_target_and_conditional_induction_open(self):
        m=meter();engine=P.Engine(m)
        row=P.record(5,'fixture',P.make_same([(0,e) for e in range(6)],[1]*6),engine)
        analyses=[R.analyse_row(row,m)]
        parent=dict(schema='prime-slide-recovery-obligation-v1',status='open',scope=R.TARGET_SCOPE,
                    equivalence_class='candidate10_complete_prime_bank_covariance',whole_signed_bound_proved=False,RH_proved=False)
        out=R.feedback(parent,analyses,R.bounded_local_recovery_obstruction([row],m),5)
        self.assertEqual(out['scope'],parent['scope'])
        self.assertEqual(out['equivalence_class'],parent['equivalence_class'])
        self.assertFalse(out['conditional_lemma']['closed_induction_proved'])
        self.assertFalse(out['whole_signed_bound_proved']);self.assertFalse(out['RH_proved'])
        with self.assertRaises(ValueError):R.feedback(dict(parent,status='closed'),analyses,{},5)
        with self.assertRaises(ValueError):R.feedback(dict(parent,scope=dict(R.TARGET_SCOPE,source='synthetic')),analyses,{},5)
        with self.assertRaises(ValueError):R.feedback(parent,analyses,{},6)


if __name__=='__main__':unittest.main()
