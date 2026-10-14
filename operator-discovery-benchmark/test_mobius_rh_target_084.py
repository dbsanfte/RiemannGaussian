import copy
import unittest
from fractions import Fraction as Q
import mobius_rh_target_084 as T
from test_mobius_coupled_square_084 import program


def transfer(extended=False):
    return dict(schema='two-dilation-source-inverse-v1',base_divisor=4,ratios=['1/2','4/5'],
                extra=dict(coefficient='3547/8192',divisor=3)if extended else None)


class TargetTests(unittest.TestCase):
    def test_exact_fixed_kernel_conditional_binding_and_scope(self):
        for extended in (False,True):
            p=program(extended);v=T.compile_target(p,transfer(extended))
            self.assertEqual(v['status'],'VERIFIED_CONDITIONAL_RH_TARGET')
            self.assertEqual(v['uniform_induction_factor'],'4')
            self.assertFalse(v['RH_proved']);self.assertFalse(v['finite_exponent_roster_suffices'])
            p['kernel'][0]['weight']='-2'
            with self.assertRaises(ValueError):T.compile_target(p,transfer(extended))

    def test_dilation_inverse_for_unrelated_step_sequence_and_real_floors(self):
        values=[0]+[((n*17)%13)-6 for n in range(1,65)]
        def M(x):return sum(values[:min(64,int(x))+1])
        def G(x):return M(x/8)-M(x/10)-M(x/4)+M(x/5)
        for x in [Q(1),Q(5,2),Q(31,3),Q(29)]:
            total=0;j=0
            while x/2**j>=1:
                y=x/2**j
                while y>=1:total-=G(4*y);y*=Q(4,5)
                j+=1
            self.assertEqual(total,M(x))

    def test_rational_exponents_exact_comparison_and_rejection(self):
        self.assertEqual(T.exponent(7),Q(8,7))
        self.assertTrue(T.exact_power_comparison('256',128,7))
        self.assertFalse(T.exact_power_comparison('257',128,7))
        self.assertTrue(T.exact_power_comparison('-1',2,17,'0'))
        with self.assertRaises(ValueError):T.exponent(0)
        with self.assertRaises(T.P.ResourceLimit):T.exact_power_comparison('3/2',1234567,1000000)
        p=program();p['drift_multiplier']='2'
        with self.assertRaises(ValueError):T.compile_target(p,transfer())


if __name__=='__main__':unittest.main()
