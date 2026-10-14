import unittest
from fractions import Fraction as Q
from math import isqrt
import convolution_control_analytic as a


class ConvolutionAnalyticTests(unittest.TestCase):
    def test_actual_local_convolution_inverse_and_tau_lift(self):
        for N in (1,2,8,64,256):
            d=a.actual_coefficients(N)
            self.assertEqual(a.convolution(d['mu'],d['lambda']),d['c'])
            self.assertEqual(a.convolution(d['c'],d['h']),[0,1]+[0]*(N-1))
            squares=[0]+[int(isqrt(n)**2==n) for n in range(1,N+1)]
            self.assertEqual(a.convolution(d['c'],d['tau']),squares)
            self.assertEqual(a.convolution(d['h'],squares),d['tau'])
            self.assertTrue(all(abs(d['c'][n])==d['h'][n]<=d['tau'][n] for n in range(1,N+1)))

    def test_sampled_shift_recovery_initial_and_varied_endpoints(self):
        for N in (1,2,3,8,31,64,256):
            r=a.sampled_prefix_certificate(N)
            self.assertEqual(r['S'][1],0)
            for x in range(N+1):
                self.assertEqual(r['T'][x],-2*r['C'][x]+r['T'][x//3])
                self.assertEqual(Q(r['T'][x//3]-r['T'][x],2),r['C'][x])
            for n in range(1,N+1):self.assertEqual(r['S'][n],r['T'][n-1])
            self.assertFalse(r['RH_proved'])

    def test_signed_square_filter_actual_and_unsigned_charge(self):
        for x in (0,1,2,3,16,64,256,1024):
            r=a.square_divisor_certificate(x)
            self.assertEqual(r['signed_filtered_sum'],isqrt(x))
            if x:self.assertGreaterEqual(r['unsigned_charge'],x)
            self.assertFalse(r['ordinary_signed_energy_bound_proved'])
        r=a.square_divisor_certificate(1024)
        self.assertEqual((r['signed_filtered_sum'],r['unsigned_charge']),(32,77648))

    def test_primepower_boxes_and_invalid_sources(self):
        self.assertEqual(a.primepower_box_certificate([])['signed_box_sum'],1)
        r=a.primepower_box_certificate([(2,10),(3,7),(5,2)])
        self.assertEqual(r['signed_box_sum'],-1)
        self.assertEqual(r['unsigned_box_charge'],1575)
        for bad in ([(4,2)],[(2,1),(2,3)],[(3,-1)]):
            with self.assertRaises(ValueError):a.primepower_box_certificate(bad)

    def test_whole_generic_positive_inverse_is_not_actual(self):
        for k in (0,1,4,8,12):
            r=a.powered_two_countermodel(k)
            self.assertEqual(r['prefix_at_X'],Q(4*(-2)**k-1,3))
            self.assertEqual(r['exact_block_energy'],(1<<k)*r['prefix_at_X']**2)
            self.assertTrue(r['complete_inverse_identity'])
            self.assertFalse(r['actual_prime_power_constraint_at_2_satisfied'])
            self.assertFalse(r['all_actual_prime_power_constraints_satisfied'])
            self.assertTrue(r['sampled_at_3_all_zero'])
            c=[1]+[2*(-2)**j for j in range(1,k+1)]
            h=[1]+[2*2**j for j in range(1,k+1)]
            self.assertEqual([sum(c[j]*h[n-j] for j in range(n+1)) for n in range(k+1)],[1]+[0]*k)
        # Mixed +2*floor-half can mask this generic cubic prefix.
        for k in range(1,13):
            C=a.powered_two_countermodel(k)['prefix_at_X']
            half=a.powered_two_countermodel(k-1)['prefix_at_X']
            self.assertEqual(C+2*half,-1)

    def test_diagonal_nonnegativity_and_energy_lower_comparisons(self):
        for X in (1,2,3,4,8,16,32,64):
            r=a.diagonal_potential_certificate(X)
            self.assertEqual(r['R_h'],r['S_h']-r['A_C'])
            self.assertEqual(r['R_diff'],r['S_tau']-r['S_h'])
            self.assertGreaterEqual(r['R_h'],0);self.assertGreaterEqual(r['R_diff'],0)
            for key,value in r['lower_energy_comparisons'].items():
                self.assertGreaterEqual(r['R_h'] if key.startswith('Rh') else r['R_diff'],value)

    def test_full_gram_difference_not_universal_psd(self):
        d=a.actual_coefficients(4)
        # Dh*v=e1-e4, but Dtau*v=e1; tau Gram minus h Gram is negative.
        v=[0,1,-2,-2,1]
        hv=a.convolution(d['h'],v);tv=a.convolution(d['tau'],v)
        self.assertEqual(hv,[0,1,0,0,-1])
        self.assertEqual(tv,[0,1,0,0,0])
        self.assertEqual(sum(z*z for z in tv)-sum(z*z for z in hv),-1)
        actual_h=a.convolution(d['h'],d['c']);actual_tau=a.convolution(d['tau'],d['c'])
        self.assertEqual(sum(z*z for z in actual_tau)-sum(z*z for z in actual_h),1)

    def test_cofinal_bridge_and_boundness_never_claim_premise(self):
        r=a.nonnegative_potential_bridge_certificate()
        self.assertTrue(r['conditional_bridge_valid'])
        self.assertFalse(r['premise_proved']);self.assertFalse(r['RH_proved'])
        self.assertIn('every integer q>=q0',r['innovation_premise'])
        self.assertIn('every dyadic X>=1',r['innovation_premise'])
        for eta in (Q(0),Q(1,6),Q(1,3)):
            r=a.potential_family_audit('diagonal_R_h',eta)
            self.assertEqual(Q(r['upper_power_after_normalization_X2']),1-eta)
            self.assertFalse(r['ordinary_zeta_bridge_from_feature_alone_proved'])
        self.assertEqual(a.potential_family_audit('pure_root_thinning',root_order=2)['upper_power_after_normalization_X2'],'0')


if __name__=='__main__':unittest.main()
