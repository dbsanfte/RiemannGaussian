"""Scope, cancellation, masking and arithmetic-tail regressions."""
from fractions import Fraction as Q
from math import factorial
import unittest
import flint
from estimate_grammar import inverse_one_prefix
from mellin_kernel_grammar import (real,power,canonical,bank_certificate,mellin_polynomial,
    frontier,theta,primitive_table,response,global_certificate,charged_cost)


class Contracts(unittest.TestCase):
    def setUp(self):flint.ctx.prec=384

    def test_joint_recovery_can_succeed_when_neither_scalar_certificate_does(self):
        Ks=[canonical([[0,0,1],[1,1,1]]),canonical([[0,0,1],[1,1,-1]])]
        self.assertTrue(all(not bank_certificate([K])['all_height_no_common_zero'] for K in Ks))
        cert=bank_certificate(Ks)
        self.assertTrue(cert['all_height_no_common_zero'])
        self.assertEqual(cert['target_polynomial'],[[0,0,'1']])
        self.assertFalse(cert['infinite_height_sampling_used'])

    def test_mask_with_a_common_complex_root_is_not_certified(self):
        # P(v)=v^2-v+1/2 vanishes at (1+i)/2, in the relevant halfplane.
        # (v)_2-2(v)_1+1/2 has the required grammar representation.
        K=canonical([[2,0,1],[1,0,-2],[0,0,Q(1,2)]])
        cert=bank_certificate([K,K])
        self.assertFalse(cert['all_height_no_common_zero'])
        self.assertFalse(cert['counterexample_to_growth_bound'])

    def test_approaching_frontier_has_free_constants_and_no_common_amplitude_gate(self):
        f=frontier(Q(1,2),Q(1,4),Q(1,6),Q(1,3))
        self.assertFalse(f['constant_growth_in_q_restricted'])
        self.assertFalse(f['finite_parameter_grid_suffices'])
        self.assertTrue(f['RH_sufficient_if_uniform_and_bank_recovers'])
        self.assertGreater(theta(f,10**12),real(Q(1,2)))
        self.assertLess(theta(f,10**12),theta(f,2))

    def test_rational_roots_have_no_denominator_ceiling(self):
        f=frontier(Q(1,2),Q(1,4),Q(1,1013))
        self.assertTrue(theta(f,1013).is_finite())
        self.assertTrue(power(flint.arb(2),Q(1,1013))>1)
        self.assertEqual(power(flint.arb(0),Q(1,6)),0)

    def test_complete_tail_agrees_with_a_different_entire_series(self):
        mu=inverse_one_prefix(32);K=canonical([[0,0,1]])
        table=primitive_table(mu,2,2,2,[1])
        complete=flint.arb(response(K,table,[1])['1'])
        flint.ctx.prec=512
        other=sum((real(Q((-1)**j,factorial(j)))/flint.arb(2+2*j).zeta() for j in range(100)),flint.arb(0))
        other+=flint.arb(0,flint.arb(202).zeta()/factorial(100))
        truncated=sum((real(mu[n])*real(Q(1,n*n))*(-real(Q(1,n*n))).exp() for n in range(1,33)),flint.arb(0))
        self.assertTrue(complete.overlaps(other))
        self.assertFalse(complete.overlaps(truncated))
        self.assertTrue(table['infinite_tail_included'])

    def test_tampered_inverse_prefix_is_rejected_before_tail_use(self):
        mu=inverse_one_prefix(32);mu[31]=0
        with self.assertRaises(ValueError):primitive_table(mu,2,2,2,[1])

    def test_no_native_observer_is_not_a_rejection_of_the_frontier(self):
        K=canonical([[0,0,1]]);f=frontier(Q(1,2),Q(1,4),Q(1,6));gc=global_certificate(K,2,2,2,384)
        cost=charged_cost([K],bank_certificate([K]),2,2,2,f,[{'2':'1','3':'1'}],[2,3],[gc],['5/8','16'])
        self.assertEqual(cost['status'],'no_tested_q_inside_this_observers_domain')
        self.assertIsNone(cost['best_log_cost'])
        self.assertTrue(cost['all_height_qualitative_recovery'])


if __name__=='__main__':unittest.main()
