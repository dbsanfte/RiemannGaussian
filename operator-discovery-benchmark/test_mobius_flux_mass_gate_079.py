import unittest
from fractions import Fraction as Q

import mobius_flux_mass_gate_079 as P
import check_mobius_flux_mass_gate_079 as C


class FluxMass(unittest.TestCase):
    def test_prime_flux_mode_binds_folded_mass_and_exponent(self):
        kernel = [{'divisor': 4, 'weight': '-1'}, {'divisor': 5, 'weight': '1'}]
        ray = ['0', '1']+['0']*8
        proposal = P.propose_gate(kernel, [2, 3], '2/7', '129/128', ray)
        self.assertEqual(proposal['certificate']['mass'], '-1/20')
        self.assertEqual(proposal['certificate']['delta'], '1/3')
        self.assertEqual(proposal['certificate']['leading_lower'], '1/120')
        result = C.verify_flux_mass_gate(kernel, [2, 3], '2/7', '129/128', ray, proposal['certificate'])
        self.assertEqual(result['status'], 'VERIFIED_FLUX_MASS_OBSTRUCTION', result)
        self.assertFalse(result['RH_proved'])

    def test_coupled_prime_semiprime_signature_is_not_a_paid_bound(self):
        kernel = [{'divisor': 4, 'weight': '-1'}]
        for slope in ('-2', '-1', '-1/2', '1/2', '1', '2'):
            ray = ['0', '1']+['0']*7+[slope]
            proposal = P.propose_gate(kernel, [2, 3, 5, 7], '3/5', '1', ray)
            self.assertEqual(proposal['status'], 'FLUX_MASS_OBSTRUCTION_PROPOSAL')
            result = C.verify_flux_mass_gate(kernel, [2, 3, 5, 7], '3/5', '1', ray, proposal['certificate'])
            self.assertEqual(result['status'], 'VERIFIED_FLUX_MASS_OBSTRUCTION', result)
        low, high = P.logarithm_bounds(Q(2, 5))
        self.assertLess(high-low, Q(1, 10**40))

    def test_zero_mass_other_bins_and_cutoff_edges_remain_unpaid(self):
        kernel = [{'divisor': 4, 'weight': '-4'}, {'divisor': 5, 'weight': '5'}]
        ray = ['0', '1']+['0']*8
        self.assertEqual(P.propose_gate(kernel, [], '1/2', '1', ray)['status'], 'UNPAID_ZERO_OR_UNRESOLVED_LEADING_MODE')
        ray[8] = '1'
        self.assertEqual(P.propose_gate(kernel, [], '3/5', '1', ray)['status'], 'UNSUPPORTED_OTHER_SIGNED_CHANNELS')
        ray[8], ray[9] = '0', '1'
        self.assertEqual(P.propose_gate(kernel, [], '1/2', '1', ray)['status'], 'OUTSIDE_SEMIPRIME_SIGNATURE_DOMAIN')
        with self.assertRaises(ValueError): P.propose_gate(kernel, [], '3/5', '2', ray)


if __name__ == '__main__': unittest.main()
