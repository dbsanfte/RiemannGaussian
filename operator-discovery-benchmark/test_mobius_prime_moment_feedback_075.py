import copy
import unittest
from fractions import Fraction as Q

import check_mobius_prime_moment_075 as C
import mobius_prime_moment_feedback_075 as F


class Feedback(unittest.TestCase):
    def test_merged_weights_keep_same_child_cross_terms(self):
        v, t = F.merged_children(100, ['2', '-1', '3'], ['1', '2', '4'], [{7: 3, 8: 1}, {7: 2}], [7])
        self.assertEqual(v, {7: Q(7), 8: Q(2)})
        self.assertEqual(t, {7: Q(11), 8: Q(1)})
        self.assertEqual(F.coherence_price(v, t)['K'], '93/11')
        self.assertFalse(F.coherence_price(v, t)['original_unit_price_proved'])

    def test_unsupported_weight_is_not_an_arithmetic_impossibility(self):
        result = F.coherence_price({3: Q(1)}, {5: Q(1)})
        self.assertEqual(result['unsupported_children'], [3])
        self.assertFalse(result['actual_arithmetic_refuted'])
        self.assertEqual(F.coherence_price({3: Q(0)}, {})['K'], '0')

    def test_pairing_conservation_with_nonzero_anchor(self):
        for v in ({2: Q(3), 5: Q(-1), 9: Q(2)}, {2: Q(-7), 5: Q(2)}, {4: Q(3)}, {2: Q(1), 9: Q(-1)}):
            certificate = F.pairing(v)
            self.assertTrue(F.verify_pairing(20, v, certificate))
            if sum(v.values()):
                bad = copy.deepcopy(certificate)
                bad['anchor_coefficient'] = '0'
                self.assertFalse(F.verify_pairing(20, v, bad))

    def test_count_normalization_recovers_multiplicity_cost(self):
        spec = dict(grid=80, theta=['1/2', '3/4'], multipliers=[])
        record = dict(id='p', shape=['1'])
        for gamma in ('1/2', '17/31', '1', '3/2'):
            control = F.normalized_control(record, spec, gamma, 64)
            self.assertTrue(control['universal_correlation_proved'])
            self.assertIsNone(control['innovation']['inherited_C'])
            self.assertFalse(control['uniform_source_bound_proved'])
            self.assertLess(Q(control['sqrt_rho_upper']), 1)
        # Sixteen identical children of value2: raw B^2/Q=16.
        row = dict(components=[32], counts=[16])
        control = F.normalized_control(record, spec, '1/2', 64)
        lo, hi = F.operator_enclosure(control, row)
        self.assertEqual(lo, hi)
        self.assertEqual(lo*lo, Q(control['beta'][0])*64)
        unpaid = F.normalized_control(record, spec, '1/3', 64)
        self.assertFalse(unpaid['universal_correlation_proved'])
        self.assertIsNone(unpaid['rho_upper'])
        self.assertTrue(unpaid['unpaid_count_price'])

    def test_general_fractional_count_powers_independently(self):
        for gamma in (Q(1, 3), Q(17, 31), Q(101, 97), Q(3, 2)):
            for n in (1, 2, 19, 127):
                actual = F.count_power_bounds(n, gamma, 12)
                independent = C.power_enclosure(n, gamma, 12, C.Meter())
                self.assertEqual(actual, independent)
        spec = dict(grid=80, theta=['1/2', '3/4'], multipliers=[2])
        control = F.normalized_control(dict(id='p', shape=['1', '-1']), spec, '1', 64)
        row = dict(components=[-10, 3], counts=[5, 1])
        a = list(map(Q, control['operator']))
        exact = a[0]*Q(-10, 5)+a[1]*3
        self.assertEqual(F.operator_enclosure(control, row), (exact, exact))

    def test_feedback_changes_generated_operators_and_keeps_open_branch(self):
        spec = dict(grid=80, theta=['1/2', '3/4'], multipliers=[])
        record = dict(id='p', kind='prime_only', shape=['1'], adaptation_correlation=dict(status='REFUTED'))
        result = F.generate_feedback([record], spec)
        self.assertEqual(len(result['controls']), 12)
        self.assertTrue(any(not c['universal_correlation_proved'] for c in result['controls']))
        self.assertFalse(result['next_numerical_search_run'])


if __name__ == '__main__':
    unittest.main()
