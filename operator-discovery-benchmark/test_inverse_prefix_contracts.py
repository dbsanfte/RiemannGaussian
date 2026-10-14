"""Proof-boundary and exact arithmetic contracts for the new search stage."""
import copy
from fractions import Fraction as Q
from math import comb
import unittest
import inverse_prefix_grammar as g
from check_inverse_prefix_math import inverse, convolution, prime_mu, safe_cutoff, truncated_components
from check_inverse_prefix_analytic import recurrence_certificate, potential_certificate


def calibrated_model():
    table = {str(k): [str((-1) ** (r - 1) * comb(k, r)) for r in range(1, k + 1)] for k in range(1, 4)}
    return {'learned_vectors': {k: v + ['0'] * (int(k) + 2) for k, v in table.items()},
            'coefficient_table': table, 'initial_arity': 1, 'initial_weights': ['1'],
            'selected_recurrence': {'terms': [['r_is_one', '1'], ['same', '1'], ['left', '-1']]}}


class Contracts(unittest.TestCase):
    def test_geometric_inverse_on_unrelated_rationals(self):
        h = [0, 1, Q(1, 2), -2, Q(3, 7), 1, 0, -1, 2]
        a = inverse(h)
        self.assertEqual(convolution(a, h, 8), [0, 1] + [0] * 7)
        self.assertEqual(g.inverse(h), a)

    def test_actual_inverse_and_reconstructed_full_blocks(self):
        h = [0] + [1] * 68
        a = g.inverse(h)
        self.assertEqual(a, prime_mu(68))
        M = g.prefix(a)
        for k in [2, 3, 4, 7]:
            u = safe_cutoff(17, k)
            columns = truncated_components(h, a, u, k, 67)
            weights = [(-1) ** (r - 1) * comb(k, r) for r in range(1, k + 1)]
            self.assertEqual([sum(c * f[n] for c, f in zip(weights, columns)) for n in range(68)], M[:68])

    def test_strict_cutoff_equality_has_actual_counterexample(self):
        h = [0] + [1] * 8; a = prime_mu(8); M = g.prefix(a)
        for k in [2, 3]:
            n = 2 ** k
            f = truncated_components(h, a, 1, k, n)
            predicted = sum((-1) ** (r - 1) * comb(k, r) * f[r - 1][n] for r in range(1, k + 1))
            self.assertEqual(M[n] - predicted, (-1) ** k)

    def test_large_arity_has_no_semantic_cap(self):
        self.assertEqual(g.root_floor(255, 10 ** 100), 1)
        self.assertEqual(g.root_floor(256, 8), 2)
        self.assertEqual(g.root_floor(256, 9), 1)

    def test_full_rational_ceiling_does_not_round_factors_separately(self):
        self.assertEqual(g.ceiling(2, '3/2'), 3)
        self.assertEqual(g.ceiling(4, '3/2'), 8)
        self.assertEqual(g.ceiling(3, '5/2'), 16)

    def test_huge_rational_denominators_and_resource_missingness(self):
        d = 10 ** 100
        self.assertEqual(g.ceiling(3, Q(1, d)), 2)
        self.assertEqual(g.ceiling(3, 1 + Q(1, d)), 4)
        self.assertIsNone(g.ceiling(2, 1000001, bit_budget=32))

    def test_symbolic_recurrence_proves_identity_only(self):
        c = recurrence_certificate(calibrated_model())
        self.assertTrue(c['admitted'])
        self.assertTrue(c['global_reconstruction_proved'])
        self.assertFalse(c['actual_signed_upper_bound_proved'])

    def test_wrong_seed_and_recurrence_are_rejected(self):
        m = calibrated_model(); m['initial_weights'] = ['2']
        self.assertFalse(recurrence_certificate(m)['admitted'])
        m = calibrated_model(); m['selected_recurrence']['terms'][-1][1] = '1'
        self.assertFalse(recurrence_certificate(m)['admitted'])

    def test_unproved_tail_column_and_observed_table_mismatch_rejected(self):
        m = calibrated_model(); m['learned_vectors']['2'][-1] = '1'
        self.assertFalse(recurrence_certificate(m)['admitted'])
        m = calibrated_model(); m['coefficient_table']['3'][1] = '-2'
        self.assertFalse(recurrence_certificate(m)['admitted'])

    def test_nonnegative_potential_is_only_conditional_RH(self):
        p = {'terms': [{'feature': {'arity': 2, 'slot': 1, 'normalizing_power': '3/2'}, 'weight': '1/4'}],
             'fitted_constants': {'3': '1/7'}}
        c = potential_certificate(p)
        self.assertTrue(c['global_potential_nonnegativity_proved'])
        self.assertTrue(c['conditional_cofinal_RH_if_innovation_inequality'])
        self.assertFalse(c['all_scale_actual_premise_proved'])
        self.assertFalse(c['unobserved_level_constants_known'])
        p['terms'][0]['weight'] = '-1/4'
        self.assertFalse(potential_certificate(p)['admitted'])

    def test_cutoff_change_cannot_use_parent_child_moment_as_potential(self):
        model = calibrated_model()
        profile = g.actual_profile([4, 8], [2], model)['rows']
        f = {'arity': 2, 'slot': 1, 'normalizing_power': '1'}
        value = g.potential_value(f, profile, 8)
        parent = next(r for r in profile if r['X'] == 4)
        incorrectly_reused = Q(parent['component_moments'][0]['child_energy'], 8)
        self.assertEqual(value, 4)
        self.assertEqual(incorrectly_reused, 1)

    def test_input_domain_and_unsafe_nonunit_reference_rejected(self):
        with self.assertRaises(ValueError): g.inverse([0, 2, 1])
        with self.assertRaises(ValueError): g.root_floor(4, 0)
        with self.assertRaises(ValueError): g.ceiling(True, '1/2')
        with self.assertRaises(TypeError): inverse([0, 1, 0.5])


if __name__ == '__main__':
    unittest.main()
