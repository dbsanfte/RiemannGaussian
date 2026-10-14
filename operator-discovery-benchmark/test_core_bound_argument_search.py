"""Exact calibration and proof-choice checks for the new argument grammar."""
import copy
import math
import unittest
from fractions import Fraction as Q
from unittest.mock import patch

import core_bound_argument_search as P
from prime_bank_candidates import Meter

METER = Meter(100000000, 300)


def solve(kind, theta=0, profile='bounded', **kwargs):
    return P.plan(P.goal(kind, theta, profile, **kwargs), METER)


class BoundArgumentTests(unittest.TestCase):
    def test_compiler_exact_period_means_and_variance_for_signed_rational_weights(self):
        for weights, constant in [([Q(1)], Q(0)), ([1, -1, -1, 0, -1], 1),
                                  ([Q(3, 2), Q(-2, 3), Q(5, 7), Q(-9, 4)], Q(2, 7)),
                                  ([0, 2, -3, 5, -7, 11], -3)]:
            compiled = P.compile_sawtooth(weights, METER, constant)
            period = math.lcm(*range(1, len(weights)+1))
            values = [Q(constant)+sum((Q(a)*Q(n % d, d) for d, a in enumerate(weights, 1)), Q(0))
                      for n in range(period)]
            mean = sum(values)/period
            variance = sum((v-mean)**2 for v in values)/period
            self.assertEqual(Q(compiled['mean']), mean)
            self.assertEqual(Q(compiled['variance']), variance)
            METER.charge(20*period*len(weights))

    def test_equal_frequencies_collect_before_magnitudes(self):
        compiled = P.compile_sawtooth([0, 1, 0, -2], METER)
        # K_2=1-2/2=0 although its two inputs are nonzero.
        self.assertNotIn(2, [x['r'] for x in compiled['conductors']])
        self.assertEqual(compiled['conductors'], [{'r': 4, 'K': '-2', 'J2': 12}])

    def test_constant_mode_is_not_erased(self):
        a = P.compile_sawtooth([1, -1, -1], METER, 1)
        b = P.compile_sawtooth([1, -1, -1], METER, 12)
        self.assertEqual(Q(b['mean'])-Q(a['mean']), 11)
        self.assertEqual(a['variance'], b['variance'])
        mu_sum, reciprocal = -1, Q(1)-Q(1, 2)-Q(1, 3)
        self.assertEqual(Q(a['mean']), 1+(mu_sum-reciprocal)/2)

    def test_search_keeps_cutoff_dependence_and_ablates_mobius_axioms(self):
        generic = solve('variance')
        actual = solve('variance', profile='mobius')
        a, b = P.rank(generic)[0], P.rank(actual)[0]
        self.assertEqual((a['exponent'], a['log_degree']), ('1', 0))
        self.assertEqual((a['exponent'], a['log_degree']), (b['exponent'], b['log_degree']))
        self.assertEqual(b['arithmetic_assumptions'], 0)
        self.assertEqual(actual['nodes'][b['selected']]['rule'], 'parseval_keep_cutoff')
        self.assertTrue(any(n['rule'] == 'parseval_inverse' for n in actual['nodes']))
        self.assertFalse(any(n['rule'] == 'parseval_inverse' for n in generic['nodes']))

    def test_removing_a_rule_changes_discovered_proof_and_bound(self):
        g = P.goal('variance')
        result = P.plan(g, METER, enabled=[r for r in P.RULES if r != 'parseval_keep_cutoff'])
        selected = P.rank(result)[0]
        self.assertEqual((selected['exponent'], selected['log_degree']), ('1', 2))
        self.assertEqual(result['nodes'][selected['selected']]['rule'], 'parseval_uniform_cofactor')
        result = P.plan(g, METER, enabled=['bounded_sawtooth', 'mean_from_supremum'])
        selected = P.rank(result)[0]
        self.assertEqual((selected['exponent'], selected['log_degree']), ('2', 0))

    def test_fractional_exponents_change_rule_choice_and_logarithmic_transition(self):
        for theta, expected in [('1/6', ('2/3', 0)), ('1/3', ('1/3', 0)),
                                ('1/2', ('0', 1)), ('2/3', ('0', 0)), ('3/2', ('0', 0))]:
            result = solve('variance', theta)
            chosen = P.rank(result)[0]
            self.assertEqual((chosen['exponent'], chosen['log_degree']), expected)
        result = solve('variance', '1/6')
        selected = P.rank(result)[0]
        self.assertEqual(result['nodes'][selected['selected']]['rule'], 'weighted_Abel')
        result = solve('variance', '1/2')
        selected = P.rank(result)[0]
        self.assertEqual(result['nodes'][selected['selected']]['rule'], 'parseval_uniform_cofactor')

    def test_interval_selection_changes_with_window_and_retains_spacing_cost(self):
        result = solve('interval')
        short, long = P.rank(result, ('1/2', '3'))
        self.assertEqual(result['nodes'][short['selected']]['rule'], 'interval_from_supremum')
        self.assertEqual((short['exponent'], short['log_degree']), ('5/2', 0))
        self.assertEqual(result['nodes'][long['selected']]['rule'], 'finite_dilation_spacing')
        self.assertEqual((long['exponent'], long['log_degree']), ('4', 0))
        bound = result['nodes'][long['selected']]['bound']
        self.assertEqual(bound, [P.envelope(Q(1, 2), 1, 1), P.envelope(1, 3, logs=1)])

    def test_finite_convolution_lift_pays_support_and_mass(self):
        result = solve('interval', support_power='2', l1_power='2')
        node = next(n for n in result['nodes'] if n['rule'] == 'finite_dilation_spacing'
                    and result['nodes'][n['premises'][0]]['rule'] == 'parseval_keep_cutoff')
        self.assertEqual(node['bound'], [P.envelope(Q(1, 2), 5, 1), P.envelope(3, 11, logs=1)])
        self.assertIn('n>=D', node['details']['domain'])
        self.assertIn('Qplus(0)=0', node['details']['short_head'])

    def test_actual_component_generates_useful_auxiliary_and_unpaid_bridge(self):
        g = dict(kind='component_mellin', p=2, m=3, sigma='9/20', theta='2/3',
                 required={'U_power': '12/5'})
        result = P.plan(g, METER)
        self.assertFalse(result['target_proved'])
        self.assertEqual(result['solutions'], [])
        self.assertTrue(any(n['goal']['kind'] == 'interval' for n in result['nodes']))
        self.assertTrue(any(f['goal']['kind'] == 'signed_convolution_mellin_bridge' for f in result['frontier']))

    def test_recovery_retains_dirichlet_powers_mean_and_all_crosses(self):
        r = P.recovery(2, 3)
        self.assertEqual([b['coefficient'] for b in r['branches']], [1, 3, 3, 1])
        self.assertEqual(len(r['all_ordered_cross_terms']), 16)
        self.assertFalse(r['pointwise_power_substitution_allowed'])
        self.assertFalse(r['mean_bound_assumed'])
        self.assertFalse(r['full_component_bound_proved'])

    def test_cycles_unknown_goals_and_resource_failures_do_not_become_proofs(self):
        g = P.goal('variance')
        with patch.object(P, 'expansions', return_value=[('weighted_Abel', [g])]):
            result = P.plan(g, METER)
        self.assertFalse(result['target_proved'])
        self.assertTrue(any(f['reason'] == 'cycle' for f in result['frontier']))
        self.assertFalse(P.plan({'kind': 'unproved_arithmetic_claim'}, METER)['target_proved'])
        with self.assertRaises(ValueError):
            P.plan(g, METER, node_limit=1)
        with self.assertRaises(OverflowError):
            P.plan(g, Meter(0, 60))

    def test_invalid_scopes_cannot_call_arithmetic_provider(self):
        for kwargs in [dict(theta='-1/3'), dict(profile='random'), dict(support_power='-1')]:
            with self.assertRaises(ValueError):
                P.goal('interval', **kwargs)
        with self.assertRaises(ValueError):
            P.goal('variance', support_power=1)
        self.assertFalse(solve('reciprocal')['target_proved'])
        self.assertTrue(solve('reciprocal', profile='mobius')['target_proved'])

    def test_external_goal_dictionary_cannot_bypass_scope_validation(self):
        g = P.goal('interval')
        for field, value in [('support_power', '-2'), ('l1_power', '-1'),
                             ('theta', '-1/2'), ('profile', 'unproved_inverse')]:
            bad = dict(g, **{field: value})
            with self.assertRaises(ValueError):
                P.plan(bad, METER)
        with self.assertRaises(ValueError):
            P.plan(dict(kind='component_mellin', p=2, m=0, sigma='9/20', theta='2/3',
                        required={'U_power': '12/5'}), METER)


def tearDownModule():
    print('operations='+str(METER.operations))


if __name__ == '__main__':
    unittest.main()
