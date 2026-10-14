import json
from pathlib import Path
from fractions import Fraction as Q
import unittest

import core_bound_goal_search as P
from prime_bank_candidates import Meter


M = Meter(100000000, 300)


def tearDownModule():
    print(f'core_bound_goal_generator_operations={M.operations}')


class BoundGoalTests(unittest.TestCase):
    def test_symbolic_minimax_general_fractional_kernels(self):
        for theta in ('1/6', '1/2', '2/3', '5/6'):
            for rule in ('ordinary', 'euler_remainder'):
                family = P.synthesize_family(theta, rule, M)
                for rho in (Q(0), Q(theta)/3, Q(theta)*Q(5, 6)):
                    point = P.family_point(family, rho, M)
                    r = Q(point['split']['power'])
                    self.assertEqual(Q(point['C_power']), (1-r)/(1-rho))
                    self.assertLessEqual(r, Q(theta))

    def test_strict_convergence_domain(self):
        family = P.synthesize_family('2/3', 'euler_remainder', M)
        for rho in ('2/3', '3/4', '-1/6'):
            with self.assertRaises(ValueError):
                P.family_point(family, rho, M)

    def test_backward_region_and_complete_weighted_cost(self):
        ordinary = P.admission(P.synthesize_family('2/3', 'ordinary', M), '1/24', 2, '0')
        euler = P.admission(P.synthesize_family('2/3', 'euler_remainder', M), '1/24', 2, '0')
        self.assertEqual([ordinary[k] for k in ('b_coefficient', 'rho_coefficient', 'rhs')], ['1', '10', '2'])
        self.assertEqual([euler[k] for k in ('b_coefficient', 'rho_coefficient', 'rhs')], ['1', '13', '4'])
        reduced = P.substituted_region(euler, 2)
        self.assertEqual(reduced['threshold'], '2/11')
        self.assertTrue(reduced['has_strictly_feasible_exponent'])
        self.assertFalse(P.substituted_region(euler, 4)['has_strictly_feasible_exponent'])
        self.assertFalse(P.substituted_region(ordinary, 2)['has_strictly_feasible_exponent'])

    def test_generic_factor_search_on_changed_moment_map(self):
        result = P.linear_factor_search(['a', 'b', 'delta'], [{'q': '2'}, {'q': '1'}, {'one': '1'}], [1, -2, 0], 2, M)
        selected = result['candidates'][result['selected']]
        self.assertEqual(selected['coefficients'], [1, -2, 0])
        self.assertEqual(selected['harmonic_moment'], {})
        unavailable = P.linear_factor_search(['a', 'b'], [{'q': '2'}, {'q': '1'}], [1, -1], 2, M)
        self.assertIsNone(unavailable['selected'])

    def test_tail_extraction_does_not_supply_a_selected_factor(self):
        expression = [dict(coefficient='3', factors=[]), dict(coefficient='2', factors=['Q', 'a']),
                      dict(coefficient='-1', factors=['b', 'Q'])]
        self.assertEqual(P.extract_tail(expression, 'Q', ['a', 'b', 'delta']), ('3', [2, -1, 0]))
        with self.assertRaises(ValueError):
            P.extract_tail([dict(coefficient='1', factors=['Q', 'Q'])], 'Q', ['delta'])

    def test_quadratic_sign_and_exact_division(self):
        self.assertFalse(P.nonnegative([1, -8, 8], Q(0), Q(1)))
        self.assertTrue(P.nonnegative([1, -2, 1], Q(0), Q(1)))
        self.assertEqual(P.divide([2, -2], [1, -1]), [2])
        with self.assertRaises(ValueError):
            P.divide([1, 1], [1, -1])

    def test_actual_source_generates_open_multi_residual_goals(self):
        parent = json.loads((Path(__file__).parent/'candidate10_split_bound_obligation.json').read_text())
        result = P.search(parent, P.DEFAULT_SPEC, M)
        self.assertEqual(result['statistics']['generated_bound_targets'], 22)
        self.assertEqual(len(result['inherited_bound_obligations']), 144)
        first = result['generated_bound_targets'][0]
        self.assertEqual(first['source_term']['coefficient'], '27/2')
        self.assertEqual(first['auxiliary_identity']['terms'][1]['coefficient'], '2')
        self.assertEqual(first['routes'][0]['current_generic_bound']['energy_N_power'], '2/7')
        self.assertEqual(first['routes'][1]['current_generic_bound']['energy_N_power'], '7/27')
        self.assertEqual([h['energy_N_power'] for h in first['routes'][1]['proved_head_branches']], ['-2/9', '-1/6'])
        self.assertTrue(first['routes'][1]['conditional_auxiliary_route_has_feasible_exponents'])
        self.assertEqual(first['remainder_branches'][2]['mass_bound'],
                         dict(constant='9', U_log_degree=2, t_log_degree=1, t_power='1'))
        self.assertEqual(result['generated_bound_targets'][1]['routes'][0]['current_generic_bound']['status'], 'unlicensed')
        self.assertFalse(result['whole_signed_bound_proved'])
        self.assertFalse(result['RH_proved'])
        core = next(n for n in result['proof_dependencies'] if n['id'] == 'actual_signed_core')
        self.assertIn('complete_signed_complement', core['depends_on'])
        self.assertEqual(result['next_search_tasks'][0]['search_kind'], 'joint_signed_core_control')
        self.assertEqual(result['statistics']['targets_redirected_to_joint_control'], 20)
        self.assertEqual(result['next_search_tasks'][1]['search_kind'], 'search_complete_remainder_bounds')
        self.assertEqual(result['next_search_tasks'][3]['search_kind'], 'search_joint_weighted_remainder_control')
        self.assertTrue(all(t['status'] == 'open' for t in result['generated_bound_targets']))
        for certificate in result['moment_cancellation_certificates']:
            self.assertTrue(certificate['include_d_greater_than_n'])
            self.assertEqual(certificate['zero_moment_degrees'], list(range(certificate['j'])))
        self.assertEqual(result['complete_signed_join']['transport_error']['coefficient'], '-1')

    def test_source_cap_never_discards_higher_factors(self):
        parent = json.loads((Path(__file__).parent/'candidate10_split_bound_obligation.json').read_text())
        with self.assertRaises(ValueError):
            P.search(parent, dict(P.DEFAULT_SPEC, maximum_residual_degree=2), M)


if __name__ == '__main__':
    unittest.main()
