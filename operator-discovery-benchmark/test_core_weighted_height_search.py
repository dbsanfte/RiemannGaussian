"""Boundary, changed-parameter and complete-recovery tests owned by root."""
import copy
from fractions import Fraction as Q
import json
from pathlib import Path
import unittest

import core_weighted_height_search as P
from prime_bank_candidates import Meter


METER = Meter(100000000, 600)
ROOT = Path(__file__).resolve().parent


def line(p=2, m=3, theta='2/3', alpha='1/24', sigma='9/20', spec=None):
    return P.line_search(p, m, Q(theta), Q(alpha), Q(sigma),
        P.DEFAULT_SPEC if spec is None else spec, METER)


class WeightedRules(unittest.TestCase):
    def test_length_threshold_and_all_branches(self):
        result = line()
        self.assertEqual([b['j'] for b in result['branches']], [0, 1, 2, 3])
        self.assertEqual([b['height_power'] for b in result['branches']],
                         ['-47/60', '-41/60', '-7/12', '-1/30'])
        for plan in result['plans']:
            kappa, tau = Q(plan['kappa']), Q(plan['tau'])
            self.assertLess(kappa, Q(1, 4))
            self.assertTrue(all(Q(b['length_slack']) >= 0 for b in plan['branches']))
            self.assertGreaterEqual(tau*kappa, 5)
            self.assertTrue(all(Q(b['tail_U_power']) <= 0 for b in plan['branches']))
            self.assertEqual(plan['low_obligation_status'], 'open_actual_Mobius_bound')
            self.assertFalse(plan['generic_complete_component_proved'])

    def test_strict_height_boundary_and_higher_degree(self):
        for result in [line(sigma='4/9'), line(m=4, sigma='49/100')]:
            self.assertIsNone(result['selected_plan'])
            self.assertEqual(result['plans'], [])
            self.assertIn('at_least_one_complete_branch_has_no_strict_height_saving', result['failed_premises'])

    def test_cap_does_not_drop_failed_plans(self):
        result = line(spec={**P.DEFAULT_SPEC, 'maximum_tau': '1'})
        self.assertTrue(result['plans'])
        self.assertIsNone(result['selected_plan'])
        self.assertTrue(all(not c['high_auxiliary_proved'] for c in result['plans']))

    def test_analytic_residue_route_can_pay_with_changed_cutoff(self):
        result = line(alpha='1/100')
        plan = result['plans'][result['selected_plan']]
        self.assertTrue(plan['generic_complete_component_proved'])
        self.assertEqual(plan['generic_low_energy_X_power'], '-9/200')
        self.assertEqual(plan['low_obligation_status'], 'proved_by_generic_fallback')
        # This asserts an analytic-residue route, not ordinary convergence.
        self.assertEqual(1-Q(1, 3), Q(2, 3))

    def test_cell_error_is_a_separate_condition(self):
        result = line(p=16, m=2, theta='2/5', alpha='1/2', sigma='3/8')
        self.assertIsNotNone(result['selected_plan'])
        plan = result['plans'][result['selected_plan']]
        self.assertGreater(Q(plan['integer_error_X_power']), 0)
        self.assertFalse(plan['generic_complete_component_proved'])

    def test_constant_polynomial_and_fractional_parameters(self):
        result = line(p=0, m=2, theta='3/4', alpha='1/60', sigma='2/5',
            spec={**P.DEFAULT_SPEC, 'epsilon_fractions': ['1/3', '1/6']})
        self.assertTrue(result['branches'][0]['coefficient_envelope']['constant_polynomial'])
        self.assertEqual(result['branches'][0]['weight_U_power'], '0')
        self.assertEqual({c['epsilon_fraction'] for c in result['plans']}, {'1/3', '1/6'})

    def test_fractional_channels_preserve_history_cost(self):
        channels = [dict(eta='1/6', polynomial=['0', '1'])]
        hardy, error = P.channel_multipliers(channels, Q(1, 4), Q(2, 3))
        self.assertEqual(hardy, 484)
        self.assertEqual(error, 324)
        with self.assertRaises(ValueError):
            P.channel_multipliers([dict(eta='-1/6', polynomial=['1'])], Q(1, 4), Q(2, 3))

    def test_invalid_contour_and_grammar_rejected(self):
        for sigma in ['0', '1/2', '2/3']:
            with self.assertRaises(ValueError):
                line(sigma=sigma)
        for change in [dict(epsilon_fractions=['0']), dict(epsilon_fractions=['1']),
                       dict(epsilon_fractions=['1/6', '1/6']), dict(maximum_tau='0')]:
            with self.assertRaises(ValueError):
                P.validate_spec({**P.DEFAULT_SPEC, **change})


class HarmonicNullGrammar(unittest.TestCase):
    def test_exact_harmonic_pairs_and_scope(self):
        result = P.harmonic_null_search(P.DEFAULT_SPEC, METER)
        self.assertTrue(result['witnesses'])
        for witness in result['witnesses']:
            x, y, d = Q(witness['x']), Q(witness['y']), witness['dilation']
            self.assertEqual(x+y/d, 0)
            self.assertEqual(max(abs(x), abs(y)), 1)
            self.assertFalse(witness['applies_to_actual_Mobius'])
            self.assertFalse(witness['applies_to_full_signed_core'])

    def test_empty_language_does_not_certify_an_obstruction(self):
        result = P.harmonic_null_search({**P.DEFAULT_SPEC, 'amplitude_max': 1}, METER)
        self.assertEqual(result['witnesses'], [])
        graph = P.dependencies([], result)
        node = next(n for n in graph if n['id'] == 'generic_weight_class_obstruction')
        self.assertEqual(node['status'], 'open')


class CompleteSearch(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import run_core_moment_bound_search as PRIOR
        cls.parent = json.loads((ROOT/'candidate10_moment_bound_obligation.json').read_text())
        cls.context = PRIOR.load_context()
        cls.result = P.search(cls.parent, cls.context, P.DEFAULT_SPEC, METER)

    def test_complete_low_gram_and_unchanged_source(self):
        self.assertEqual(self.result['inherited_bindings'], self.parent['generated_bound_obligations'])
        self.assertEqual(self.result['inherited_complete_source_reduction'], self.parent['complete_source_reduction'])
        self.assertEqual(len(self.result['targets']), len(self.parent['auxiliary_bound_targets']))
        for target in self.result['targets']:
            self.assertFalse(target['new_source_payment'])
            self.assertEqual(target['centering']['unit_J_theta_1'], '1')
            if target['low_obligation'] is None:
                continue
            low = target['low_obligation']
            self.assertEqual(len(low['matrix_entries']), (target['m']+1)**2)
            self.assertEqual(len(target['conditional_recovery_bindings']), len(self.parent['generated_bound_obligations']))
            self.assertFalse(low['diagonal_only_allowed'])
            self.assertFalse(low['unweighted_Gaussian_substitution_allowed'])
        self.assertEqual(self.result['statistics']['new_component_bounds_proved'], 0)
        self.assertFalse(self.result['whole_signed_bound_proved'])

    def test_feedback_is_exact_next_search_input(self):
        fb = P.feedback(self.parent, self.result, 'parent.json', 'search.json')
        self.assertEqual(fb['next_search_tasks'][0]['target_id'], 'actual_signed_core')
        self.assertTrue(any(t['search_kind'] == 'bound_actual_signed_low_Gram' for t in fb['next_search_tasks']))
        self.assertEqual(fb['complete_source_reduction'], self.parent['complete_source_reduction'])
        self.assertEqual(fb['auxiliary_bound_targets'], self.parent['auxiliary_bound_targets'])
        self.assertFalse(fb['RH_proved'])

    def test_missing_channel_and_source_rejected(self):
        target = self.parent['auxiliary_bound_targets'][0]
        bad = copy.deepcopy(self.context)
        bad['channel_programs'].pop()
        with self.assertRaises(ValueError):
            P.target_search(self.parent, bad, target, P.DEFAULT_SPEC, METER)
        bad = dict(self.context, complete_signed_join=dict(collected_terms=[]))
        with self.assertRaises(ValueError):
            P.search(self.parent, bad, P.DEFAULT_SPEC, METER)


def tearDownModule():
    print('operations='+str(METER.operations), flush=True)


if __name__ == '__main__':
    unittest.main()
