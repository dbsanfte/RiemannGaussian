"""Generic algebra and quantitative proof-rule tests; no arithmetic samples."""
import copy
import unittest
from fractions import Fraction as Q

import core_cutoff_work_search as ALG
import core_work_moment_proof_search as P
from prime_bank_candidates import Meter

METER = Meter(100000000, 300)


class PolynomialArguments(unittest.TestCase):
    def test_coupled_E_substitution_can_discover_an_exact_zero(self):
        identity = {('E',): Q(1), (): Q(-1), ('c', 'z'): Q(-1), ('A', 'z'): Q(1)}
        definition = {(): Q(1), ('c', 'z'): Q(1), ('A', 'z'): Q(-1)}
        self.assertEqual(P.substitute(identity, {'E': definition}, METER), {})
        self.assertTrue(P.polynomial_envelope(identity, Q(1, 2), METER))

    def test_fractional_coefficient_powers_and_all_conjugates(self):
        polynomial = {('A', 'Abar', 'a', 'b', 'bbar', 'c', 'v'): Q(-3)}
        # q^(4/3) * q^-1 * q^-2/3, coefficient 3*2*(3/2)^2.
        expected = {(Q(-1, 3), 0): Q(27, 2)}
        self.assertEqual(P.polynomial_envelope(polynomial, Q(1, 3), METER), expected)

    def test_E_norm_expansion_keeps_the_constant_and_mixed_terms(self):
        value = P.polynomial_envelope({('E', 'Ebar'): Q(1)}, Q(1, 2), METER)
        self.assertEqual(value, {(Q(0), 0): Q(1), (Q(1, 2), 1): Q(8), (Q(1), 2): Q(16)})

    def test_squared_envelope_retains_the_ordered_cross_pairs(self):
        value = {(Q(0), 0): Q(2), (Q(1, 6), 1): Q(3)}
        squared = P.multiply_envelopes(value, value, METER)
        self.assertEqual(squared, {(Q(0), 0): Q(4), (Q(1, 6), 1): Q(12), (Q(1, 3), 2): Q(9)})

    def test_generic_source_exposes_all_presentations_and_both_signs(self):
        transition = ALG.compile_transition(1, 2, True, METER)
        out = P.source_envelopes(transition, Q(1, 2), METER)
        self.assertEqual(list(out['branches']), ['1', '-1'])
        self.assertEqual([r['id'] for r in out['representations']], P.REPRESENTATIONS)
        self.assertNotEqual(out['branches']['1'], out['branches']['-1'])
        self.assertTrue(out['zero_mu_history_and_head_retained'])
        self.assertFalse(out['cached_samples_used'])

    def test_missing_zero_child_head_is_detected_before_bounding(self):
        transition = ALG.compile_transition(1, 2, True, METER)
        transition['child'] = [t for t in transition['child'] if 'D' not in t['monomial']]
        with self.assertRaises(ValueError): P.source_envelopes(transition, Q(1, 2), METER)


class UniformCostRules(unittest.TestCase):
    def test_event_sum_critical_log_and_convergent_range(self):
        self.assertEqual(P.summed_power('-1'), P.envelope(0, 1))
        self.assertEqual(P.summed_power('-7/6'), P.envelope(0))
        self.assertEqual(P.summed_power('-5/6'), P.envelope('1/6'))

    def test_height_compact_head_and_negative_slack(self):
        moment = dict(best=dict(integral_height_power='59/30', epsilon_coefficient='5'))
        out = P.height_bound(moment, '45/2', '1/1000')
        self.assertEqual(out['dyadic_power'], '-17/600')
        self.assertEqual(out['bound'], P.envelope(0))
        self.assertTrue(out['compact_head_retained'])
        self.assertTrue(out['full_height_bound_available'])

    def test_critical_height_keeps_log_or_explicit_epsilon_cost(self):
        critical = dict(best=dict(integral_height_power='2', epsilon_coefficient='0'))
        self.assertEqual(P.height_bound(critical, '9/2', '1/1000')['bound'], P.envelope(0, 1))
        critical['best']['epsilon_coefficient'] = '3'
        self.assertEqual(P.height_bound(critical, '9/2', '1/1000')['bound'], P.envelope('27/2000'))

    def test_positive_height_is_paid_at_common_B_not_each_event_q(self):
        moment = dict(best=dict(integral_height_power='3', epsilon_coefficient='0'))
        height = P.height_bound(moment, '45/2', '1/1000')
        out = P.direct_bound([dict(q_power='-2', zeta_power=0, constant='1')], {0: height}, METER)
        self.assertEqual(out['bound'], P.envelope('45/2'))
        self.assertEqual(out['coefficient_cost_floor'], P.envelope(0))
        self.assertTrue(out['coefficient_floor_is_not_a_bound_on_actual_work'])

    def test_Minkowski_avoids_an_unnecessary_mass_log(self):
        rep = dict(id='generic', envelope=[dict(q_power='-1/2', zeta_power=0, constant='1')],
                   squared_envelope=[dict(q_power='-1', zeta_power=0, constant='1')])
        heights = {0: dict(bound=P.envelope(0))}
        weight = dict(q_power='0')
        cauchy = P.gram_attempt(rep, weight, heights, 'weighted_event_Cauchy', '0', METER)
        minkowski = P.gram_attempt(rep, weight, heights, 'weighted_label_Minkowski', None, METER)
        self.assertEqual(cauchy['bound'], P.envelope(1, 1))
        self.assertEqual(minkowski['bound'], P.envelope(1))

    def test_event_weight_reciprocal_and_general_label_growth_both_paid(self):
        rep = dict(id='generic', envelope=[dict(q_power='1/6', zeta_power=0, constant='1')],
                   squared_envelope=[dict(q_power='1/3', zeta_power=0, constant='1')])
        height = {0: dict(bound=P.envelope('2/3'))}
        out = P.gram_attempt(rep, dict(q_power='1/2'), height, 'weighted_event_Cauchy', '-1/2', METER)
        self.assertEqual(out['event_mass'], P.envelope('3/2'))
        self.assertEqual(out['bound'], P.envelope('7/2'))
        self.assertEqual(out['coefficient_cost_floor'], P.envelope('17/6'))

    def test_fixed_smooth_label_cost_cannot_be_used_for_a_growing_window(self):
        catalogue = P.PREFIX.program_catalogue()
        fixed = P.label_weight(catalogue[1], '3/2')
        growing = P.label_weight(catalogue[7], '3/2')
        self.assertEqual(fixed['q_power'], '0')
        self.assertIn('p=2', fixed['multiplier'])
        self.assertEqual(growing['q_power'], '3/2')
        self.assertFalse(growing['constant_may_depend_on_fixed_prime'])

    def test_reciprocal_log_target_is_not_a_free_boundary_payment(self):
        target = dict(B_power='24/5', log_degree=-1)
        self.assertFalse(P.meets(P.envelope('24/5', 0), target))
        self.assertTrue(P.meets(P.envelope('23/5', 100), target))


class Feedback(unittest.TestCase):
    def test_full_goal_alternatives_and_new_unproved_tasks_are_preserved(self):
        catalogue = P.PREFIX.program_catalogue()
        tasks = [dict(priority=0, target_id='actual_signed_core', status='open'),
                 dict(priority=1, target_id='old_alternative', status='open')]
        parent = dict(next_search_tasks=copy.deepcopy(tasks), complete_source_reduction={'signed': ['full', '-e', 'unit']},
            prefix_projection_search=dict(catalogue=catalogue, selection=dict(selected=[dict(program_id=1)])),
            whole_signed_bound_proved=False, RH_proved=False)
        result = dict(binding=dict(target_id='signed_work'), targets=[dict(program_id=1, gamma='0', requested_bound_proved=False)],
            direct_attempts=[dict(bound=P.envelope('11/2'))], selected_direct=0)
        out = P.feedback(parent, result, 'synthetic-artifact')
        self.assertEqual(out['complete_source_reduction'], parent['complete_source_reduction'])
        self.assertEqual(out['next_search_tasks'][0], tasks[0])
        self.assertEqual(out['next_search_tasks'][2:], tasks[1:])
        self.assertFalse(out['next_search_tasks'][1]['arithmetic_bound_refuted'])
        self.assertFalse(out['whole_signed_bound_proved'])


def tearDownModule():
    print('operations='+str(METER.operations))
