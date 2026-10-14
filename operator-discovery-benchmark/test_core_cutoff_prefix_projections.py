"""Root-owned tests for prefix recovery, fractional costs and ranking scope."""
import copy
import json
from pathlib import Path
import unittest
from flint import arb, ctx

import core_cutoff_prefix_projections as P
from prime_bank_candidates import Meter

METER = Meter(100000000, 300)
ROOT = Path(__file__).resolve().parent


def samples(N, work=None):
    mu = [0]+[1]*N
    for n in range(2, N+1):
        mu[n] = -sum(mu[d] for d in range(1, n) if n % d == 0)
    return dict(schema='cutoff-work-samples-v1', start=2, end=N, heights=P.HEIGHTS, mu=mu,
        records=[dict(q=q, mu=mu[q], values=[dict(w1='1' if work is None else '0',
            w2=str(0 if work is None else work.get(q, 0)))]+[
                dict(w1='0', w2='0') for _ in P.HEIGHTS[1:]]) for q in range(2, N+1)])


class PrefixGeometry(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192

    def test_cross_scale_insertion_keeps_prime_composite_and_opposite_signs(self):
        case = P.group_case(P.program_catalogue()[0], 4, samples(8), METER)
        self.assertEqual(case['group_sizes'], [[1, 1], [3, 2], [5, 1], [7, 1]])
        self.assertEqual(case['cross_scale_groups'], 1)
        self.assertEqual(case['groups_with_opposite_mu'], 1)
        self.assertEqual(case['prime_composite_groups'], 1)
        self.assertEqual(case['zero_events'], 2)
        self.assertEqual(sum(n for _, n in case['group_sizes'])+case['zero_events'], 7)

    def test_initial_prefix_is_retained_but_not_an_extra_peak_endpoint(self):
        case = P.group_case(P.program_catalogue()[1], 4, samples(8, {3: 7, 5: -7}), METER)
        self.assertEqual(arb(case['initial_grouped_absolute']), 7)
        self.assertEqual(arb(case['grouped_peak_absolute']), 0)
        self.assertEqual(len(case['partial_curve']), 4)
        self.assertTrue(all(arb(x) == 0 for x in case['partial_curve']))
        self.assertEqual(arb(case['ungrouped_absolute']), 14)

    def test_smooth_projection_has_the_complementary_factor_labels(self):
        case = P.group_case(P.program_catalogue()[1], 8, samples(16), METER)
        self.assertEqual([r for r, _ in case['group_sizes']], [1, 2])
        self.assertEqual(case['cross_scale_groups'], 2)
        self.assertEqual(case['prime_composite_groups'], 2)
        self.assertGreater(case['groups_with_opposite_mu'], 0)

    def test_missing_old_prefix_or_squarefree_lie_is_rejected(self):
        data = samples(16)
        data['records'] = data['records'][1:]
        with self.assertRaises(ValueError): P.group_case(P.program_catalogue()[0], 8, data, METER)
        data = samples(16); data['mu'][4] = 1; data['records'][2]['mu'] = 1
        with self.assertRaises(ValueError): P.group_case(P.program_catalogue()[0], 8, data, METER)

    def test_coarsening_and_refinement_have_opposite_cost_directions(self):
        catalogue, data = P.program_catalogue(), samples(32)
        for projection in ('rough', 'smooth'):
            programs = [p for p in catalogue if p['projection'] == projection and p['prime_program'].get('lower') == '0']
            cases = [P.group_case(p, 16, data, METER) for p in programs]
            for first, second in zip(cases, cases[1:]):
                for a, b in zip(first['partial_curve'], second['partial_curve']):
                    self.assertTrue(arb(a) >= arb(b) if projection == 'rough' else arb(a) <= arb(b))


class Ranking(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192
        self.programs = P.program_catalogue()
        ratios = {0: '0.99', 2: '0.90', 4: '0.95'}
        self.cases = [dict(program_id=p['id'], B=B, nontrivial_partition=True,
            grouped_peak_absolute=ratios.get(p['id'], '0.95'), ungrouped_absolute='1')
            for p in self.programs for B in P.DISCOVERY]

    def test_resolves_old_integer_bit_ties_and_preserves_interval_ambiguity(self):
        out = P.select(self.programs, self.cases, METER)
        self.assertEqual(out['selected'][0]['program_id'], 2)
        self.assertEqual(out['undominated_by_lane']['fixed:smooth'], [1, 3, 5])

    def test_worst_block_matters_and_later_evaluation_cannot_reselect(self):
        for c in self.cases:
            if (c['program_id'], c['B']) == (2, 512): c['grouped_peak_absolute'] = '0.999'
        out = P.select(self.programs, self.cases, METER)
        self.assertEqual(out['selected'][0]['program_id'], 4)
        later = [dict(program_id=0, B=1024, nontrivial_partition=True,
                      grouped_peak_absolute='0', ungrouped_absolute='1')]
        self.assertEqual(P.select(self.programs, self.cases+later, METER), out)

    def test_no_missing_zero_or_degenerate_candidate_is_promoted(self):
        self.cases = [c for c in self.cases if (c['program_id'], c['B']) != (0, 64)]
        for c in self.cases:
            if c['program_id'] == 2: c['ungrouped_absolute'] = '0'
            if c['program_id'] == 4: c['nontrivial_partition'] = False
        out = P.select(self.programs, self.cases, METER)
        self.assertNotIn('fixed:rough', [x['lane'] for x in out['selected']])
        self.assertEqual(out['rejected'][:3], [dict(program_id=0, reason='missing_discovery_case'),
            dict(program_id=2, reason='zero_baseline'), dict(program_id=4, reason='degenerate_partition')])


class ProofRecipes(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parent = json.loads((ROOT/'candidate10_cutoff_prime_orbit_obligation.json').read_text())
        cls.binding = P.source_binding(cls.parent, METER)
        cls.proof = P.proof_search(cls.parent, cls.binding, METER)

    def test_local_tail_is_summed_without_a_tiny_q_to_B_ratio(self):
        r = self.proof['common_window']
        self.assertEqual(r['summed_powers']['raw_child_high_tail'], dict(B_power='15/16', log_degree=0))
        self.assertEqual(r['cost_B_power'], '21/10')
        self.assertEqual(r['gap_to_goal'], '3/10')
        self.assertIn('q/(q-1)', r['length_ratio'])
        self.assertFalse(r['whole_signed_bound_proved'])
        self.assertEqual(P.summed_power('-1'), dict(B_power='0', log_degree=1))

    def test_fractional_weights_and_critical_log_are_derived(self):
        routes = self.proof['programs'][0]['gram_auxiliaries']
        expected = ['19/5', '119/30', '62/15', '43/10', '67/15', '24/5', '24/5']
        self.assertEqual([r['sufficient_bound']['B_power'] for r in routes], expected)
        self.assertEqual(routes[5]['sufficient_bound']['log_degree'], -1)
        self.assertTrue(all(r['W_sectors_are_unweighted'] for r in routes))
        self.assertTrue(all(not r['higher_moment_provider_available'] for r in routes))

    def test_fixed_smooth_mass_is_not_assigned_to_a_growing_window(self):
        catalogue = P.program_catalogue()
        self.assertEqual(P.mass_rule(catalogue[1], '0'),
            dict(method='labels_subset_1_and_fixed_prime', B_power='0', log_degree=0, constant='2'))
        self.assertEqual(P.mass_rule(catalogue[7], '0')['B_power'], '1')
        self.assertEqual(P.mass_rule(catalogue[0], '1/2')['B_power'], '1/2')

    def test_all_targets_and_original_recovery_survive_feedback(self):
        selected = dict(selected=[dict(lane='fixed:smooth', program_id=1)])
        out = P.feedback(self.parent, self.binding, self.proof, selected, [], 'synthetic-artifact')
        for key in ('generated_bound_obligations', 'complete_source_reduction', 'cutoff_work_targets',
                    'selected_source_representation', 'inherited_proof_dependencies'):
            self.assertEqual(out[key], self.parent[key])
        self.assertEqual(out['next_search_tasks'][0], self.parent['next_search_tasks'][0])
        self.assertEqual(out['next_search_tasks'][2:], self.parent['next_search_tasks'][1:])
        self.assertEqual(self.proof['statistics']['conditional_Gram_routes'], 252)
        self.assertFalse(out['whole_signed_bound_proved'])


def tearDownModule():
    print('operations='+str(METER.operations))
