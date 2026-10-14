import copy
from fractions import Fraction as Q
import json
from pathlib import Path
import unittest

import core_moment_bound_search as P
from prime_bank_candidates import Meter


METER = Meter(100000000, 600)
ROOT = Path(__file__).resolve().parent


def c(p=2, m=2, theta='2/3', alpha='1/24', sigma='3/8', orders=None):
    return P.candidate(p, m, Q(theta), Q(alpha), Q(sigma),
        ['2', '4'] if orders is None else orders, Q(0), METER)


class MomentRules(unittest.TestCase):
    def test_fractional_holder_vertices(self):
        vertices = P.holder_vertices([Q(3, 4), Q(2, 3)])
        self.assertEqual(set(vertices), {(Q(0), Q(0)), (Q(3, 4), Q(0)),
            (Q(0), Q(2, 3)), (Q(3, 4), Q(1, 4)), (Q(1, 3), Q(2, 3))})

    def test_fractional_moment_powers(self):
        for power in ('1/2', '1/3', '1/6'):
            r = P.product_moment_search([dict(real_part='3/4', power=power)], ['2', '4'], METER)
            self.assertEqual(r['best']['integral_height_power'], '1')
            self.assertEqual(r['best']['factors'][0]['convexity_power'], '0')

    def test_generic_payable_rule(self):
        r = c()
        self.assertTrue(r['target_met'])
        self.assertEqual(r['full_finite_factor_U_power'], '5')
        self.assertEqual(r['recovered_energy_X_power'], '-1/24')
        self.assertEqual(r['mellin_height_powers'], ['-1', '-5/24'])

    def test_strict_mellin_boundary(self):
        r = c(sigma='1/3')
        self.assertFalse(r['strict_tail_summation'])
        self.assertIsNone(r['epsilon'])
        self.assertFalse(r['target_met'])

    def test_moment_ablation(self):
        self.assertFalse(c(orders=[])['target_met'])
        self.assertFalse(c(orders=['2'])['target_met'])

    def test_analytic_residue_does_not_pay_ordinary_moment(self):
        r = c(m=3, alpha='1/100', sigma='9/20')
        self.assertTrue(r['strict_tail_summation'])
        self.assertLess(Q(r['recovered_energy_X_power']), 0)
        self.assertEqual(r['failed_premises'], ['ordinary_centering_moment_unproved'])

    def test_cutoff_cost_is_not_dropped(self):
        r = c(m=3, sigma='9/20')
        self.assertIn('cutoff_cost_exceeds_target_energy_power', r['failed_premises'])
        self.assertIn('ordinary_centering_moment_unproved', r['failed_premises'])

    def test_changed_kernel_and_finite_degree(self):
        self.assertTrue(c(p=0, theta='3/4', alpha='1/100', sigma='2/5')['target_met'])
        self.assertFalse(c(p=0, theta='1/3', alpha='1/100', sigma='1/4')['target_met'])

    def test_full_history_hardy_constant(self):
        channels = [dict(eta='1/6', polynomial=['0', '1'])]
        self.assertEqual(P.channel_constant(channels, Q(1, 4)), '484')
        with self.assertRaises(ValueError):
            P.channel_constant([dict(eta='-1/6', polynomial=['1'])], Q(1, 4))

    def test_reject_unlicensed_provider_and_contour(self):
        with self.assertRaises(ValueError):
            c(orders=['6'])
        with self.assertRaises(ValueError):
            c(sigma='1/2')
        with self.assertRaises(ValueError):
            c(sigma='0')


class CompleteSearch(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Read trusted frozen inputs; do not run another source experiment.
        import run_core_moment_bound_search as RUN
        cls.parent = json.loads((ROOT/RUN.INPUT).read_text())
        cls.context = RUN.load_context()
        cls.result = P.search(cls.parent, cls.context, P.DEFAULT_SPEC, METER)

    def test_complete_source_search_and_recovery(self):
        result = self.result
        self.assertEqual(len(result['targets']), len(self.parent['auxiliary_bound_targets']))
        paid = [t for t in result['targets'] if t['component_bound_proved']]
        self.assertTrue(paid)
        self.assertLess(len(paid), len(result['targets']))
        self.assertEqual(len(result['source_reduction']['bindings']), 144)
        self.assertEqual(result['source_reduction']['transport_error_retained'], '-e')
        self.assertEqual(len(result['source_reduction']['new_paid_components']), len(paid))
        for t in paid:
            chosen = t['candidate_lines'][t['selected']]
            self.assertTrue(chosen['complete_centering']['ordinarily_convergent'])
            self.assertLessEqual(Q(chosen['recovered_energy_X_power']), 0)
            self.assertIsNone(t['proof_constant']['numerical_value'])
        self.assertFalse(result['whole_signed_bound_proved'])

    def test_feedback_keeps_remaining_bounds_open(self):
        fb = P.feedback(self.parent, self.result, 'input.json', 'search.json')
        self.assertEqual(fb['next_search_tasks'][0]['target_id'], 'actual_signed_core')
        self.assertTrue(any(t.get('missing_estimate') for t in fb['next_search_tasks']))
        self.assertTrue(all(t['status'] == 'open' for t in fb['next_search_tasks']))
        self.assertFalse(fb['RH_proved'])

    def test_no_missing_channel_program_or_source_term(self):
        bad = copy.deepcopy(self.context)
        bad['channel_programs'].pop()
        with self.assertRaises(ValueError):
            P.source_reduction(self.parent, bad, self.result['targets'], METER)
        bad = copy.deepcopy(self.context)
        bad['complete_signed_join']['collected_terms'] = []
        with self.assertRaises(ValueError):
            P.source_reduction(self.parent, bad, self.result['targets'], METER)


def tearDownModule():
    print('operations='+str(METER.operations), flush=True)


if __name__ == '__main__':
    unittest.main()
