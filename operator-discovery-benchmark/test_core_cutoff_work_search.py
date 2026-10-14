"""Root-owned calibration, scope, and proof-composition boundary tests."""
from fractions import Fraction as Q
import json
import copy
from pathlib import Path
import unittest

import core_cutoff_work_search as P
import core_cutoff_bound_planner as B
from prime_bank_candidates import Meter


ROOT = Path(__file__).resolve().parent
METER = Meter(120000000, 600)


def evaluate(poly, values):
    answer = 0
    for term in poly:
        v = Q(term['coefficient'])
        for symbol in term['monomial']:
            v *= values[symbol[:-3]].conjugate() if symbol.endswith('bar') else values[symbol]
        answer += v
    return answer


class Algebra(unittest.TestCase):
    def test_ternary_work_matches_complete_energy_at_all_three_signs(self):
        values = dict(A=1j, E=1-1j, c=1, D=1+2j, z=1+1j, a=0.5, b=0.5+0.5j, v=1)
        for head in [False, True]:
            t = P.compile_transition(2, 3, head, METER)
            parent = values['A']**2*values['E']**3-(values['c']**3*values['D'] if head else 0)
            for x in [-1, 0, 1]:
                child = (values['A']+x*values['b'])**2*(values['E']+x*values['z']*(values['a']-values['b']))**3
                if head:
                    child -= (values['c']+x*values['a'])**3*(values['D']+values['v']*values['b'])
                delta = sum(x**j*evaluate(poly, values) for j, poly in enumerate(t['increment_sectors']))
                work = sum(x**j*evaluate(poly, values) for j, poly in enumerate(t['work_sectors']))
                self.assertEqual(delta, child-parent)
                self.assertAlmostEqual(work.real, (child*child.conjugate()-parent*parent.conjugate()).real)
                self.assertEqual(work.imag, 0)

    def test_zero_mu_correction_and_harmonic_nullness(self):
        raw = P.compile_transition(2, 3, False, METER)
        centered = P.compile_transition(2, 3, True, METER)
        self.assertEqual(raw['increment_sectors'][0], [])
        self.assertEqual(centered['increment_sectors'][0], [dict(monomial=['b', 'c', 'c', 'c', 'v'], coefficient='-1')])
        A, c, z, a, b, x = 2+3j, 1, 1-2j, .5, 1+.5j, -1
        E = 1+z*(c-A)
        self.assertEqual(E+x*z*(a-b), 1+z*((c+x*a)-(A+x*b)))

    def test_head_normal_form_generalizes_and_deduplicates_unit(self):
        for p, m, degree in [(0, 2, 2), (4, 2, -2), (2, 2, 0)]:
            found = P.head_search(p, m, METER)
            self.assertEqual(found['normal_form'], [dict(c_power=m, One_power=degree, coefficient='1')])
            self.assertEqual(len(found['matched_indices']), 1)
            self.assertTrue(found['zero_power_atom_deduplicated'])
            self.assertEqual(len(found['trials']), 6*(p+m+1)*(2*(p+m)+1))
            chosen = found['trials'][found['matched_indices'][0]]
            self.assertEqual(chosen['atom'], 'mu' if degree < 0 else 'One')

    def test_invalid_polynomial_and_contour_domains(self):
        for p, m in [(-1, 3), (17, 3), (2, 1), (2, 33)]:
            with self.assertRaises(ValueError):
                P.compile_transition(p, m, True, METER)
        for sigma in [Q(0), Q(2, 3), Q(3, 4)]:
            with self.assertRaises(ValueError):
                P.head_certificate(2, 3, Q(2, 3), sigma, Q(1, 24), Q(12, 5))


class RuleComposition(unittest.TestCase):
    def test_finite_kernel_recognition_and_open_symbol(self):
        terms = [dict(monomial=['b', 'c', 'c', 'c', 'v'], coefficient='-1')]
        c = B.finite_shift_control(terms, 1, Q(2, 3), Q(9, 20), METER)
        self.assertEqual(c['squared_norm_constant'], '6400/13')
        self.assertEqual(c['squared_norm_envelope'], B.envelope(Q(-9, 10)))
        self.assertFalse(c['target_assumed_in_proof'])
        self.assertTrue(B.finite_shift_control(terms, 0, Q(2, 3), Q(9, 20), METER)['identically_zero'])
        unsupported = B.finite_shift_control([dict(monomial=['A', 'b'], coefficient='1')], 1, Q(2, 3), Q(9, 20), METER)
        self.assertFalse(unsupported['available'])

    def test_sublinear_rules_and_critical_log_not_dropped(self):
        for r in [Q(1, 2), Q(1, 3), Q(1, 6)]:
            out = B.maximal_energy_rule(B.envelope(Q(-1, 2)), B.envelope(0), B.envelope(0), r)
            self.assertEqual(Q(out['resulting_envelope']['U_power']), Q(1, 2)/(1-r))
        critical = B.maximal_energy_rule(B.envelope(-1), B.envelope(0), B.envelope(0), Q(1, 2))
        self.assertEqual(critical['feedback_envelope'], B.envelope(0, 2))
        self.assertFalse(B.meets(critical['feedback_envelope'], Q(0)))
        self.assertTrue(B.meets(critical['feedback_envelope'], Q(1, 6)))
        self.assertEqual(B.summation(B.envelope(-2, 3)), B.envelope(0))
        for r in [-1, 1, 2]:
            with self.assertRaises(ValueError):
                B.maximal_energy_rule(None, B.envelope(0), B.envelope(0), r)

    def test_log_absorption_equality_requires_zero_log_cost(self):
        self.assertFalse(P.absorb(Q(1), 1, Q(1))['proved'])
        self.assertTrue(P.absorb(Q(1), 0, Q(1))['proved'])
        self.assertEqual(P.absorb(Q(1), 1, Q(3, 2))['multiplier'], '6')


class ActualObligation(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parent = json.loads((ROOT/'candidate10_weighted_height_obligation.json').read_text())
        cls.result = P.search(cls.parent, METER)
        cls.target = cls.result['targets'][0]

    def test_head_recovery_costs_and_entire_source_preserved(self):
        cert = self.target['head_bound']
        self.assertEqual(cert['global_squared_norm_constant'], '2560000/1573')
        self.assertEqual(cert['global_U_power'], '11/10')
        self.assertEqual(cert['physical_energy_X_power'], '-11/12')
        self.assertEqual(self.result['inherited_bindings'], self.parent['generated_bound_obligations'])
        self.assertEqual(self.result['inherited_complete_source_reduction'], self.parent['complete_source_reduction'])
        self.assertFalse(self.result['diagnostic_spec']['executed'])
        self.assertEqual(self.result['statistics']['new_component_bounds_proved'], 0)

    def test_search_pays_zero_sector_without_assuming_energy_goal(self):
        program = self.target['programs'][1]
        b = program['bound_search']
        route = b['routes'][b['selected_route']]
        self.assertEqual(route['method'], 'pay_zero_sector_by_energy_feedback')
        self.assertEqual(route['aggregation'], 'prefix')
        self.assertEqual(route['recurrence']['feedback_envelope'], B.envelope(Q(11, 10)))
        self.assertEqual(route['nonnegative_cost'], B.envelope(Q(21, 10)))
        self.assertEqual(route['forcing']['R_q']['sectors'], [1, 2])
        self.assertEqual(route['forcing']['power'], '12/5')
        self.assertEqual(route['status'], 'conditional_open_signed_work')
        self.assertFalse(route['recurrence']['target_assumed_in_proof'])
        self.assertFalse(b['goal_proved'])

    def test_consecutive_goal_is_optional_and_max_partial_is_not_endpoints(self):
        for program in self.target['programs']:
            self.assertFalse(program['missing_work']['head_correction_preserves_this_work_goal'])
            for route in program['bound_search']['routes'][1:]:
                if route['aggregation'] == 'consecutive':
                    self.assertIn('stronger', route['relation_to_original_goal'])
                    self.assertEqual(route['forcing']['power'], '7/5')
                if route['aggregation'] == 'dyadic_max_partial':
                    self.assertIn('EVERY integer', route['forcing']['quantifier'])
                    self.assertFalse(route['endpoint_samples_suffice'])

    def test_search_can_close_looser_goal_but_reject_unpaid_cost(self):
        program = self.target['programs'][1]
        args = (program, self.target['head_bound'], Q(2, 3), Q(9, 20))
        loose = B.search_bounds(*args, Q(6), Q(11, 2), METER)
        self.assertTrue(loose['goal_proved'])
        tight = B.search_bounds(*args, Q(1), Q(11, 2), METER)
        self.assertFalse(tight['goal_proved'])
        self.assertTrue(any(r['status'] == 'unpaid_auxiliary_cost' for r in tight['routes']))

    def test_inverse_head_dependence_requires_repartition(self):
        # Synthetic alternate head: the low-norm payment remains a bound,
        # but this zero-sector rule cannot assume v independent of mu(q).
        program = copy.deepcopy(self.target['programs'][1])
        cert = {**self.target['head_bound'], 'atom': 'mu'}
        out = B.search_bounds(program, cert, Q(2, 3), Q(9, 20), Q(12, 5), Q(11, 2), METER)
        self.assertFalse(out['zero_sector_control']['available'])
        self.assertFalse(any(r['method'] == 'pay_zero_sector_by_energy_feedback' for r in out['routes']))

    def test_feedback_contains_executable_exact_signed_target(self):
        fb = P.feedback(self.parent, self.result, 'input.json', 'search.json')
        self.assertEqual(fb['next_search_tasks'][0]['target_id'], 'actual_signed_core')
        next_target = fb['next_search_tasks'][1]['next_bound_targets'][0]
        self.assertEqual(next_target['status'], 'open')
        self.assertEqual(next_target['R_q']['sectors'], [1, 2])
        self.assertTrue(all(next_target['R_q']['sector_polynomials']))
        self.assertEqual(fb['generated_bound_obligations'], self.parent['generated_bound_obligations'])
        self.assertFalse(fb['RH_proved'])


def tearDownModule():
    print('operations='+str(METER.operations))


if __name__ == '__main__':
    unittest.main()
