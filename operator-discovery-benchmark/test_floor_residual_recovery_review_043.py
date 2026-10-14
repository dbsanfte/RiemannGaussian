"""Owned exact/synthetic recovery checks, without any norm evaluator call."""
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import time
import unittest

import floor_residual_recovery_review_043 as review

METERS = []


def meter(**kwargs):
    instance = review.Meter(**kwargs)
    METERS.append(instance)
    return instance


def recipe(identifier='toy', channel='mu', beta='0', anchor=False, alpha='2/7', gamma='1'):
    return {'id': identifier, 'channel': channel, 'decay': beta,
            'anchor_cell_one': anchor, 'taper': {'alpha': alpha, 'gamma': gamma}}


def rule(identifier='toy', q=2, b='1/2', stratum='toy_rule'):
    return {'family': identifier, 'q': q, 'b': b, 'stratum': stratum}


def residual(k, coefficients, steps):
    return 1-sum(c*F(k % n, n) for n, c in coefficients.items()) \
            -sum(d for q, d in steps.items() if k >= q)


class RecoveryReviewTests(unittest.TestCase):
    def setUp(self):
        self.meter = meter()

    def test_discovered_small_witnesses(self):
        expected = {2: ({1: '-2', 2: '1'}, '14', '-1'),
                    3: ({1: '-1', 2: '-1', 3: '1'}, '20', '-1'),
                    4: ({1: '1', 2: '-1', 3: '-1', 4: '1'}, '40', '0')}
        for n, (alpha, denominator, constant) in expected.items():
            witness = review.generate_witness(n, self.meter)
            self.assertEqual({row['k']: row['alpha'] for row in witness['cells']}, alpha)
            self.assertEqual(witness['denominator'], denominator)
            self.assertEqual(witness['constant'], constant)
            self.assertTrue(review.verify_witness(witness, self.meter))

    def test_arbitrary_higher_support_and_step_identity(self):
        coefficients = {2: F(7, 3), 3: F(-1, 2), 4: F(5, 7), 11: F(-3), 101: F(2, 257)}
        steps = {2: F(1, 2), 5: F(-2, 3)}
        for n in range(2, 11):
            w = review.generate_witness(n, self.meter)
            alpha = {row['k']: F(row['alpha']) for row in w['cells']}
            lhs = coefficients.get(n, F(0))+review.mu(n, self.meter) \
                  -sum(d*sum(a for k, a in alpha.items() if k >= q) for q, d in steps.items())
            rhs = sum(a*residual(k, coefficients, steps) for k, a in alpha.items())
            self.assertEqual(lhs, rhs)
            for j in (n+1, 101, 1009):
                self.assertEqual(sum(a*F(k % j, j) for k, a in alpha.items()), 0)
                self.meter.charge(12)

    def test_cauchy_constant_against_synthetic_cell_values(self):
        for n in range(2, 9):
            w = review.generate_witness(n, self.meter)
            alpha = {row['k']: F(row['alpha']) for row in w['cells']}
            e = {k: F((-1)**k*(k+2), 7) for k in alpha}
            linear = sum(a*e[k] for k, a in alpha.items())
            cell_energy = sum(e[k]**2/F(k*(k+1)) for k in alpha)
            self.assertLessEqual(linear**2, F(w['denominator'])*cell_energy)
            # Equality calibration, so the supplied denominator is sharp for
            # this finite-cell functional without additional tail assumptions.
            optimal = {k: a*k*(k+1) for k, a in alpha.items()}
            self.assertEqual(sum(a*optimal[k] for k, a in alpha.items())**2,
                             F(w['denominator'])*sum(optimal[k]**2/F(k*(k+1)) for k in alpha))

    def test_witness_replay_rejects_tampering(self):
        w = review.generate_witness(7, self.meter)
        for field, value in (('constant', '0'), ('denominator', '1'),
                             ('higher_support_slope', '1'), ('identity', 'RH proved')):
            altered = deepcopy(w)
            altered[field] = value
            with self.assertRaises(ValueError):
                review.verify_witness(altered, self.meter)
        altered = deepcopy(w)
        altered['cells'][0]['alpha'] = '2'
        with self.assertRaises(ValueError):
            review.verify_witness(altered, self.meter)

    def test_exact_root_brackets_and_independent_replay(self):
        for base, exponent in ((F(1, 3), '1/7'), (F(1, 2), '1/257'),
                               (F(1, 4), '1/2'), (F(0), '1/3'), (F(1), '4/3'), (F(1, 7), '0')):
            bracket = review.root_bracket(base, exponent, 20, self.meter)
            self.assertTrue(review.verify_root_bracket(bracket, self.meter))
            if exponent != '0':
                a, b = F(exponent).numerator, F(exponent).denominator
                self.assertLessEqual(F(bracket['lower'])**b, base**a)
                self.assertGreaterEqual(F(bracket['upper'])**b, base**a)
        altered = review.root_bracket(F(1, 3), '1/7', 20, self.meter)
        altered['lower'], altered['upper'] = '1', '1'
        with self.assertRaises(ValueError):
            review.verify_root_bracket(altered, self.meter)

    def test_channels_from_scalar_factorization(self):
        self.assertEqual(review.channel_value('mu', 4, self.meter), 0)
        self.assertEqual(review.channel_value('liouville', 4, self.meter), 1)
        self.assertEqual(review.channel_value('radical_sign', 4, self.meter), -1)
        self.assertEqual(review.channel_value('mu_convolution_mu', 6, self.meter), 4)
        self.assertEqual(review.channel_value('mu_convolution_mu', 8, self.meter), 0)
        self.assertEqual(review.channel_value('mu_plus_half_liouville', 3, self.meter), F(-3, 2))

    def test_anchor_preserved_and_mu_necessary_condition_open(self):
        for anchor in (False, True):
            r = review.review_recipe(recipe(anchor=anchor), max_index=8, meter=self.meter)
            self.assertEqual(r['target_convergence_status'], 'OPEN')
            self.assertIsNone(r['strongest_target_witness'])
            self.assertTrue(r['necessary_condition_only'])
            if anchor:
                self.assertEqual(r['target_candidates'][0]['status'], 'unresolved')
            self.assertFalse(r['RH_proved'])

    def test_generic_fixed_mixture_and_forcing_obstruction(self):
        mixed = recipe(channel='mu_plus_half_liouville')
        r = review.review_recipe(mixed, rule(), max_index=8, meter=self.meter)
        self.assertEqual(r['target_convergence_status'], 'analytically_refuted')
        self.assertEqual(r['strongest_target_witness']['index'], 2)
        self.assertEqual(r['strongest_target_witness']['liminf_energy_lower'], '1/56')
        self.assertEqual(r['forcing_bound_status'], 'analytically_refuted')
        self.assertEqual(r['strongest_forcing_witness']['index'], 4)
        self.assertEqual(r['strongest_forcing_witness']['liminf_forcing_energy_lower'], '9/640')
        self.assertEqual(r['forcing_candidates'][0]['status'], 'unresolved')
        for b in ('-1', '0'):
            other = review.review_recipe(mixed, rule(b=b), max_index=8, meter=self.meter)
            self.assertEqual(other['forcing_bound_status'], 'analytically_refuted')

    def test_irrational_limit_and_beta_anchor_obstruction(self):
        r = review.review_recipe(recipe(channel='mu_plus_half_liouville', beta='1/7'),
                                 rule(b='0'), max_index=8, meter=self.meter)
        self.assertEqual(r['target_convergence_status'], 'analytically_refuted')
        best = r['strongest_target_witness']
        self.assertGreater(F(best['liminf_energy_lower']), 0)
        self.assertNotEqual(best['coefficient_limit']['lower'], best['coefficient_limit']['upper'])
        anchored = review.review_recipe(recipe(beta='1/7', anchor=True), max_index=8, meter=self.meter)
        self.assertEqual(anchored['target_candidates'][0]['status'], 'unresolved')
        self.assertEqual(anchored['target_convergence_status'], 'analytically_refuted')

    def test_selector_multiple_rules_and_missing_match(self):
        chosen = {'recipes': [recipe(channel='mu_plus_half_liouville')],
                  'rules': [rule(b='1/2', stratum='positive'), rule(b='-1', stratum='negative')]}
        result = review.audit_selected(chosen, max_index=6, meter=self.meter)
        self.assertEqual(len(result['reviews']), 2)
        self.assertEqual([r['rule']['b'] for r in result['reviews']], ['1/2', '-1'])
        json.dumps(result)
        for bad in ({'recipes': [recipe()], 'rules': []},
                    {'recipes': [recipe()], 'rules': [rule(identifier='missing')]},
                    {'recipes': [recipe()], 'rules': [rule(), rule()]}):
            with self.assertRaises(ValueError):
                review.review_selected(bad, max_index=6, meter=self.meter)

    def test_frontier_is_only_a_necessary_condition_filter(self):
        recipes = [recipe('a'), recipe('b', beta='1/7'), recipe('c', channel='liouville'),
                   recipe('d', anchor=True), recipe('e', channel='radical_sign')]
        frontier = review.review_frontier(recipes, max_index=6, meter=self.meter)
        self.assertEqual({r['id'] for r in frontier['OPEN_recipes']}, {'a', 'd'})
        self.assertEqual(frontier['refuted'], 3)
        self.assertFalse(frontier['frontier_convergence_proved'])
        self.assertFalse(frontier['prior_selection_or_scores_changed'])
        self.assertFalse(frontier['additional_norms_evaluated'])
        self.assertFalse(frontier['source_arrays_read'])

    def test_resource_guards(self):
        with self.assertRaises(OverflowError):
            review.generate_witness(3, meter(cap=0))
        for n in (True, 1, 65):
            with self.assertRaises(ValueError):
                review.generate_witness(n, self.meter)
        with self.assertRaises(OverflowError):
            review.root_bracket(F(1, 3), '1/1000000', 24, self.meter)
        with self.assertRaises(ValueError):
            review.coefficient_limit(recipe(beta='2/14'), 3, meter=self.meter)


if __name__ == '__main__':
    started = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(RecoveryReviewTests)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    invocation = {'returncode': 0 if result.wasSuccessful() else 1,
                  'tests': result.testsRun, 'failures': len(result.failures), 'errors': len(result.errors),
                  'elapsed_seconds': time.monotonic()-started,
                  'operations': sum(m.operations for m in METERS),
                  'max_power_bits': max(m.max_power_bits for m in METERS),
                  'exposure': 'synthetic exact cell witnesses, scalar arithmetic channels and rational root brackets only'}
    path = Path(__file__).with_name('floor_residual_recovery_review_043_development.json')
    receipt = json.loads(path.read_text()) if path.exists() else {
        'schema': 'floor-recovery-review-development-v1', 'invocations': [],
        'additional_norms_evaluated': False, 'source_arrays_read': False,
        'frozen_files_modified': False, 'hashes_generated': False}
    receipt['invocations'].append(invocation)
    receipt['cumulative_operations'] = sum(row['operations'] for row in receipt['invocations'])
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    raise SystemExit(invocation['returncode'])
