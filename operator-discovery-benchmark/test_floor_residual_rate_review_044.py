"""Synthetic AST/asymptotic certificates; no new N norms or selected application."""
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import time
import unittest

import floor_residual_rate_review_044 as review

METERS = []


def meter(**kwargs):
    instance = review.Meter(**kwargs)
    METERS.append(instance)
    return instance


def taper(coordinate='log', alpha='1/3', gamma='1'):
    return {'kind': 'taper', 'coordinate': coordinate, 'alpha': alpha, 'gamma': gamma}


def recipe(base=None, envelope=None, channel='mu', coefficient='1/2', identifier='synthetic'):
    return {'id': identifier, 'base': {'kind': 'unit'} if base is None else base,
            'auxiliary': None if envelope is None else {'channel': channel, 'coefficient': coefficient, 'envelope': envelope}}


def rule(identifier='synthetic', q=2, b='1', eta='1', stratum='synthetic'):
    return {'family': identifier, 'q': q, 'b': b, 'finite_log_bound': {'A': '1/4', 'eta': eta}, 'stratum': stratum}


class LogRateTests(unittest.TestCase):
    def setUp(self):
        self.meter = meter()

    def test_log_taper_and_twist_exact_rates(self):
        t = review.weight_correction(taper(alpha='1/257', gamma='3/7'), 3, self.meter)
        self.assertEqual(t['rate'], '1/257')
        self.assertEqual(t['coefficient'], [{'rational': '-3/7', 'log_n_power': '1/257', 'log_2_power': '-1/257'}])
        v = review.weight_correction({'kind': 'vanishing_twist', 'rate': '2/7', 'level_power': 2}, 3, self.meter)
        self.assertEqual(v['rate'], '2')
        self.assertEqual(v['coefficient'][0]['rational'], '-2/7')
        self.assertEqual(v['coefficient'][0]['log_n_power'], '1')

    def test_flat_rules_are_individually_justified(self):
        fixtures = [recipe(), recipe(taper('cutoff', '2/7')),
                    recipe(envelope={'kind': 'power_amplitude', 'power': '1/7', 'weight': taper()}),
                    recipe(envelope={'kind': 'moving_band', 'cutoff_power': '3/7', 'weight': taper()})]
        for p in fixtures:
            self.assertEqual(review.coefficient_error(p, 3, self.meter)['expansion']['status'], 'flat')

    def test_products_and_log_amplitude(self):
        product = {'kind': 'product', 'left': taper(alpha='1/3'),
                   'right': {'kind': 'vanishing_twist', 'rate': '1/5', 'level_power': 1}}
        correction = review.weight_correction(product, 5, self.meter)
        self.assertEqual(correction['rate'], '1/3')
        envelope = {'kind': 'log_amplitude', 'power': '2/5', 'weight': product}
        e = review.envelope_expansion(envelope, 3, self.meter)
        self.assertEqual(e['rate'], '2/5')
        self.assertEqual(e['coefficient'], [{'rational': '1', 'log_n_power': '0', 'log_2_power': '0'}])

    def test_conservative_cancellation_and_barrier(self):
        difference = {'kind': 'difference', 'left': taper(alpha='1'), 'right': taper(alpha='1')}
        e = review.envelope_expansion(difference, 3, self.meter)
        self.assertEqual(e['status'], 'UNRESOLVED')
        self.assertEqual(e['cancellation_barrier'], '1')
        self.assertEqual(review.coefficient_error(recipe(envelope=difference), 3, self.meter)['expansion']['status'], 'UNRESOLVED')
        slower = review.coefficient_error(recipe(taper(alpha='1/3'), difference), 3, self.meter)['expansion']
        self.assertEqual(slower['rate'], '1/3')
        faster = review.coefficient_error(recipe(taper(alpha='2'), difference), 3, self.meter)['expansion']
        self.assertEqual(faster['status'], 'UNRESOLVED')

    def test_recipe_leading_terms_cancel_without_flat_inference(self):
        # At a prime: base error=-logratio and auxiliary=mu*(logT-unit)
        # has leading+logratio. The cancellation's next order is uncompiled.
        p = recipe(taper(alpha='1'), {'kind': 'difference', 'left': taper(alpha='1'), 'right': {'kind': 'unit'}},
                   coefficient='1')
        result = review.coefficient_error(p, 3, self.meter)['expansion']
        self.assertEqual(result['status'], 'UNRESOLVED')
        self.assertEqual(result['cancellation_barrier'], '1')

    def test_exact_zero_arithmetic_multiplier_removes_uncertainty(self):
        difference = {'kind': 'difference', 'left': taper(), 'right': taper()}
        error = review.coefficient_error(recipe(envelope=difference, channel='mu'), 4, self.meter)
        self.assertEqual(error['mu'], 0)
        self.assertEqual(error['auxiliary_arithmetic'], '0')
        self.assertEqual(error['expansion']['status'], 'flat')

    def test_canonical_n2_and_mixed_sign_license(self):
        terms = [{'rational': '1', 'log_n_power': '1/3', 'log_2_power': '-1/3'},
                 {'rational': '-1', 'log_n_power': '0', 'log_2_power': '0'}]
        self.assertEqual(review.canonical_terms(terms, 2), [])
        self.assertEqual(review.license_nonzero(terms, 2, meter=self.meter)['status'], 'UNRESOLVED')
        at3 = review.license_nonzero(terms, 3, meter=self.meter)
        self.assertEqual(at3['status'], 'certified')
        self.assertEqual(at3['method'], 'Arb')
        self.assertEqual(at3['sign'], 1)

    def test_witness_import_independent_column_replay(self):
        result = review.review_recipe(recipe(taper()), max_index=6, meter=self.meter)
        w = result['target_candidates'][1]['witness']
        self.assertEqual(w['denominator'], '20')
        self.assertTrue(review.verify_witness(w, self.meter))
        altered = deepcopy(w)
        altered['cells'][0]['alpha'] = '-2'
        with self.assertRaises(ValueError):
            review.verify_witness(altered, self.meter)

    def test_strict_eta_gate_and_zero_step_response(self):
        envelope = {'kind': 'difference', 'left': taper(alpha='1/3'), 'right': taper(alpha='1')}
        p = recipe(taper('cutoff', '2/7'), envelope)
        result = review.review_recipe(p, [rule(eta='1'), rule(eta='2/3', stratum='equality'),
                                         rule(eta='1/2', stratum='lower')], max_index=6, meter=self.meter)
        self.assertEqual([row['status'] for row in result['rule_reviews']], ['analytically_refuted', 'OPEN', 'OPEN'])
        rejection = result['rule_reviews'][0]['strongest_rejection']
        self.assertEqual(rejection['index'], 3)
        self.assertEqual(rejection['energy_rate'], '2/3')
        self.assertEqual(rejection['step_response'], '0')
        self.assertEqual(rejection['candidate']['witness']['denominator'], '20')
        self.assertEqual(rejection['candidate']['nonzero_license']['sign'], 1)
        self.assertEqual(result['rule_reviews'][0]['forcing_candidates'][0]['status'], 'UNRESOLVED')
        self.assertEqual(result['convergence_status'], 'OPEN')

    def test_b0_and_repeated_selected_strata(self):
        p = recipe(taper())
        selected = {'recipes': [p], 'rules': [rule(b='1'), rule(b='0', stratum='restatement')]}
        result = review.audit_selected(selected, max_index=6, meter=self.meter)
        rules = result['reviews'][0]['rule_reviews']
        self.assertEqual(len(rules), 2)
        self.assertEqual(rules[0]['strongest_rejection']['index'], 3)
        self.assertEqual(rules[1]['strongest_rejection']['index'], 2)
        self.assertFalse(result['additional_norms_evaluated'])
        self.assertFalse(result['source_arrays_read'])
        self.assertFalse(result['RH_proved'])
        json.dumps(result)

    def test_frontier_preserves_open_convergence(self):
        recipes = [recipe(taper(), identifier='log'), recipe(taper('cutoff'), identifier='flat')]
        result = review.review_frontier(recipes, ['1/3', '2/3', '1'], max_index=6, meter=self.meter)
        self.assertEqual(result['rows'][0]['refuted_etas'], ['1'])
        self.assertEqual(result['rows'][0]['OPEN_etas'], ['1/3', '2/3'])
        self.assertEqual(result['rows'][1]['refuted_etas'], [])
        self.assertTrue(all(row['convergence_status'] == 'OPEN' for row in result['rows']))

    def test_resource_and_typed_schema_guards(self):
        with self.assertRaises(OverflowError):
            review.coefficient_error(recipe(taper()), 3, meter(cap=0))
        for bad in (taper(alpha='0'), taper(coordinate='unknown'), taper(alpha='2/6')):
            with self.assertRaises(ValueError):
                review.weight_correction(bad, 3, self.meter)
        with self.assertRaises(ValueError):
            review.weight_correction({'kind': 'vanishing_twist', 'rate': '1', 'level_power': True}, 3, self.meter)
        with self.assertRaises(ValueError):
            review.audit_selected({'recipes': [recipe()], 'rules': []}, max_index=6, meter=self.meter)


if __name__ == '__main__':
    started = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(LogRateTests)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    invocation = {'returncode': 0 if result.wasSuccessful() else 1,
                  'tests': result.testsRun, 'failures': len(result.failures), 'errors': len(result.errors),
                  'elapsed_seconds': time.monotonic()-started,
                  'operations': sum(m.operations for m in METERS),
                  'exposure': 'synthetic typed ASTs, rational/log monomials and imported recovery witnesses only'}
    path = Path(__file__).with_name('floor_residual_rate_review_044_development.json')
    receipt = json.loads(path.read_text()) if path.exists() else {
        'schema': 'floor-log-rate-development-v1', 'invocations': [],
        'actual_selected_or_frontier_applied': False, 'additional_norms_evaluated': False,
        'source_arrays_read': False, 'frozen_files_modified': False,
        'old_suites_or_studies_rerun': False, 'hashes_generated': False}
    receipt['invocations'].append(invocation)
    receipt['cumulative_operations'] = sum(row['operations'] for row in receipt['invocations'])
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    raise SystemExit(invocation['returncode'])
