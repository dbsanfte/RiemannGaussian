"""Synthetic signed comparison and scope tests for the new transition runner."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest

import run_floor_residual_transitions_050 as R


def norm(lo, hi=None):
    return dict(verification=dict(verified=True, all_domain_included=True, convergence_proved=False,
        global_fixed_norm_squared_lower=str(Q(lo)), global_fixed_norm_squared_upper=str(Q(lo if hi is None else hi))))


def selection():
    return dict(tau='1', request=dict(target=dict(A='1/4', eta='1/2'),
        argument=dict(recurrence=dict(rho='3/4', C='1/32'))))


class TransitionRunnerTests(unittest.TestCase):
    def test_receipt_adapter_admits_only_passing_source_free_guard_schema(self):
        receipt = dict(schema='floor-residual-prime-work-guard-050-development-v1', invocations=1,
            tests_run=10, errors=0, failures=0, failed_attempts=[], actual_norms_evaluated=False,
            scientific_candidates_applied=False, source_values_evaluated=False)
        self.assertEqual(R.verify_receipt(receipt), receipt)
        for key, value in [('errors', 1), ('tests_run', 0), ('invocations', True),
                           ('source_values_evaluated', True), ('failed_attempts', ['failure'])]:
            changed = deepcopy(receipt); changed[key] = value
            with self.assertRaises(ValueError): R.verify_receipt(changed)
        self.assertEqual(R.verify_receipt(dict(invocations=[dict(returncode=0)])), dict(returncode=0))

    def test_failing_recurrence_does_not_refute_a_passing_target(self):
        result = R.assess(selection(), dict(N=32, r=0, child=64),
            {32: dict(h=norm('1/50'), v=norm('1/50')), 64: dict(h=norm('1/25'), v=norm('1/25'))})
        self.assertEqual(result['status'], 'refuted_at_this_pair')
        self.assertTrue(result['recurrence_refuted'])
        self.assertFalse(result['potential_target_refuted'])
        self.assertFalse(result['whole_h_target_refuted'])
        self.assertFalse(result['RH_refuted'])
        self.assertEqual(Q(result['potential_increment']['lower']), Q(1, 20))

    def test_separates_potential_and_whole_target_counterexamples(self):
        result = R.assess(selection(), dict(N=32, r=1, child=65),
            {32: dict(h=norm('1/50'), v=norm('1/50')), 65: dict(h=norm('1/25'), v=norm('1/5'))})
        self.assertTrue(result['potential_target_refuted'])
        self.assertFalse(result['whole_h_target_refuted'])
        self.assertFalse(result['RH_proved'])

    def test_interval_signs_for_parent_subtraction_and_unresolved_refinement(self):
        result = R.assess(selection(), dict(N=32, r=0, child=64),
            {32: dict(h=norm('1/100', '1/10'), v=norm('1/100', '1/10')),
             64: dict(h=norm('1/200', '3/100'), v=norm('1/200', '3/100'))})
        self.assertEqual(result['status'], 'unresolved_interval')
        self.assertEqual(Q(result['potential_increment']['lower']), Q(-7, 50))
        self.assertEqual(Q(result['potential_increment']['upper']), Q(9, 200))
        self.assertFalse(result['recurrence_refuted'])

    def test_finite_pass_keeps_uniform_claim_open(self):
        result = R.assess(selection(), dict(N=32, r=0, child=64),
            {32: dict(h=norm('1/25'), v=norm('1/25')), 64: dict(h=norm('1/40'), v=norm('1/40'))})
        self.assertEqual(result['status'], 'verified_at_this_pair')
        self.assertFalse(result['uniform_recurrence_proved'])

    def test_rejects_partial_or_forged_norm_admission(self):
        for field, value in [('verified', False), ('all_domain_included', False), ('convergence_proved', True)]:
            row = norm('1/10'); row['verification'][field] = value
            with self.assertRaises(ValueError): R.interval(row)
        with self.assertRaises(ValueError): R.interval(norm('1/10', '1/20'))
        with self.assertRaises(ValueError): R.interval(norm('-1/10', '1/20'))

    def test_rounding_rejects_nondict_and_extra_fields_before_source_compilation(self):
        recipe = dict(id='synthetic', base=dict(kind='drift_mixture', a='1', theta='13/23',
            terms=[dict(rate='1', weight='1')]), auxiliary=None)
        request = dict(source_recipe=recipe, prime=3, parent_support=7, d='2', rounding=None)
        with self.assertRaises(ValueError): R.SEARCH.validate_request(request)
        request['rounding'] = deepcopy(R.SEARCH.ROUNDING); request['rounding']['unbound'] = 1
        with self.assertRaises(ValueError): R.SEARCH.validate_request(request)


if __name__ == '__main__':
    path = Path(__file__).with_name('floor_residual_transition_runner_050_development.json')
    if path.exists(): raise SystemExit('preserve focused runner receipt')
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(TransitionRunnerTests))
    receipt = dict(schema='transition-runner-development-v1', invocations=[dict(
        returncode=0 if result.wasSuccessful() else 1, tests=result.testsRun,
        failures=len(result.failures), errors=len(result.errors), elapsed_seconds=time.monotonic()-started,
        operations=R.CAP.CONVERSION_OPERATIONS)],
        scope='synthetic interval/scope and input tests, no actual candidate arrays or norm observations')
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
