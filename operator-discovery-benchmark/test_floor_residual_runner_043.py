"""043 integration with synthetic coefficients; no search performance observed."""
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest

import run_floor_residual_043 as R


class RunnerTests(unittest.TestCase):
    def test_compiled_batch_shares_identical_programs_and_preserves_roles(self):
        recipe = dict(id='toy', channel='one', taper=None, decay='0', anchor_cell_one=False)
        search = dict(selected_recipes=[recipe], selections=[
            dict(stratum='positive', family='toy', q=2, b='1', finite_contraction_tau=None, finite_log_bound=None),
            dict(stratum='negative', family='toy', q=3, b='-1/2', finite_contraction_tau=None, finite_log_bound=None),
            dict(stratum='control', family='toy', q=2, b='0', finite_contraction_tau=None, finite_log_bound=None)])
        batch = R.compile_batch(search, R.SEARCH.FINAL_PARENTS)
        self.assertEqual(len(batch['cases']), 9)
        self.assertEqual(len({R.semantic_key(p) for p in batch['programs']}), len(batch['programs']))
        for c in batch['cases']:
            if c['b'] == '0':
                self.assertEqual(c['child'], c['forcing'])
        for r in batch['rules']:
            self.assertTrue(r['relative_conditional_gate']['admissible'])
            self.assertFalse(r['conditional_gate']['convergence_proved'])
        with self.assertRaises(ValueError):
            R.compile_batch(search, (40, 64, 81))

    def test_independent_certificate_pipeline_with_signed_steps(self):
        p = R.SEARCH.program('pipeline_toy', {2: Q(3, 7), 5: Q(-1, 13)}, {3: Q(2, 11)})
        row = R.audit_one(dict(program=p, H=128))
        self.assertTrue(row['verification']['verified'])
        self.assertTrue(row['verification']['all_domain_included'])
        self.assertFalse(row['verification']['target_zero_guard_available'])
        self.assertFalse(row['verification']['convergence_proved'])
        self.assertGreater(row['checker_operations'], 0)

    def test_exact_diagnostic_bounds_and_scope(self):
        def energy(v):
            return dict(verification=dict(global_fixed_norm_squared_lower=str(v), global_fixed_norm_squared_upper=str(v)))
        rows = {'parent':energy(4), 'child':energy(1), 'forcing':energy(1)}
        c = dict(rule='toy', N=40, q=2, b='1', tau='1/4', parent='parent', child='child', forcing='forcing')
        c['log_bound'] = R.log_bound_interval(40, '4', '1/2')
        a = R.analyze_case(c, rows)
        self.assertEqual(a['relative_forcing_status'], 'verified_at_this_support')
        self.assertEqual(a['signed_cross_effect'], 'strict_cancellation')
        self.assertEqual(a['signed_forcing_cross']['upper'], '-2')
        self.assertFalse(a['all_supports_inequality_proved'])
        self.assertEqual(a['logarithmic_forcing_status'], 'verified_at_this_support')
        self.assertEqual(a['signed_mechanism_for_bound'], 'signed_cross_needed_even_against_diagonal')
        c['tau'] = '1/8'
        self.assertEqual(R.analyze_case(c, rows)['relative_forcing_status'], 'refuted_at_this_support')
        c['b'] = '0'
        self.assertEqual(R.analyze_case(c, rows)['signed_cross_effect'], 'zero_by_restatement')
        self.assertEqual(R.analyze_case(c, rows)['signed_mechanism_for_bound'], 'endpoint_restatement')

    def test_log_bound_exact_arbitrary_root_bracket(self):
        bound = R.log_bound_interval(100, '3/7', '123/257')
        lo, hi = Q(bound['lower'])/Q('3/7'), Q(bound['upper'])/Q('3/7')
        self.assertLessEqual(lo**257, Q(1, 7)**123)
        self.assertGreater(hi**257, Q(1, 7)**123)
        with self.assertRaises(ValueError):
            R.log_bound_interval(100, '3/7', '7/5')


if __name__ == '__main__':
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(RunnerTests))
    record = dict(returncode=0 if result.wasSuccessful() else 1, tests=result.testsRun,
                  failures=len(result.failures), errors=len(result.errors), elapsed_seconds=time.monotonic()-started,
                  exposure='one constant synthetic recipe compiled without norm evaluation; signed rational toy norm128; artificial diagnostics')
    path = Path(__file__).with_name('floor_residual_runner_043_development.json')
    receipt = json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1', invocations=[])
    receipt['invocations'].append(record)
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(record))
    raise SystemExit(record['returncode'])
