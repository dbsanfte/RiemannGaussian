"""044 integration: synthetic coefficients, exact diagnostics, no scores."""
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest
from unittest.mock import patch

import run_floor_residual_044 as R


class RunnerTests(unittest.TestCase):
    def test_development_receipt_schemas_and_failure_rejection(self):
        for key in ('invocations','runs'):
            self.assertEqual(R.verify_development_receipt({key:[dict(returncode=0)]})['returncode'],0)
            with self.assertRaises(ValueError):
                R.verify_development_receipt({key:[dict(returncode=1)]})
        with self.assertRaises(ValueError):
            R.verify_development_receipt({})

    def test_frozen_batch_dedup_and_auxiliary_roles_with_synthetic_compiler(self):
        recipe = dict(id='toy', base=dict(kind='unit'), auxiliary=dict(channel='one', coefficient='1/2',
            envelope=dict(kind='power_amplitude', power='1/7', weight=dict(kind='unit'))))
        search = dict(selected_recipes=[recipe], selections=[
            dict(stratum='signed', family='toy', q=2, b='1/2', finite_log_bound=dict(A='1',eta='1')),
            dict(stratum='endpoint', family='toy', q=3, b='0', finite_log_bound=None)])
        class SyntheticCompiler:
            def __init__(self, maximum):
                self.meter = R.SEARCH.Meter()
            def compile(self, r, N):
                scale = 2 if r['auxiliary'] is not None else 1
                return R.SEARCH.program(r['id']+'_N'+str(N), {2:Q(scale,7), N:Q(-scale,11)})
        with patch.object(R.SEARCH, 'Compiler', SyntheticCompiler):
            batch = R.compile_batch(search, R.SEARCH.FINAL_PARENTS)
            with self.assertRaises(ValueError):
                R.compile_batch(search, (257,389,522))
        self.assertEqual(len(batch['cases']), 6)
        self.assertEqual(len({R.SEARCH.semantic_key(p) for p in batch['programs']}), len(batch['programs']))
        by_id = {p['id']:p for p in batch['programs']}
        for case in batch['cases']:
            self.assertEqual(by_id[case['auxiliary_forcing']]['constant'], '0')
            self.assertFalse(by_id[case['auxiliary_forcing']]['steps'])
            if case['b'] == '0':
                self.assertEqual(case['child'], case['forcing'])
        self.assertTrue(batch['all_programs_compiled_before_norm_evaluation'])
        self.assertFalse(batch['uniform_convergence_proved'])

    def test_signed_vector_and_zero_audit_pipeline(self):
        p = R.SEARCH.program('toy_signed', {2:Q(-1,7), 5:Q(2,11)}, {3:Q(1,13)}, constant='0')
        row = R.audit_one(dict(program=p,H=96))
        self.assertTrue(row['verification']['verified'])
        self.assertFalse(row['verification']['target_zero_guard_available'])
        self.assertFalse(row['verification']['convergence_proved'])
        zero = R.audit_one(dict(program=R.SEARCH.program('zero',{},constant='0'),H=0))
        self.assertEqual(R.interval(zero), (0,0))

    def test_exact_signed_necessity_and_refutation_classification(self):
        def norm(value):
            return dict(verification=dict(global_fixed_norm_squared_lower=str(value),global_fixed_norm_squared_upper=str(value)))
        rows = {k:norm(v) for k,v in dict(parent=4,child=1,forcing=1,baseline_forcing=2,auxiliary_forcing=1).items()}
        case = dict(rule='toy',N=257,q=2,b='1',has_auxiliary=True,
                    **{k:k for k in rows},log_bound=R.log_bound_interval(257,'12','1'))
        outcome = R.analyze_case(case,rows)
        self.assertEqual(outcome['logarithmic_forcing_status'],'verified_at_this_support')
        for kind in ('refinement','auxiliary'):
            self.assertEqual(outcome[kind]['mechanism'],'signed_cross_needed_even_against_diagonal')
            self.assertEqual(outcome[kind]['cross']['upper'],'-2')
        rows['forcing'] = norm(2)
        self.assertEqual(R.analyze_case(case,rows)['logarithmic_forcing_status'],'refuted_at_this_support')
        self.assertFalse(outcome['all_supports_inequality_proved'])

    def test_bound_root_arbitrary_denominator_and_rate_guard(self):
        bound = R.log_bound_interval(257,'2/11','19/257')
        lo, hi = Q(bound['lower'])/Q(2,11), Q(bound['upper'])/Q(2,11)
        self.assertLessEqual(lo**257,Q(1,9)**19)
        self.assertGreater(hi**257,Q(1,9)**19)
        with self.assertRaises(ValueError):
            R.log_bound_interval(257,'1','6/5')


if __name__ == '__main__':
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(RunnerTests))
    record = dict(returncode=0 if result.wasSuccessful() else 1, tests=result.testsRun,
                  failures=len(result.failures), errors=len(result.errors), elapsed_seconds=time.monotonic()-started,
                  exposure='mock compiler for batch partition/dedup; rational synthetic norm96 and exact zero; artificial signed diagnostics')
    path = Path(__file__).with_name('floor_residual_runner_044_development.json')
    receipt = json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1',invocations=[])
    receipt['invocations'].append(record)
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(record))
    raise SystemExit(record['returncode'])
