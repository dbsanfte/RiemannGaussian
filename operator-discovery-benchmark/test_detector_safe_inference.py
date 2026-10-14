"""Finite-fit regressions exercising dictionary projection and missing arities."""

import unittest
from copy import deepcopy

import inverse_prefix_grammar as grammar
from detector_safe_evaluation import Status
from detector_safe_inference import safe_infer, predict_full


class SafeInferenceTests(unittest.TestCase):
    def test_rank_deficient_constant_fit_keeps_full_vector(self):
        rows = grammar.feature_table(17, 1, [1, 2, 3], [1])['rows']
        before = deepcopy(rows)
        report = safe_infer(rows, [1, 2, 3]).value
        native = report['native_inference_archive']
        self.assertEqual(native, grammar.infer(rows, [1, 2, 3]))
        self.assertFalse(report['macro_eligible'])
        self.assertIsNone(report['macro_candidate'])
        self.assertTrue(all(p['observation']['finite_pass']
                            for p in report['full_weight_predictions']))
        self.assertEqual(native['coefficient_table']['1'], ['0'])
        self.assertTrue(any(r['reason'] == 'noncore_coefficients_present'
                            for r in report['macro_ineligibility_reasons']))
        self.assertEqual(rows, before)
        self.assertGreater(len(native['retained_minimum_support_arity_fits']['1']), 1)

    def test_absent_arity_is_explicit_missing_without_native_index_error(self):
        rows = grammar.feature_table(17, 12, [1], [3, 7, 11])['rows']
        report = safe_infer(rows, [1, 2]).value
        missing = next(r for r in report['arity_outcomes'] if r['arity'] == 2)
        self.assertEqual(missing['status'], 'missing')
        self.assertEqual(missing['reason'], 'no_response_rows')
        self.assertFalse(report['macro_eligible'])
        empty = safe_infer([], [1, 2]).value
        self.assertIsNone(empty['native_inference_archive'])
        self.assertEqual(len(empty['arity_outcomes']), 2)
        huge_missing = safe_infer([], [10 ** 100]).value
        self.assertEqual(huge_missing['arity_outcomes'][0]['reason'], 'no_response_rows')

    def test_inconsistent_response_fit_remains_rejected(self):
        rows = [{'arity': 1, 'columns': [0, 0, 0, 0], 'anonymous_target': 1}]
        report = safe_infer(rows, [1]).value
        self.assertEqual(report['arity_outcomes'][0]['reason'], 'no_exact_fit')
        self.assertEqual(report['full_weight_predictions'][0]['status'], 'missing')
        self.assertFalse(report['macro_eligible'])

    def test_ordinary_generic_fitting_is_core_eligible_but_not_a_theorem(self):
        rows = []
        for seed in [19, 71, 302]:
            rows.extend(grammar.feature_table(seed, 32, [1, 2, 3], [9, 13, 21, 31])['rows'])
        report = safe_infer(rows, [1, 2, 3]).value
        self.assertTrue(report['macro_eligible'])
        self.assertTrue(report['analytical_admission_still_required'])
        self.assertFalse(report['global_reconstruction_proved'])
        model = report['native_inference_archive']
        fresh = grammar.feature_table(411, 40, [3], [17, 37])['rows']
        self.assertTrue(all(predict_full(model, row).value['finite_pass'] for row in fresh))

    def test_prediction_rejects_width_changes_and_unknown_arities(self):
        model = {'learned_vectors': {'1': ['1', '0', '0', '0']}}
        self.assertEqual(predict_full(model, {'arity': 2}).status, Status.MISSING)
        self.assertEqual(predict_full(model, {'arity': 1, 'columns': [1],
                                            'anonymous_target': 1}).status, Status.INVALID)
        self.assertEqual(safe_infer([], [1, 1]).status, Status.INVALID)
        rows = grammar.feature_table(17, 12, [2], [3, 7, 11])['rows']
        report = safe_infer(rows, [2]).value
        self.assertFalse(report['macro_eligible'])
        self.assertTrue(any(reason['reason'] == 'incomplete_core_arity_chain'
                            for reason in report['macro_ineligibility_reasons']))


if __name__ == '__main__':
    unittest.main()
