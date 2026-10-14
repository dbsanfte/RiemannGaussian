import copy
import unittest

import publish_cancellation_parametric_source_identities as P


class PublicationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inputs = P.load_inputs()

    def test_actual_archive_and_filename_bindings(self):
        self.assertEqual(self.inputs['review']['formal_identities_verified'], 74)
        self.assertIn('recipes.json', self.inputs['review']['input_sha256'])
        self.assertNotIn('recipes', self.inputs['review']['input_sha256'])

    def test_scope_cannot_be_promoted(self):
        for field in ('RH_proved', 'global_bound_proved', 'inequality_proved', 'full_target_proved'):
            review = copy.deepcopy(self.inputs['review'])
            review[field] = True
            with self.assertRaises(ValueError):
                P.validate_outcome(review, self.inputs['execution'])

    def test_incomplete_outcome_rejected(self):
        review = copy.deepcopy(self.inputs['review'])
        review['results'].pop()
        with self.assertRaises(ValueError):
            P.validate_outcome(review, self.inputs['execution'])

    def test_missing_full_compiler_gap_cannot_be_hidden(self):
        review = copy.deepcopy(self.inputs['review'])
        review['full_source_compiler_equivalence_formally_proved'] = True
        with self.assertRaises(ValueError):
            P.validate_outcome(review, self.inputs['execution'])

    def test_failed_certificate_or_deadline_cannot_promote(self):
        execution = copy.deepcopy(self.inputs['execution'])
        execution['cost']['elapsed_seconds'] = 301
        with self.assertRaises(ValueError):
            P.validate_outcome(self.inputs['review'], execution)
        review = copy.deepcopy(self.inputs['review'])
        review['results'][0]['FORMAL_EQ_verified'] = False
        execution = copy.deepcopy(self.inputs['execution'])
        execution['results'] = review['results']
        with self.assertRaises(ValueError):
            P.validate_outcome(review, execution)

    def test_report_retains_scope_and_open_obligations(self):
        report = P.report(self.inputs)
        self.assertFalse(report['global_bound_proved'])
        self.assertFalse(report['full_source_compiler_equivalence_formally_proved'])
        self.assertEqual(report['supplied_recipe_instances'], 74)
        self.assertIn('1/6', report['generic_rational_root_calibration'])
        self.assertNotIn('1/6', report['ordinary_source_cut_parameters'])
        self.assertGreaterEqual(len(report['remaining_obligations']), 4)


if __name__ == '__main__':
    unittest.main()
