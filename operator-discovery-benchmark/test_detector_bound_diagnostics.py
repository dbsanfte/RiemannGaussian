"""Experimental warnings preserve strong leads and separate proof scope."""
import unittest
from detector_bound_diagnostics import training_diagnostics


class BoundDiagnosticsTests(unittest.TestCase):
    def test_negative_training_does_not_measure_positive_forcing(self):
        rows = [{'X': 2, 'arity': 2, 'energy': 1, 'child_energy': 10},
                {'X': 16, 'arity': 2, 'energy': 76, 'child_energy': 151}]
        result = training_diagnostics({'terms': []}, rows, [16])
        self.assertEqual(result['training_sign_counts']['positive'], 0)
        self.assertEqual(result['training_sign_counts']['negative'], 1)
        self.assertGreater(len(result['evidence_warnings']), 0)
        self.assertFalse(result['candidate_discarded'])
        self.assertFalse(result['unknown_global_claim_disproved'])
        at_two = next(row for row in result['boundary_observations'] if row['X'] == 2)
        self.assertEqual(at_two['innovation'], '3/8')
        self.assertFalse(at_two['included_in_fit'])

    def test_missing_response_is_explicit_not_zero_forcing(self):
        result = training_diagnostics({'terms': []}, [{'X': 8, 'missing': True}], [8])
        self.assertEqual(result['training_sign_counts'], {'positive': 0, 'zero': 0, 'negative': 0})
        self.assertEqual(result['unavailable_training_cases'][0]['status'], 'missing')
        self.assertFalse(result['global_signed_bound_proved'])


if __name__ == '__main__':
    unittest.main()
