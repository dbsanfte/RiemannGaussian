"""Regressions for the unfrozen detector arithmetic safety boundary."""

from fractions import Fraction as Q
import unittest

import detector_safe_evaluation as safe


def term(power='1', weight='1', arity=2, slot=1):
    return {'feature': {'arity': arity, 'slot': slot,
                        'normalizing_power': power}, 'weight': weight}


def rows():
    return [
        {'X': 2, 'arity': 2, 'energy': 1, 'child_energy': 10,
         'component_moments': [{'energy': 7}]},
        {'X': 4, 'arity': 2, 'energy': 10, 'child_energy': 31,
         'component_moments': [{'energy': 4, 'child_energy': 8}]},
        {'X': 8, 'arity': 2, 'energy': 31, 'child_energy': 76,
         'component_moments': [{'energy': 32}]},
    ]


class SafeEvaluationTests(unittest.TestCase):
    def test_missing_normalizer_never_becomes_fraction_energy_none(self):
        ceiling = safe.rational_ceiling(2, '1000001')
        self.assertEqual(ceiling.status, safe.Status.MISSING)
        result = safe.safe_potential({'terms': [term('1000001')]}, rows(), 2)
        self.assertEqual(result.status, safe.Status.MISSING)
        self.assertIsNone(result.value)

    def test_huge_reciprocal_and_full_fractional_power(self):
        self.assertEqual(safe.rational_ceiling(3, Q(1, 10 ** 100)).value, 2)
        self.assertEqual(safe.rational_ceiling(3, 1 + Q(1, 10 ** 100)).value, 4)
        self.assertEqual(safe.rational_ceiling(2, '3/2').value, 3)
        result = safe.safe_potential({'terms': [term('3/2')]}, rows(), 2)
        self.assertEqual(result.value, Q(7, 3))

    def test_moving_cutoff_rows_are_not_replaced_by_child_component(self):
        program = {'terms': [term('1')]}
        self.assertEqual(safe.safe_potential(program, rows(), 4).value, 1)
        self.assertEqual(safe.safe_potential(program, rows(), 8).value, 4)
        self.assertEqual(safe.safe_innovation(program, rows(), 4).value, Q(183, 64))

    def test_unknown_level_is_missing_without_an_invented_constant(self):
        program = {'terms': [], 'fitted_constants': {'3': '1'}}
        result = safe.safe_score_potential(program, rows(), [2], [3, 17])
        self.assertTrue(result.available)
        report = result.value
        self.assertEqual(report['finite_cases'], 1)
        self.assertEqual(report['missing_cases'], 1)
        observation = report['observations'][1]
        self.assertEqual(observation['reason'], 'unknown_level_constant')
        self.assertEqual(observation['signed_innovation'], '3/8')
        self.assertIsNone(observation['bound'])
        self.assertIsNone(observation['margin'])
        self.assertIsNone(observation['finite_pass'])
        self.assertEqual(program['fitted_constants'], {'3': '1'})

    def test_resource_failure_clears_signed_value_and_has_no_pass(self):
        program = {'terms': [term('1000001')], 'fitted_constants': {'3': '1'}}
        report = safe.safe_score_potential(program, rows(), [2], [3]).value
        self.assertEqual(report['missing_cases'], 1)
        self.assertEqual(report['finite_cases'], 0)
        self.assertEqual(report['finite_passes'], 0)
        for key in ('signed_innovation', 'bound', 'margin', 'finite_pass'):
            self.assertIsNone(report['observations'][0][key])
        bound_limited = safe.safe_score_potential(
            {'terms': [], 'fitted_constants': {'1': '1'}}, rows(), [4], [1],
            bit_budget=1).value
        self.assertEqual(bound_limited['missing_cases'], 1)
        self.assertIsNone(bound_limited['observations'][0]['signed_innovation'])

    def test_fit_does_not_drop_unavailable_scales(self):
        program = {'terms': [term('1000001')]}
        result = safe.safe_fit_potential(program, rows(), [2, 4], [3])
        self.assertEqual(result.status, safe.Status.MISSING)
        self.assertIsNone(result.value)
        self.assertNotIn('fitted_constants', program)

    def test_completed_fit_preserves_native_exact_rule(self):
        program = {'terms': []}
        result = safe.safe_fit_potential(program, rows(), [2], [3])
        expected = Q(5, 4) * (Q(3, 8) / 2) + Q(1, 2 ** 64)
        self.assertEqual(result.value['fitted_constants']['3'], str(expected))
        self.assertNotIn('fitted_constants', program)

    def test_valid_zero_weight_is_exactly_zero_without_resource_work(self):
        program = {'terms': [term('1000001', weight='0')]}
        self.assertEqual(safe.safe_potential(program, [], 2).value, 0)
        malformed = {'terms': [term('-1', weight='0')]}
        self.assertEqual(safe.safe_potential(malformed, [], 2).status, safe.Status.INVALID)
        # A zero observed energy does not hide a missing nonzero normalizer.
        zero_energy = [{'X': 2, 'arity': 2, 'component_moments': [{'energy': 0}]}]
        self.assertEqual(safe.safe_potential(
            {'terms': [term('1000001')]}, zero_energy, 2).status, safe.Status.MISSING)

    def test_invalid_domain_and_negative_weights(self):
        for base, exponent in [(True, '1/2'), (2, '-1'), (2, 0.5), (2, 'bad')]:
            self.assertEqual(safe.rational_ceiling(base, exponent).status, safe.Status.INVALID)
        self.assertEqual(safe.safe_potential(
            {'terms': [term(weight='-1')]}, rows(), 2).status, safe.Status.INVALID)

    def test_missing_reconstruction_and_conflicting_actual_rows(self):
        missing = [{'X': 2, 'arity': 2, 'missing': True}]
        self.assertEqual(safe.safe_innovation({'terms': []}, missing, 2).status, safe.Status.MISSING)
        conflicting = rows() + [dict(rows()[0], child_energy=11)]
        self.assertEqual(safe.safe_innovation({'terms': []}, conflicting, 2).status,
                         safe.Status.INVALID)


if __name__ == '__main__':
    unittest.main()
