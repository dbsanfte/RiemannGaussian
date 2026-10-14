"""Meaningful rejection tests for the independent analytical certificate gate."""
import copy
import unittest

from check_candidate_reviews import actual_arithmetic, endpoint_certificate

C = '1478554275663870691771/45950839487610493075456'
MARGIN = '-64490596404424127537871/11487709871902623268864'


def example():
    program = {'arithmetic_model': 'inverse_one',
               'exponent_schedule': {'kind': 'power', 'power': '1'},
               'constant_law': {'kind': 'constant'},
               'log_power': '0', 'fitted_coefficient': C}
    certificate = {'kind': 'fixed_dyadic_constant_endpoint', 'X': 2,
                   'parameter_threshold': 1, 'A_X': 1, 'A_2X': 10,
                   'Delta': 6, 'Q_4X': 6, 'root_ceiling': 2,
                   'log_ceiling': 1, 'constant_endpoint': C,
                   'half_gap_margin': MARGIN}
    return program, certificate


class CertificateContracts(unittest.TestCase):
    def test_actual_signed_arithmetic_and_discrete_endpoints(self):
        row = actual_arithmetic(2)
        self.assertEqual(row['mu'][1:], [1, -1, -1, 0, -1, 1, -1, 0])
        self.assertEqual(row['M'][1:], [1, 0, -1, -1, -2, -1, -2, -2])
        self.assertEqual([row[k] for k in ['A_X', 'A_2X', 'Delta', 'Q_4X']], [1, 10, 6, 6])

    def test_all_parameter_disproof_covers_different_schedules(self):
        p, c = example()
        for s in [{'kind': 'power', 'power': '1/6'}, {'kind': 'power', 'power': '2'},
                  {'kind': 'exponential', 'power': '1/2'}, {'kind': 'factorial'}]:
            p['exponent_schedule'] = s
            with self.subTest(s=s):
                self.assertTrue(endpoint_certificate(p, c)['covers_every_later_parameter'])

    def test_forged_actual_arithmetic_rejected(self):
        p, c = example()
        for field in ['A_X', 'A_2X', 'Delta', 'Q_4X']:
            wrong = copy.deepcopy(c)
            wrong[field] += 1
            with self.subTest(field=field), self.assertRaises(AssertionError):
                endpoint_certificate(p, wrong)

    def test_changed_coefficient_or_margin_rejected(self):
        p, c = example()
        c['half_gap_margin'] = '-6'
        with self.assertRaises(AssertionError):
            endpoint_certificate(p, c)
        p, c = example()
        p['fitted_coefficient'] = '1/4'
        with self.assertRaises(AssertionError):
            endpoint_certificate(p, c)

    def test_growing_constant_finite_failure_not_global_certificate(self):
        p, c = example()
        p['constant_law'] = {'kind': 'power', 'power': '1/3'}
        with self.assertRaises(AssertionError):
            endpoint_certificate(p, c)

    def test_free_per_level_fits_do_not_establish_cofinal_failure(self):
        p, c = example()
        p['constant_law'] = {'kind': 'free_per_level'}
        p['fitted_constants'] = {'2': C}
        with self.assertRaises(AssertionError):
            endpoint_certificate(p, c)

    def test_non_dyadic_witness_and_unproved_parameter_threshold_rejected(self):
        p, c = example()
        c['X'] = 3
        with self.assertRaises(AssertionError):
            endpoint_certificate(p, c)
        p, c = example()
        c['parameter_threshold'] = 0
        with self.assertRaises(AssertionError):
            endpoint_certificate(p, c)

    def test_satisfied_endpoint_does_not_refute_candidate(self):
        p, c = example()
        p['fitted_coefficient'] = c['constant_endpoint'] = '1/2'
        c['half_gap_margin'] = '0'
        with self.assertRaises(AssertionError):
            endpoint_certificate(p, c)


if __name__ == '__main__':
    unittest.main()
