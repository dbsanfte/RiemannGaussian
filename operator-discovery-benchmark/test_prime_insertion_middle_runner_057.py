"""New integration and adversarial missing-source checks for057."""
from fractions import Fraction as Q
import unittest
import prime_insertion_middle_search_057 as S
import run_prime_insertion_middle_057 as R
import prime_insertion_middle_source_057 as P
import check_prime_insertion_middle_057 as C

SM, PM, CM = S.Meter(), P.Meter(), C.Meter(cap=1_000_000_000, seconds=600)


class IntegrationTests(unittest.TestCase):
    def test_missing_used_source_is_not_zero(self):
        cache = {(0, 7): {'lower': '1', 'upper': '2'}}
        with self.assertRaises(ValueError): R.table_from_cache(cache, [7], 2)
        table = R.table_from_cache(cache, [7], 2, [0])
        self.assertEqual(table[7][1], (Q(0), Q(0)))
        with self.assertRaises(ValueError): R.table_from_cache(cache, [7], 2, [1])

    def test_real_synthetic_middle_and_independent_source(self):
        request = {'alpha': '2/7', 'primes': [7], 'N': 5, 'gamma': '1',
            'lower_fraction': '1/4', 'upper_fraction': '3/4'}
        produced = P.evaluate(request, meter=PM)
        checked = C.verify_middle_interval(request, {k: produced[k] for k in ('lower', 'upper')}, CM)
        self.assertTrue(checked['verified'])
        self.assertLessEqual(Q(produced['lower']), Q(checked['lower']))
        self.assertLessEqual(Q(checked['upper']), Q(produced['upper']))

    def test_parent_recovery_matches_independent_checker(self):
        request = {'alpha': '2/7', 'features': [S.feature([7], '1'), S.feature([3, 7], '2/7', '3/5')],
            'coefficients': [1, -1], 'lambda': '1/3', 'weights': ['2/3', '0', '1/3'], 'delta': '2/11', 'C': '3/7'}
        certificate = S.recovery_certificate(request)
        checked = C.verify_parent_recovery(request, certificate, CM)
        self.assertTrue(checked['verified'])
        self.assertFalse(checked['uniform_middle_bound_proved'])
        program = S.energy_correlations({'coefficients': request['coefficients'], 'lambda': request['lambda']}, request['weights'])
        self.assertEqual(program['weights'], request['weights'])
        self.assertIn('N+s', program['formula'])
        self.assertTrue(program['each_source_uses_its_own_moving_endpoints'])

    def test_transport_comparison_and_final_coverage(self):
        form = {'id': 'control', 'coefficients': [0, 0], 'lambda': '0', 'support': [], 'baseline': True, 'signed_auxiliary': False}
        row = {'id': 'synthetic', 'form': form, 'transport': {'weights': ['0', '1', '0'], 'center_only': True},
            'delta': '0', 'C': '8', 'archive_family': 'target_center_control'}
        needed = R.required_requests([row], [10])
        self.assertEqual(needed, {10: [0], 20: [0], 21: [0]})
        table = {n: [(Q(n), Q(n)), (Q(0), Q(0))] for n in [10, 20, 21]}
        checked = R.check_transition(row, 10, 0, table, table, SM)
        self.assertEqual(checked['status'], 'FINITE_REFUTATION')
        self.assertFalse(checked['RH_refuted'])
        with self.assertRaises(ValueError): R.assessment(row, [checked])
        finals = [dict(checked, N=n, parity=r) for n in R.FINAL for r in (0, 1)]
        assessed = R.assessment(row, finals)
        self.assertEqual(assessed['status'], 'REFUTED_FIXED_RECURRENCE')


if __name__ == '__main__': unittest.main()
