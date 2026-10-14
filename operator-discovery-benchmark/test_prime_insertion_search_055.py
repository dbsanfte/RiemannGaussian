from copy import deepcopy
from fractions import Fraction as Q
import unittest
import prime_insertion_search_055 as S
import prime_insertion_argument_055 as A


METERS = []
def meter():
    m = S.Meter(); METERS.append(m); return m


class SearchTests(unittest.TestCase):
    def test_grammar_signed_auxiliaries_and_general_fractional_decay(self):
        bank = S.grammar(meter=meter())
        self.assertEqual(bank['form_count'], 397)
        self.assertEqual(bank['bound_candidate_count'], 1985)
        self.assertTrue(any(any(c < 0 for c in row['coefficients']) for row in bank['forms']))
        spec = deepcopy(S.DEFAULT); spec['decay_exponents'] = ['2/11']
        self.assertEqual(S.grammar(spec, meter())['decay_exponents'], ['2/11'])
        spec['features'][1] = [4]
        with self.assertRaises(ValueError): S.grammar(spec, meter())

    def test_energy_encloses_negative_cross_and_zero_crossing(self):
        form = {'coefficients': [2, -3], 'lambda': '1/4'}
        result = S.energy(form, [(Q(-1), Q(2)), (Q(3), Q(4))], 2, meter())
        self.assertEqual(result, (Q(25, 8), Q(53, 2)))
        for x in (Q(-1), Q(0), Q(2)):
            for y in (Q(3), Q(7, 2), Q(4)):
                value = (x*x+Q(1, 4)*(2*x-3*y)**2)/2
                self.assertLessEqual(result[0], value); self.assertLessEqual(value, result[1])
        with self.assertRaises(ValueError): S.energy({'coefficients': [1], 'lambda': '-1'}, [(Q(1), Q(1))], 2, meter())

    def test_cross_polynomial_retains_all_terms(self):
        form = {'coefficients': [2, -3, 1], 'lambda': '1/4'}
        terms = S.drift_polynomial(form)['terms']
        values = [Q(3, 2), Q(-2), Q(5, 3)]
        total = sum(Q(t['coefficient'])*values[t['i']]*values[t['j']] for t in terms)
        direct = values[0]**2+Q(1, 4)*sum(c*v for c, v in zip(form['coefficients'], values))**2
        self.assertEqual(total, direct)
        self.assertTrue(any(Q(t['coefficient']) < 0 for t in terms))

    def test_fitted_training_recurrence_can_fail_at_a_new_scale(self):
        form = {'id': 'synthetic', 'coefficients': [0, 0], 'lambda': '0', 'support': [], 'baseline': True}
        table = {n: [(Q(n), Q(n)), (Q(0), Q(0))] for n in range(2, 10)}
        weights = {'1': {n: (Q(1, n), Q(1, n)) for n in (2, 3)}}
        rows = S.score_form(form, table, [2, 3], weights, list(map(Q, (0, 1, 2, 4, 8, 16))), meter())
        self.assertEqual(rows[0]['C'], '16')
        self.assertFalse(rows[0]['uniform_drift_proved'])
        self.assertEqual(S.assess((Q(5), Q(5)), (Q(4), Q(4))), 'FINITE_REFUTATION')
        self.assertEqual(S.assess((Q(3), Q(5)), (Q(4), Q(4))), 'UNRESOLVED_INTERVAL')

    def test_interval_decay_uses_general_rational_exponent(self):
        lo, hi = S.decay(128, '1/7', meter())
        self.assertLessEqual(lo, Q(1, 2)); self.assertGreaterEqual(hi, Q(1, 2))
        self.assertEqual(S.decay(128, '0', meter()), (Q(1), Q(1)))

    def test_recovery_and_pointwise_attempt_do_not_pay_the_drift(self):
        request = {'alpha': '1/257', 'features': [[], [2]], 'coefficients': [1, -1],
            'lambda': '1/3', 'delta': '1/11', 'C': '2'}
        certificate = A.energy_certificate(request)
        self.assertEqual(Q(certificate['recovery']['constant'])-Q(certificate['base_upper']), 44)
        self.assertEqual(certificate['recurrence']['children'], [0, 1])
        self.assertFalse(certificate['uniform_target_bound_proved'])
        attempt = A.pointwise_proof_attempt(request)
        self.assertEqual(attempt['paid_F_upper']['N_power'], '1')
        self.assertEqual(attempt['requested_drift_N_power'], '-1/11')
        self.assertFalse(attempt['uniform_drift_proved'])

    def test_zero_decay_recovery_retains_binary_logarithm_units(self):
        request = {'alpha': '1/5', 'features': [[], [2]], 'coefficients': [0, 1],
            'lambda': '1', 'delta': '0', 'C': '3'}
        certificate = A.energy_certificate(request)
        self.assertEqual(certificate['recovery']['logarithm_base'], 2)
        self.assertEqual(certificate['recovery']['log_coefficient'], '3')
        self.assertEqual(certificate['recovery']['constant'], certificate['base_upper'])
        self.assertEqual(certificate['recurrence']['status'], 'OPEN')

    def test_tail_provider_leaves_full_target_and_small_parameter_core_open(self):
        empty = A.tail_certificate({'alpha': '1/257', 'primes': [], 'tau': 8})
        mixed = A.tail_certificate({'alpha': '1/5', 'primes': [2, 3], 'tau': 8})
        self.assertEqual(Q(empty['uniform_absolute_upper']), Q(18, 256))
        self.assertEqual(Q(mixed['uniform_absolute_upper']), Q(48, 6**8))
        self.assertTrue(mixed['tail_bound_proved'])
        self.assertFalse(mixed['complete_target_bound_proved'])
        self.assertEqual(mixed['unpaid_core'], '0<t<tau')
        with self.assertRaises(ValueError): A.tail_certificate({'alpha': '1/5', 'primes': [], 'tau': 1})


def tearDownModule(): print('SYNTHETIC_WORK operations='+str(sum(m.operations for m in METERS)))


if __name__ == '__main__': unittest.main()
