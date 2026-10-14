"""Owned synthetic/exact tests; running this file writes its metered receipt."""
from fractions import Fraction as F
import json
from pathlib import Path
import time
import unittest

import finite_prime_obstruction_042 as producer

METERS = []


def meter(**kwargs):
    value = producer.Meter(**kwargs)
    METERS.append(value)
    return value


class FinitePrimeObstructionTests(unittest.TestCase):
    def setUp(self):
        self.meter = meter()

    def test_local_h_divisor_difference_all_valuations(self):
        for v in (F(1, 2), F(2, 3), F(1, 257)):
            previous = F(0)
            for e in range(10):
                u = F(1) if e == 0 else (v-1)*v**(e-1)
                self.assertEqual(producer.synthetic_local_h(v, e, self.meter), u-previous)
                previous = u

    def test_local_l1_norm_geometric_tail(self):
        for v in (F(1, 2), F(2, 3), F(1, 257)):
            N = 8
            partial = sum(abs(producer.synthetic_local_h(v, e, self.meter)) for e in range(N+1))
            tail = (1-v)*v**(N-1)
            self.assertEqual(partial+tail, 4-2*v)
            self.assertLessEqual(partial+tail, 4)

    def test_multiplicative_divisor_identity(self):
        values = {2: F(1, 2), 3: F(2, 3)}
        for n in range(1, 101):
            u = producer.synthetic_u(n, values, self.meter)
            divisor_sum = sum(producer.synthetic_h(d, values, self.meter)
                              for d in range(1, n+1) if n % d == 0)
            self.assertEqual(u, divisor_sum)
            self.assertLessEqual(abs(u), 1)
        self.assertEqual(producer.synthetic_u(1, values, self.meter), 1)
        self.assertEqual(producer.synthetic_u(7**3, values, self.meter), 1)
        self.assertEqual(producer.synthetic_h(7, values, self.meter), 0)

    def test_registered_prime_laws_with_unregistered_factors(self):
        values = {2: F(1, 2), 3: F(2, 3)}
        for p, v in values.items():
            for n in range(1, 61):
                u = producer.synthetic_u(n, values, self.meter)
                expected = (v if n % p == 0 else v-1)*u
                self.assertEqual(producer.synthetic_u(p*n, values, self.meter), expected)

    def test_periodic_divisor_prefix_and_bound(self):
        values = {2: F(1, 2), 3: F(2, 3)}
        for q in (2, 5, 6):
            L = (q+1)*4**len(values)
            for x in (F(0), F(1, 2), F(1), F(7, 3), F(16), F(101, 3)):
                N = x.numerator//x.denominator
                c_sum = sum(producer.synthetic_u(n, values, self.meter)
                            -(q*producer.synthetic_u(n//q, values, self.meter) if n % q == 0 else 0)
                            for n in range(1, N+1))
                g_floor_sum = F(0)
                for d in range(1, N+1):
                    g = producer.synthetic_h(d, values, self.meter)
                    if d % q == 0:
                        g -= q*producer.synthetic_h(d//q, values, self.meter)
                    g_floor_sum += g*(x.numerator//(x.denominator*d))
                self.assertEqual(c_sum, g_floor_sum)
                self.assertLessEqual(abs(c_sum), L)

    def test_exact_harmonic_moment_cancelled(self):
        values = {2: F(1, 2), 3: F(2, 3)}
        H_one = F(1)
        for p, v in values.items():
            t = F(1, p)
            H_one *= (1-t)**2/(1-v*t)
            self.meter.charge(12)
        for q in (2, 5, 6):
            self.assertEqual((1-F(q, q))*H_one, 0)

    def test_minimal_exact_dyadic_thresholds(self):
        for theta, k, L in (('2/3', '1/10', 48), ('256/257', '1/17', 48),
                            ('258/259', '3/8', 1), ('2/3', '100', 3)):
            t = producer.dyadic_threshold(theta, k, L, self.meter)
            a, b = F(theta).numerator, F(theta).denominator
            ratio, X = F(k)/(2*L), int(t['X'])
            self.assertEqual(X, 1 << t['j'])
            self.assertGreaterEqual(ratio**b*X**a, 1)
            if t['j']:
                self.assertLess(ratio**b*(X//2)**a, 1)
            self.assertEqual(int(t['lhs']), int(t['powered_numerator'])*X**a)
            self.assertEqual(int(t['rhs']), int(t['powered_denominator']))

    def test_certificate_empty_set_and_unregistered_period(self):
        for P, q, missing in (([], 2, 2), ([2, 3], 5, 5), ([5, 2], 2, 3)):
            cert = producer.generate_certificate(P, q=q, meter=self.meter)
            self.assertEqual(cert['parameters']['primes'], sorted(P))
            self.assertEqual(cert['first_missing_prime']['prime'], missing)
            self.assertEqual(cert['norms']['h_l1_upper'], str(4**len(P)))
            self.assertEqual(cert['norms']['g_l1_upper'], str((q+1)*4**len(P)))
            json.dumps(cert)

    def test_certificate_denominator257_and_source_scope(self):
        cert = producer.generate_certificate([2, 3, 5, 7], '1/257', 2, '1/17', 1, self.meter)
        self.assertEqual(cert['parameters']['theta'], '256/257')
        self.assertEqual(cert['energy_obstruction']['exponent'], '255/257')
        self.assertEqual(cert['energy_obstruction']['lower_constant'], '1/1156')
        self.assertEqual(cert['first_missing_prime']['prime'], 11)
        self.assertEqual(cert['quantifier'], 'for any fixed finite set P of distinct actual primes')
        self.assertFalse(cert['source_scope']['retains_actual_global_meromorphic_identity'])
        self.assertFalse(cert['source_scope']['retains_actual_center_as_its_own_residue'])
        self.assertFalse(cert['source_scope']['fake_periodic_has_theta_pole'])
        self.assertTrue(cert['source_scope']['excluded_by_actual_all_prime_source_binding'])
        for name in ('source_counterexample', 'covariance_bound_proved', 'actual_all_prime_bound_proved',
                     'RH_proved', 'RH_refuted', 'actual_source_values_generated', 'actual_normalization_evaluated'):
            self.assertFalse(cert[name])
        self.assertTrue(cert['assumptions']['scalar_bounds_require_independent_verification'])

    def test_reject_nonprime_duplicate_and_bad_parameters(self):
        for P in ([1], [4], [2, 2], [True], [2.0], '2'):
            with self.assertRaises(ValueError):
                producer.generate_certificate(P, meter=self.meter)
        for kwargs in ({'r_text': '0'}, {'r_text': '1/2'}, {'r_text': '2/6'},
                       {'q': True}, {'q': 1}, {'k_text': '0'}, {'k_text': '2'},
                       {'k_text': 0.1}, {'K': 0}, {'K': 1.0}):
            with self.assertRaises(ValueError):
                producer.generate_certificate([2], meter=self.meter, **kwargs)

    def test_resource_rejection_before_large_powers(self):
        with self.assertRaises(OverflowError):
            producer.generate_certificate([2], meter=meter(cap=0))
        with self.assertRaises(OverflowError):
            producer.dyadic_threshold('1/1000000', '1/10', 3, self.meter)
        with self.assertRaises(OverflowError):
            producer.validate_primes([2**127-1], self.meter)
        with self.assertRaises(ValueError):
            producer.synthetic_local_h(F(1, 2), True, self.meter)
        with self.assertRaises(ValueError):
            producer.synthetic_u(2, {2: 0.5}, self.meter)


if __name__ == '__main__':
    started = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(FinitePrimeObstructionTests)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    invocation = {'returncode': 0 if result.wasSuccessful() else 1,
                  'tests': result.testsRun, 'failures': len(result.failures), 'errors': len(result.errors),
                  'elapsed_seconds': time.monotonic()-started,
                  'operations': sum(m.operations for m in METERS),
                  'peak_integer_bits': max(m.peak_integer_bits for m in METERS),
                  'source_exposure': 'synthetic injected rational locals and formal exact certificates only'}
    receipt_path = Path(__file__).with_name('finite_prime_obstruction_042_development.json')
    receipt = json.loads(receipt_path.read_text()) if receipt_path.exists() else {
        'schema': 'finite-prime-obstruction-development-v1', 'invocations': [],
        'actual_source_generated': False, 'actual_normalization_evaluated': False,
        'old_suites_or_studies_rerun': False, 'hashes_generated': False}
    receipt['invocations'].append(invocation)
    receipt['cumulative_operations'] = sum(run['operations'] for run in receipt['invocations'])
    receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
    raise SystemExit(invocation['returncode'])
