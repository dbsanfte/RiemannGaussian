"""Synthetic exact proof-rule tests; no candidate response tables."""
from copy import deepcopy
from fractions import Fraction as Q
import itertools
import json
from pathlib import Path
import time
import unittest

import fractional_prime_kernel_051 as P

METER = P.Meter(cap=2_000_000)


def request(a='2/3', alpha='7/11', sign=-1):
    return dict(a=a, b=str(1-Q(a)), alpha=alpha, sign=sign)


def abstract_kernel(req, logs, exponents):
    a, b, power = Q(req['a']), Q(req['b']), int(req['alpha'])
    total = sum(x*e for x, e in zip(logs, exponents))
    result = Q(0)
    for bits in itertools.product((0, 1), repeat=len(logs)):
        divisor = sum(x*e for x, e in zip(logs, bits))
        result += (-1)**sum(bits)*(a*divisor+b*(total-divisor))**power
    return req['sign']*result


class KernelProofTests(unittest.TestCase):
    def test_fractional_scope_all_indices_all_powers_but_no_rh_recovery(self):
        cert = P.build_certificate(request(alpha='13/29'), METER)
        self.assertEqual(cert['status'], 'PAID_UNIFORM_POINTWISE_CONTROL')
        self.assertEqual(cert['branch'], 'fractional_forward')
        self.assertTrue(cert['nonnegative_for_all_n'])
        self.assertTrue(cert['identity']['normalizer_finite_positive'])
        for key in ('RH_proved', 'RH_refuted', 'original_floor_energy_bound_proved',
                    'prime_distribution_bound_proved', 'analytic_continuation_proved'):
            self.assertIs(cert[key], False)
        self.assertEqual(cert['zeta_bridge']['domain'], 'Re(s)>1')

    def test_zero_offset_cannot_use_derivative_product_bound(self):
        cert = P.build_certificate(request(a='1', alpha='2/7'), METER)
        self.assertIsNone(cert['product_bound'])
        self.assertEqual(cert['upper_bound']['offset_coefficient'], '0')
        self.assertEqual(cert['upper_bound']['step_coefficient'], '1')

    def test_exponential_prime_count_gate_is_exact_and_not_universal(self):
        for a, expected in [('3/5', True), ('3/4', False), ('4/5', False)]:
            cert = P.build_certificate(request(a=a), METER)
            self.assertIs(cert['product_bound']['exponential_omega_decay'], expected)
            self.assertEqual(Q(cert['product_bound']['omega_ratio']), (2*Q(a)-1)/(2*(1-Q(a))))

    def test_derivative_coefficient_for_unrestricted_rational_exponents(self):
        self.assertEqual(P.derivative_coefficient('1/2', 1, METER), '1/2')
        self.assertEqual(P.derivative_coefficient('1/2', 4, METER), '15/16')
        a = Q(13, 29)
        expected = a
        for j in range(1, 6): expected *= j-a
        self.assertEqual(Q(P.derivative_coefficient(str(a), 6, METER)), expected)
        with self.assertRaises(ValueError): P.derivative_coefficient('1', 2, METER)

    def test_linear_endpoint_exact_on_abstract_prime_power_cubes(self):
        logs = list(map(Q, [2, 3, 5]))
        for a, sign in [('2/3', -1), ('1/3', 1)]:
            req = request(a=a, alpha='1', sign=sign)
            cert = P.build_certificate(req, METER)
            c = abs(Q(req['a'])-Q(req['b']))
            self.assertEqual(cert['identity']['coefficient'], str(c))
            for k in range(1, 4):
                for exponents in itertools.product((1, 2, 5), repeat=k):
                    expected = c*logs[0] if k == 1 else 0
                    self.assertEqual(abstract_kernel(req, logs[:k], exponents), expected)

    def test_quadratic_positive_decomposition_retains_prime_power_valuations(self):
        req = request(a='2/7', alpha='2', sign=1)
        cert = P.build_certificate(req, METER)
        self.assertEqual(cert['branch'], 'quadratic_backward')
        c, b = Q(3, 7), Q(5, 7)
        logs = list(map(Q, [2, 3, 5]))
        for k in range(1, 4):
            for exponents in itertools.product((1, 3, 7), repeat=k):
                expected = (c*(2*b*exponents[0]-c)*logs[0]**2 if k == 1 else
                            2*c*c*logs[0]*logs[1] if k == 2 else Q(0))
                value = abstract_kernel(req, logs[:k], exponents)
                self.assertEqual(value, expected)
                self.assertLessEqual(value, c*sum(x*e for x, e in zip(logs[:k], exponents))**2)

    def test_every_nonpositive_branch_has_an_exact_structural_witness(self):
        cases = [(request(sign=1), 2), (request(alpha='3/2'), 6),
                 (request(a='1/3', sign=1), 6), (request(a='1/3', alpha='3/2', sign=1), 30)]
        for req, n in cases:
            cert = P.build_certificate(req, METER)
            self.assertEqual(cert['status'], 'REFUTED_UNIFORM_NONNEGATIVITY')
            self.assertEqual(cert['witness']['n'], n)
            self.assertTrue(cert['witness']['exact_sign_proved'])
            self.assertFalse(cert['witness']['numerical_evaluation_required'])
            self.assertFalse(cert['RH_refuted'])

    def test_input_and_work_guards(self):
        for key, value in [('alpha', '0'), ('alpha', '5/2'), ('alpha', '2/4'),
                           ('sign', True), ('sign', 0), ('b', '1/7')]:
            req = request(); req[key] = value
            with self.assertRaises(ValueError): P.build_certificate(req, METER)
        with self.assertRaises(ValueError): P.build_certificate(request(a='1/2'), METER)
        with self.assertRaises(OverflowError): P.build_certificate(request(), P.Meter(cap=0))


if __name__ == '__main__':
    path = Path(__file__).with_name('fractional_prime_kernel_051_development.json')
    if path.exists(): raise SystemExit('preserve proof development receipt')
    start = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(KernelProofTests))
    receipt = dict(schema='fractional-prime-proof-development-v1', invocations=[dict(
        returncode=0 if result.wasSuccessful() else 1, tests=result.testsRun,
        failures=len(result.failures), errors=len(result.errors), operations=METER.operations,
        elapsed_seconds=time.monotonic()-start)],
        scope='synthetic proof schemas, abstract prime-log polynomial cubes, gates; no actual candidate table')
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
