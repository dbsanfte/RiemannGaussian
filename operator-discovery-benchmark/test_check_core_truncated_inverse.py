"""Tiny exact polynomial/support and independent divisor-pair reconstruction."""
import copy
from fractions import Fraction as Q
from math import isqrt
import unittest
from flint import arb, ctx
import check_core_truncated_inverse as C

TOTAL = 0


class Meter:
    def __init__(self): self.operations = 0; self.peak = 0
    def charge(self, n=1):
        global TOTAL
        if type(n) is not int or n < 0: raise ValueError('strict nonnegative work')
        self.operations += n; TOTAL += n
    def live(self, cells):
        if type(cells) is not int or not 0 <= cells <= 48000000: raise ValueError('resident cap')
        self.peak = max(self.peak, cells)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_truncated_inverse operations=' + str(TOTAL))


def word(alpha='1/2', gamma='1/3', p=1, q=0, terms=None):
    if terms is None: terms = [(0, 0, '1'), (1, 0, '1')]
    return dict(alpha=alpha, gamma=gamma, p=p, q=q,
                terms=[dict(a=a, b=b, coefficient=c) for a, b, c in terms])


def toy_mu(H, meter):
    values = [0] + [1] * H
    for n in range(2, H + 1):
        rest = n; prime = 2; value = 1
        while prime * prime <= rest:
            exponent = 0; meter.charge(2)
            while rest % prime == 0: rest //= prime; exponent += 1; meter.charge(3)
            if exponent > 1: value = 0
            elif exponent == 1: value = -value
            prime += 1; meter.charge()
        if rest > 1: value = -value; meter.charge()
        values[n] = value
    return values


def naive(left, right, meter):
    H = len(left) - 1; result = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        for d in range(1, isqrt(n) + 1):
            meter.charge(2)
            if n % d == 0:
                result[n] += left[d] * right[n // d]; meter.charge(3)
                if d != n // d: result[n] += left[n // d] * right[d]; meter.charge(3)
    return result


def power(values, exponent, meter):
    delta = [arb(0)] * len(values); delta[1] = arb(1)
    for _ in range(exponent): delta = naive(delta, values, meter)
    return delta


class TruncatedInverseTests(unittest.TestCase):
    def setUp(self): ctx.prec = 192; self.meter = Meter()
    def ball(self, a, b): self.assertTrue(a.overlaps(b), (str(a), str(b)))

    def test_exact_residual_boundary_and_all_scale_support(self):
        result = C.verify_certificate(word(), self.meter)
        self.assertEqual(result['residual'], [dict(a=2, b=0, coefficient='-1', weight='1')])
        self.assertTrue(result['exact_all_scale_identity_verified'])
        self.assertTrue(result['actual_mu_inverse_required']); self.assertFalse(result['core_recurrence_proved'])
        self.assertIn('all units', result['domain'])
        # At weight exactly1 the omitted product still strictly exceedsN.
        for N in (1, 3, 16, 31, 63):
            U = C._cutoff(N, Q(1, 2), self.meter)
            self.assertGreater((U + 1) ** 2, N); self.meter.charge(3)

    def test_complete_mixed_inverse_components_by_divisor_pairs(self):
        p = word('1/3', '1/2', 2, 1, [(0, 0, '1'), (0, 1, '1'), (1, 0, '2'), (1, 1, '2'), (2, 0, '3')])
        mu = toy_mu(31, self.meter); result = C.evaluate(mu, p, 31, self.meter)
        self.assertEqual((result['U'], result['V']), (3, 5))
        mub = list(map(arb, mu)); muv = [arb(0)] + [arb(mu[n]) / arb(n) ** (arb(2) / 3) for n in range(1, 32)]; self.meter.charge(31 * 70)
        expected = naive(power(mub, 2, self.meter), muv, self.meter)
        for a, b in zip(result['reference'], expected): self.ball(a, b)
        total = [arb(0)] * 32
        prefactor = naive(power(result['A'], 2, self.meter), result['B'], self.meter)
        for term in result['terms']:
            component = naive(prefactor, naive(power(result['R'], term['a'], self.meter), power(result['S'], term['b'], self.meter), self.meter), self.meter)
            scalar = Q(term['coefficient']); scalar = arb(scalar.numerator) / scalar.denominator; self.meter.charge(3)
            for n in range(32):
                self.ball(term['values'][n], component[n]); total[n] += scalar * component[n]; self.meter.charge(3)
        for n in range(32):
            self.ball(total[n], result['reconstructed'][n]); self.ball(total[n], expected[n])
        self.assertFalse(result['full_signed_bound_proved']); self.assertFalse(result['RH_proved'])

    def test_zero_power_delta_units_and_weighted_prime_powers(self):
        p = word('1/2', '1/3', 0, 2, [(0, 0, '1'), (0, 1, '2'), (0, 2, '3')])
        mu = toy_mu(15, self.meter); result = C.evaluate(mu, p, 15, self.meter)
        for n, integer in ((1, 1), (2, -2), (4, 1), (8, 0), (6, 4), (9, 1)):
            expected = arb(integer) / arb(n) ** (arb(2) / 3); self.meter.charge(70)
            self.ball(result['reference'][n], expected); self.ball(result['reconstructed'][n], expected)
        one = C.evaluate([0, 1], p, 1, self.meter)
        self.assertEqual((one['U'], one['V']), (1, 1)); self.ball(one['reconstructed'][1], arb(1))
        self.assertTrue(one['R'][1].is_zero()); self.assertTrue(one['S'][1].is_zero())

    def test_exact_fractional_cutoffs_and_support_zeroes(self):
        p = word('2/3', '1/2'); mu = toy_mu(63, self.meter)
        result = C.evaluate(mu, p, 63, self.meter)
        self.assertEqual((result['U'], result['V']), (15, 7))
        for n in range(1, 16): self.assertTrue(result['R'][n].is_zero())
        for n in range(1, 8): self.assertTrue(result['S'][n].is_zero())
        self.assertTrue(result['A'][16].is_zero()); self.assertTrue(result['B'][8].is_zero())
        self.assertEqual(C._cutoff(64, Q(2, 3), self.meter), 16)
        self.assertEqual(C._cutoff(63, Q(1, 3), self.meter), 3)
        with self.assertRaises(RuntimeError): C._cutoff(31, Q(1, 1000), self.meter)

    def test_forged_inverse_and_omitted_strict_boundary_rejected(self):
        forged = word(terms=[(0, 0, '1'), (1, 0, '2')])
        with self.assertRaises(ValueError): C.verify_certificate(forged, self.meter)
        with self.assertRaises(ValueError): C.verify_certificate(word(terms=[(1, 0, '1')]), self.meter)
        with self.assertRaises(ValueError): C.verify_certificate(word(terms=[(0, 0, '1'), (1, 0, '1'), (2, 0, '1')]), self.meter)
        with self.assertRaises(ValueError): C.verify_certificate(word(terms=[(0, 0, '1'), (0, 0, '1'), (1, 0, '1')]), self.meter)
        with self.assertRaises(ValueError): C.verify_certificate(word(terms=[(0, 0, '1'), (1, 0, '0')]), self.meter)
        valid = word('2/3', '2/3', 2, 2, [(0, 0, '1'), (1, 0, '2'), (0, 1, '2')])
        cert = C.verify_certificate(valid, self.meter)
        self.assertTrue(all(Q(term['weight']) >= 1 for term in cert['residual']))

    def test_mu_counterfeit_square_unit_and_horizon_rejected(self):
        mu = toy_mu(31, self.meter)
        for n, value in ((1, -1), (4, 1), (17, 1), (0, 1), (3, True)):
            bad = list(mu); bad[n] = value
            with self.subTest(n=n), self.assertRaises(ValueError): C.evaluate(bad, word(), 31, self.meter)
        with self.assertRaises(ValueError): C.evaluate(mu[:-1], word(), 31, self.meter)
        with self.assertRaises(ValueError): C.evaluate(mu, word(), True, self.meter)
        with self.assertRaises(ValueError): C.evaluate([0], word(), 0, self.meter)

    def test_strict_ast_and_canonical_fraction_types(self):
        invalid = []
        for key, value in (('alpha', '0'), ('gamma', '1'), ('alpha', '2/4'), ('alpha', 0.5), ('p', True), ('q', 3)):
            p = word(); p[key] = value; invalid.append(p)
        invalid.append(word(p=0, q=0)); invalid.append(word(terms=[]))
        for key, value in (('a', -1), ('b', True), ('coefficient', '2/2')):
            p = word(); p['terms'][0][key] = value; invalid.append(p)
        p = word(); p['id'] = 0; invalid.append(p)
        p = word(); p['terms'][0]['weight'] = '0'; invalid.append(p)
        for p in invalid:
            with self.subTest(p=p), self.assertRaises(ValueError): C.verify_certificate(p, self.meter)
        ctx.prec = 128
        with self.assertRaises(ValueError): C.evaluate([0, 1], word(), 1, self.meter)
        ctx.prec = 192

    def test_large_formal_powers_zero_by_support_and_shared_meter(self):
        values = [arb(0), arb(0), arb(1), arb(-1), arb(1), arb(0), arb(0), arb(0)]
        before = self.meter.operations
        result = C._power(values, 10 ** 100, 7, self.meter, 1)
        self.assertTrue(all(v.is_zero() for v in result)); self.assertEqual(self.meter.operations - before, 1)
        C.evaluate(toy_mu(7, self.meter), word(), 7, self.meter)
        self.assertGreater(self.meter.operations, before); self.assertGreater(self.meter.peak, 0)


if __name__ == '__main__': unittest.main()
