"""Independent tiny finite-ball tests; no producer imports or study arithmetic."""
from fractions import Fraction as Q
import unittest

from flint import arb, ctx
import check_shifted_quotient_candidates as C

METERS = []


class Meter:
    def __init__(self, cap=2000000):
        self.operations = 0; self.cap = cap; self.peak_cells = 0
        METERS.append(self)

    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('exact nonnegative charge')
        if n > self.cap - self.operations: raise OverflowError('synthetic operation cap')
        self.operations += n

    def live(self, cells):
        self.charge(); self.peak_cells = max(self.peak_cells, cells)
        if cells > 6000000: raise MemoryError('synthetic resident cap')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_shifted_quotient_candidates operations=' +
          str(sum(m.operations for m in METERS)))


def real(b, meter):
    meter.charge(3)
    return arb(b.numerator) / b.denominator


def manual_atom(b, q, meter):
    # Intentionally trial ALL possible divisors, unlike the checker SPF path.
    out = [arb(0)] * len(q)
    exponent = real(-b, meter)
    for n in range(2, len(q)):
        value = arb(0)
        for d in range(1, n + 1):
            meter.charge()
            if n % d: continue
            meter.charge(C.POWER_WORK + 4)
            value += q[d] * arb(n // d) ** exponent
        meter.charge(4)
        out[n] = value / real(b, meter)
    return out


def manual_convolution(left, right, meter):
    out = [arb(0)] * len(left)
    for n in range(1, len(left)):
        for d in range(1, n + 1):
            meter.charge()
            if n % d == 0:
                meter.charge(2); out[n] += left[d] * right[n // d]
    return out


def manual_normalizer(shifts, meter):
    result = []
    for i, b in enumerate(shifts):
        meter.charge(C.ZETA_WORK + 4)
        z = real(1 - b, meter).zeta()
        residue = 1 / (real(b, meter) * z)
        for j, other in enumerate(shifts):
            if i == j: continue
            meter.charge(C.ZETA_WORK + 4)
            residue *= (real(1 - b + other, meter).zeta() - z) / (real(other, meter) * z)
        meter.charge(2)
        result.append(dict(shift=str(b), residue=residue, coefficient=residue / real(1 - b, meter)))
    return result


class ShiftedCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old_precision = ctx.prec; ctx.prec = 192

    @classmethod
    def tearDownClass(cls): ctx.prec = cls.old_precision

    def test_strict_program_schema_and_numeric_order(self):
        self.assertEqual(C.validate({'shifts': ['1/12', '1/6', '5/6']}), (Q(1, 12), Q(1, 6), Q(5, 6)))
        for p in ({}, {'shifts': [], 'extra': 1}, {'shifts': []}, {'shifts': ['0']}, {'shifts': ['1']},
                  {'shifts': ['-1/6']}, {'shifts': ['2/12']}, {'shifts': ['1/25']},
                  {'shifts': ['1/6', '1/6']}, {'shifts': ['1/3', '1/6']}, {'shifts': [True]},
                  {'shifts': ['1/6'] * 4}, {'shifts': ['1/0']}, {'shifts': [' ' + '1/6']},
                  {'shifts': ['1' * 33 + '/24']}):
            with self.assertRaises(ValueError): C.validate(p)

    def test_factorized_sources_and_control_counterfeit(self):
        m = Meter(); mu = C.source('mu', 63, m); partial = C.source('partial_prime_13', 63, m)
        one = C.source('one', 63, m)
        for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61):
            self.assertEqual(mu[p], -1); self.assertEqual(partial[p], -1 if p <= 13 else 1)
        self.assertEqual((mu[1], mu[4], mu[6], mu[34]), (1, 0, 1, 1))
        self.assertEqual((partial[17], partial[34], partial[49]), (1, -1, 0))
        self.assertEqual(one, [0] + [1] * 63)
        self.assertEqual(mu[:17], partial[:17]); self.assertNotEqual(mu[17], partial[17])
        for H in (True, 0, -1, 262144):
            with self.assertRaises(ValueError): C.source('mu', H, m)
        for name in ('MU', 'counterfeit_mu', 1):
            with self.assertRaises(ValueError): C.source(name, 15, m)

    def test_arbitrary_signed_q_complete_divisor_formula(self):
        m = Meter(); q = [0, 1, 1, -1, 0, 1, -1, 0, 1, 0, -1, 1, -1, 1, 0, 1]
        p = {'shifts': ['1/6', '1/2']}
        state = C.evaluate(p, q, m)
        left = manual_atom(Q(1, 6), q, m); right = manual_atom(Q(1, 2), q, m)
        expected = manual_convolution(left, right, m)
        self.assertEqual(set(state), {'coefficients', 'centered', 'absolute', 'normalizer'})
        for actual, reference in zip(state['coefficients'], expected):
            self.assertTrue(actual.overlaps(reference))
        self.assertTrue(state['coefficients'][0].is_zero()); self.assertTrue(state['coefficients'][1].is_zero())
        self.assertTrue(state['coefficients'][2].is_zero()); self.assertTrue(state['coefficients'][3].is_zero())
        for reference, actual in zip(manual_normalizer((Q(1, 6), Q(1, 2)), m), state['normalizer']):
            self.assertTrue(reference['residue'].overlaps(actual['residue']))
            self.assertTrue(reference['coefficient'].overlaps(actual['coefficient']))

    def test_single_kernel_zero_unit_and_whole_signed_mainterm(self):
        m = Meter(); p = {'shifts': ['1/3']}; one = [0] + [1] * 15
        state = C.evaluate(p, one, m); expected = manual_atom(Q(1, 3), one, m)
        for a, b in zip(state['coefficients'], expected): self.assertTrue(a.overlaps(b))
        coefficient = state['normalizer'][0]['coefficient']
        self.assertTrue(coefficient < 0)
        self.assertTrue(state['centered'][1].overlaps(-coefficient))
        self.assertTrue(state['absolute'][1].overlaps(abs(coefficient)))
        # The signed main term is subtracted as a whole, never clipped to0.
        self.assertTrue(state['centered'][2] > state['coefficients'][2])
        mu_state = C.evaluate(p, C.source('mu', 15, m), m)
        self.assertTrue(coefficient.overlaps(mu_state['normalizer'][0]['coefficient']))

    def test_full_moments_and_absolute_channels_manual(self):
        m = Meter(); p = {'shifts': ['1/6', '1/3', '1/2']}; values = [0] + [1] * 15
        state = C.evaluate(p, values, m)
        prefix = abs_prefix = arb(0); signed = [arb(0)] * 16; envelope = [arb(0)] * 16
        rows = manual_normalizer(tuple(map(Q, p['shifts'])), m)
        for n in range(1, 16):
            m.charge(2); prefix += state['coefficients'][n]; abs_prefix += abs(state['coefficients'][n])
            main = abs_main = arb(0)
            for row in rows:
                m.charge(C.POWER_WORK + 4)
                power = arb(n) ** real(1 - Q(row['shift']), m)
                main += row['coefficient'] * power; abs_main += abs(row['coefficient']) * power
            m.charge(2); signed[n] = prefix - main; envelope[n] = abs_prefix + abs_main
        actual = C.moments(state, [3, 4, 8], m)
        for row in actual:
            X = row['X']; E = A = arb(0)
            for n in range(X, 2 * X):
                m.charge(4); E += signed[n] ** 2; A += envelope[n] ** 2
            m.charge(2)
            self.assertTrue(row['energy'].overlaps(E / (X * X)))
            self.assertTrue(row['absolute_energy'].overlaps(A / (X * X)))
        # Plain public mappings need no producer helper/private memo and retain
        # each absolute normalizer channel independently.
        plain = dict(state); plain.pop('absolute')
        rebuilt = C.moments(plain, [4], m)[0]
        self.assertTrue(rebuilt['energy'].overlaps(actual[1]['energy']))
        self.assertTrue(rebuilt['absolute_energy'].overlaps(actual[1]['absolute_energy']))

    def test_correct_lag_matched_baseline_all_three_degrees(self):
        m = Meter(); mu = [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1]
        atom = list(map(arb, mu)); atom[1] = arb(0); expected = atom
        for degree in (1, 2, 3):
            if degree > 1: expected = manual_convolution(expected, atom, m)
            state = C.baseline(degree, 15, m)
            prefix = abs_prefix = arb(0)
            for n in range(16):
                self.assertTrue(state['coefficients'][n].contains(expected[n]))
                m.charge(2); prefix += expected[n]; abs_prefix += abs(expected[n])
                self.assertTrue(state['centered'][n].contains(prefix))
                self.assertTrue(state['absolute'][n].contains(abs_prefix))
            self.assertEqual(state['normalizer'], [])
            self.assertTrue(state['coefficients'][1].is_zero())
            if degree >= 2: self.assertTrue(state['coefficients'][3].is_zero())
            self.assertEqual(len(C.moments(state, [4, 8], m)), 2)
        self.assertTrue(C.baseline(3, 15, m)['coefficients'][8].contains(-1))

    def test_mainterm_center_and_envelope_tampering(self):
        m = Meter(); state = C.evaluate({'shifts': ['1/3']}, [0] + [1] * 15, m)
        def clone():
            # Arb values are immutable arithmetic objects without a pickle
            # reducer; copy containers, then replace the intended field.
            return C.State(coefficients=list(state['coefficients']), centered=list(state['centered']),
                           absolute=list(state['absolute']), normalizer=[dict(r) for r in state['normalizer']],
                           powers=state._powers)
        for key in ('residue', 'coefficient'):
            bad = clone(); m.charge(); bad['normalizer'][0][key] = bad['normalizer'][0][key] * 2
            with self.assertRaises(ValueError): C.moments(bad, [2], m)
        bad = clone(); bad['centered'][2] = arb(0)
        with self.assertRaises(ValueError): C.moments(bad, [2], m)
        bad = clone(); bad['absolute'][2] = arb(0)
        with self.assertRaises(ValueError): C.moments(bad, [2], m)
        bad = dict(state); bad['normalizer'] = [dict(state['normalizer'][0], extra=True)]
        with self.assertRaises(ValueError): C.moments(bad, [2], m)

    def test_strict_source_state_horizon_precision_and_scales(self):
        m = Meter(); p = {'shifts': ['1/6']}
        for values in ([], [0], [0, 0], [0, True], [1, 1], [0, 1, 0.0], [0, 1, 2]):
            with self.assertRaises(ValueError): C.evaluate(p, values, m)
        state = C.baseline(1, 15, m)
        self.assertEqual(C.moments(state, [], m), [])
        for scales in ([True], [0], [8, 8], [9], (4,), [-1]):
            with self.assertRaises(ValueError): C.moments(state, scales, m)
        for degree in (0, 4, True):
            with self.assertRaises(ValueError): C.baseline(degree, 15, m)
        for prec in (127, 257):
            ctx.prec = prec
            with self.assertRaises(ValueError): C.normalizer(p, m)
            with self.assertRaises(ValueError): C.evaluate(p, [0, 1], m)
        ctx.prec = 192
        bad = dict(state); bad['centered'] = bad['centered'][:-1]
        with self.assertRaises(ValueError): C.moments(bad, [4], m)
        self.assertFalse(any(C.FLAGS.values()))

    def test_shared_counter_failure_no_new_meter_and_cached_powers(self):
        m = Meter(); state = C.evaluate({'shifts': ['1/6']}, [0] + [1] * 15, m)
        first = m.operations; C.moments(state, [4, 8], m); cached = m.operations - first
        first = m.operations; C.moments(dict(state), [4, 8], m); plain = m.operations - first
        self.assertGreaterEqual(plain - cached, (4 + 8) * (C.POWER_WORK - 4))
        limited = Meter(1)
        with self.assertRaises(OverflowError): C.evaluate({'shifts': ['1/6']}, [0, 1], limited)
        self.assertEqual(limited.operations, 1)


if __name__ == '__main__': unittest.main()
