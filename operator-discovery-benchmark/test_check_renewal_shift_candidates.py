"""Tiny independent renewal tests; no producer or study response imports."""
from fractions import Fraction as Q
from itertools import combinations
import unittest

from flint import arb, ctx
import check_renewal_shift_candidates as C

METERS = []


class Meter:
    def __init__(self, cap=2000000):
        self.cap = cap; self.operations = 0; self.peak_cells = 0; METERS.append(self)

    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('nonnegative exact charge')
        if n > self.cap - self.operations: raise OverflowError('synthetic operation cap')
        self.operations += n

    def live(self, cells):
        self.charge(); self.peak_cells = max(self.peak_cells, cells)
        if cells > 6000000: raise MemoryError('synthetic scalar cell cap')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_renewal_shift_candidates operations=' +
          str(sum(m.operations for m in METERS)))


def real(q, meter):
    meter.charge(3); return arb(q.numerator) / q.denominator


def trial_source(name, H, meter):
    values = [0, 1]
    for n in range(2, H + 1):
        if name == 'one': values.append(1); continue
        residue = n; p = 2; sign = 1
        while p * p <= residue:
            meter.charge(); exponent = 0
            while residue % p == 0:
                meter.charge(2); residue //= p; exponent += 1
            if exponent > 1: sign = 0
            elif exponent == 1 and (name == 'mu' or p <= 13): sign = -sign
            p += 1
        if residue > 1 and (name == 'mu' or residue <= 13): sign = -sign
        values.append(sign)
    return values


def append_by_trial_quotient(old, b, meter):
    """Independent global Dirichlet division, not local Euler expansion."""
    H = len(old) - 1; shifted = [arb(0)] * (H + 1); out = [arb(0)] * (H + 1)
    shifted[1] = old[1]; out[1] = arb(1)
    for n in range(2, H + 1):
        meter.charge(C.POWER_WORK + 3)
        shifted[n] = old[n] * arb(n) ** real(-b, meter)
        value = old[n]
        for d in range(2, n + 1):
            meter.charge()
            if n % d == 0:
                meter.charge(2); value -= shifted[d] * out[n // d]
        out[n] = value
    return out


def manual_stencil(shifts, meter):
    merged = {}
    for size in range(len(shifts) + 1):
        for indices in combinations(range(len(shifts)), size):
            meter.charge(len(indices) + 1)
            shift = sum((shifts[i] for i in indices), Q(0))
            merged[shift] = merged.get(shift, 0) + (-1) ** (size + 1)
    return sorted((t, c) for t, c in merged.items() if c)


def manual_normalizer(program, meter):
    shifts = tuple(map(Q, program['shifts'])); compiled = manual_stencil(shifts, meter)
    L = Q(1)
    for b in shifts: L *= b
    rows = []
    for t, c in compiled:
        if c <= 0: continue
        residue = 1 / real(L, meter)
        for r, exponent in compiled:
            if r == t: continue
            meter.charge(C.ZETA_WORK + 8)
            residue *= real(1 - t + r, meter).zeta() ** exponent
        meter.charge(2)
        rows.append(dict(shift=str(t), residue=residue, coefficient=residue / real(1 - t, meter)))
    return rows


def clone(state):
    return C.State(coefficients=list(state['coefficients']), centered=list(state['centered']),
                   absolute=list(state['absolute']), normalizer=[dict(r) for r in state['normalizer']],
                   program=state._program, roots=state._roots, lcd=state._lcd)


class RenewalCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.old_precision = ctx.prec; ctx.prec = 192

    @classmethod
    def tearDownClass(cls): ctx.prec = cls.old_precision

    def test_exact_stencil_collisions_and_accepted_repeats(self):
        m = Meter()
        p = {'shifts': ['1/12', '1/6', '1/4']}
        expected = [(Q(0), -1), (Q(1, 12), 1), (Q(1, 6), 1), (Q(1, 3), -1),
                    (Q(5, 12), -1), (Q(1, 2), 1)]
        self.assertEqual(C.stencil(p), expected)
        self.assertEqual(C.stencil(p), manual_stencil(tuple(map(Q, p['shifts'])), m))
        self.assertNotIn(Q(1, 4), dict(C.stencil(p)))
        repeat = {'shifts': ['1/12', '1/6', '1/4', '1/4']}
        compiled = [(Q(k, 12), c) for k, c in ((0, -1), (1, 1), (2, 1), (3, 1),
                    (4, -2), (5, -2), (6, 1), (7, 1), (8, 1), (9, -1))]
        self.assertEqual(C.stencil(repeat), compiled)
        self.assertEqual(C.stencil(repeat), manual_stencil(tuple(map(Q, repeat['shifts'])), m))
        self.assertEqual([r['shift'] for r in C.normalizer(repeat, m)], ['1/12', '1/6', '1/4', '1/2', '7/12', '2/3'])
        self.assertEqual(sum(c for _, c in compiled), 0)
        self.assertEqual(compiled[0], (Q(0), -1))

    def test_unsupported_real_poles_rejected_before_ball_work(self):
        p = {'shifts': ['1/6', '1/6']}
        self.assertEqual(C.validate(p), (Q(1, 6), Q(1, 6)))
        self.assertEqual(C.stencil(p), [(Q(0), -1), (Q(1, 6), 2), (Q(1, 3), -1)])
        for action in ('evaluate', 'normalizer'):
            m = Meter()
            with self.assertRaisesRegex(ValueError, 'higher real pole'):
                if action == 'evaluate': C.evaluate(p, 'mu', 31, m)
                else: C.normalizer(p, m)
            self.assertEqual(m.operations, 0)

    def test_local_expansion_matches_global_shift_quotients_all_sources(self):
        m = Meter(); p = {'shifts': ['1/6', '1/3']}; L = Q(1, 18)
        for name in C.SOURCES:
            raw = list(map(arb, trial_source(name, 31, m)))
            for b in map(Q, p['shifts']): raw = append_by_trial_quotient(raw, b, m)
            state = C.evaluate(p, name, 31, m)
            self.assertEqual(set(state), {'coefficients', 'centered', 'absolute', 'normalizer'})
            self.assertTrue(state['coefficients'][1].is_zero())
            for n in range(2, 32):
                m.charge(2)
                self.assertTrue(state['coefficients'][n].overlaps(raw[n] / real(L, m)))

    def test_actual_prime_power_renewal_signs_and_control_parity(self):
        m = Meter(); p = {'shifts': ['1/3']}; b = Q(1, 3)
        actual = C.evaluate(p, 'mu', 63, m); one = C.evaluate(p, 'one', 63, m)
        partial = C.evaluate(p, 'partial_prime_13', 63, m)
        for prime in (2, 3, 5, 17, 19, 23):
            m.charge(C.POWER_WORK + 8); w = arb(prime) ** real(-b, m)
            power = prime; exponent = 1
            while power <= 63:
                m.charge(12)
                expected = (w - 1) * w ** (exponent - 1) / real(b, m)
                self.assertTrue(actual['coefficients'][power].overlaps(expected))
                self.assertTrue(actual['coefficients'][power] < 0)
                self.assertTrue(one['coefficients'][power].overlaps((1 - w) / real(b, m)))
                self.assertTrue(one['coefficients'][power] > 0)
                target = expected if prime <= 13 else (-1) ** exponent * expected
                self.assertTrue(partial['coefficients'][power].overlaps(target))
                power *= prime; exponent += 1
        m.charge(3)
        self.assertTrue(actual['coefficients'][6].overlaps(real(b, m) * actual['coefficients'][2] * actual['coefficients'][3]))

    def test_normalizer_all_channels_collisions_and_source_invariance(self):
        m = Meter(); p = {'shifts': ['1/12', '1/6', '1/4']}
        rows = C.normalizer(p, m); expected = manual_normalizer(p, m)
        self.assertEqual([r['shift'] for r in rows], ['1/12', '1/6', '1/2'])
        for a, b in zip(rows, expected):
            self.assertTrue(a['residue'].overlaps(b['residue']))
            self.assertTrue(a['coefficient'].overlaps(b['coefficient']))
        for name in C.SOURCES:
            state = C.evaluate(p, name, 15, m)
            for a, b in zip(state['normalizer'], rows): self.assertTrue(a['coefficient'].overlaps(b['coefficient']))
            # At1 the normalized increment is0; the ENTIRE signed normalizer
            # remains. Its absolute channels are not collapsed before abs.
            signed = envelope = arb(0)
            for row in rows:
                m.charge(2); signed += row['coefficient']; envelope += abs(row['coefficient'])
            self.assertTrue(state['centered'][1].overlaps(-signed))
            self.assertTrue(state['absolute'][1].overlaps(envelope))

    def test_complete_centers_full_moments_and_plain_mapping(self):
        m = Meter(); p = {'shifts': ['1/6', '1/3']}; state = C.evaluate(p, 'mu', 15, m)
        rows = manual_normalizer(p, m); prefix = abs_prefix = arb(0)
        centers = [arb(0)] * 16; envelopes = [arb(0)] * 16
        for n in range(1, 16):
            m.charge(2); prefix += state['coefficients'][n]; abs_prefix += abs(state['coefficients'][n])
            main = envelope = arb(0)
            for row in rows:
                m.charge(C.POWER_WORK + 4); power = arb(n) ** real(1 - Q(row['shift']), m)
                main += row['coefficient'] * power; envelope += abs(row['coefficient']) * power
            m.charge(2); centers[n] = prefix - main; envelopes[n] = abs_prefix + envelope
            self.assertTrue(state['centered'][n].overlaps(centers[n]))
            self.assertTrue(state['absolute'][n].overlaps(envelopes[n]))
        results = C.moments(state, [3, 4, 8], m)
        for row in results:
            E = A = arb(0); X = row['X']
            for n in range(X, 2 * X): m.charge(4); E += centers[n] ** 2; A += envelopes[n] ** 2
            m.charge(2)
            self.assertTrue(row['energy'].overlaps(E / (X * X)))
            self.assertTrue(row['absolute_energy'].overlaps(A / (X * X)))
        plain = dict(state); plain.pop('absolute'); rebuilt = C.moments(plain, [4], m)[0]
        self.assertTrue(rebuilt['energy'].overlaps(results[1]['energy']))
        self.assertTrue(rebuilt['absolute_energy'].overlaps(results[1]['absolute_energy']))

    def test_baseline_is_complete_mu_minus_unit_for_every_word(self):
        m = Meter(); state = C.baseline(31, m); expected = trial_source('mu', 31, m); expected[1] = 0
        prefix = envelope = 0
        for n in range(32):
            m.charge(2); prefix += expected[n]; envelope += abs(expected[n])
            self.assertTrue(state['coefficients'][n].contains(expected[n]))
            self.assertTrue(state['centered'][n].contains(prefix)); self.assertTrue(state['absolute'][n].contains(envelope))
        self.assertEqual(state['normalizer'], [])
        self.assertEqual(len(C.moments(state, [4, 8, 16], m)), 3)

    def test_normalizer_channel_center_envelope_and_state_tampering(self):
        m = Meter(); state = C.evaluate({'shifts': ['1/6', '1/3']}, 'one', 15, m)
        for key in ('residue', 'coefficient'):
            bad = clone(state); m.charge(); bad['normalizer'][0][key] = bad['normalizer'][0][key] * 2
            with self.assertRaises(ValueError): C.moments(bad, [2], m)
        bad = clone(state); bad['normalizer'].pop()
        with self.assertRaises(ValueError): C.moments(bad, [2], m)
        bad = clone(state); bad['normalizer'][0]['shift'] = '1/4'
        with self.assertRaises(ValueError): C.moments(bad, [2], m)
        for key in ('centered', 'absolute'):
            bad = clone(state); bad[key][2] = arb(0)
            with self.assertRaises(ValueError): C.moments(bad, [2], m)
        bad = dict(state); bad['coefficients'] = bad['coefficients'][:-1]
        with self.assertRaises(ValueError): C.moments(bad, [2], m)

    def test_strict_grammar_source_horizon_precision_and_fullblocks(self):
        invalid = [{}, {'shifts': []}, {'shifts': ['1/6'], 'extra': 1}, {'shifts': [True]},
                   {'shifts': ['0']}, {'shifts': ['1']}, {'shifts': ['-1/6']}, {'shifts': ['2/12']},
                   {'shifts': ['1/3', '1/6']}, {'shifts': ['1/2', '1/2']}, {'shifts': ['1/25']},
                   {'shifts': ['1/8', '1/9']}, {'shifts': ['1/12'] * 5}, {'shifts': ['1/0']}]
        for p in invalid:
            with self.assertRaises(ValueError): C.validate(p)
        m = Meter(); p = {'shifts': ['1/6']}
        for H in (0, -1, True, 262144):
            with self.assertRaises(ValueError): C.evaluate(p, 'mu', H, m)
            with self.assertRaises(ValueError): C.baseline(H, m)
        for name in ('MU', 'counterfeit_mu', 1):
            with self.assertRaises(ValueError): C.evaluate(p, name, 15, m)
        state = C.baseline(15, m)
        self.assertEqual(C.moments(state, [], m), [])
        for scales in ([9], [0], [True], [8, 8], (4,)):
            with self.assertRaises(ValueError): C.moments(state, scales, m)
        for precision in (127, 257):
            ctx.prec = precision
            with self.assertRaises(ValueError): C.normalizer(p, m)
        ctx.prec = 192
        self.assertFalse(any(C.FLAGS.values()))

    def test_shared_root_cache_and_operation_failure(self):
        m = Meter(); state = C.evaluate({'shifts': ['1/6', '1/3']}, 'mu', 15, m)
        before = m.operations; C.moments(state, [4, 8], m); cached = m.operations - before
        before = m.operations; C.moments(dict(state), [4, 8], m); plain = m.operations - before
        # Plain metadata lacks the original program, so it avoids a few zeta
        # checks. Compare its direct common-root work to a fixed zero-pole
        # baseline instead of falsely claiming its total must exceed cached.
        self.assertGreater(plain, 12 * C.POWER_WORK)
        self.assertGreater(cached, 0); self.assertGreater(m.peak_cells, 0)
        limited = Meter(1)
        with self.assertRaises(OverflowError): C.evaluate({'shifts': ['1/6']}, 'mu', 15, limited)
        self.assertLessEqual(limited.operations, 1)


if __name__ == '__main__': unittest.main()
