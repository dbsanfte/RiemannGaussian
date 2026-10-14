"""Synthetic independent storage/control tests; no actual source arithmetic."""
from fractions import Fraction as F
import unittest

from flint import arb, ctx
import check_core_control_synthesis as C

TOTAL = 0


class Meter:
    def __init__(self, cap=1000000): self.operations = 0; self.peak = 0; self.cap = cap
    def charge(self, n=1):
        global TOTAL
        if type(n) is not int or n < 0: raise ValueError('strict nonnegative work')
        TOTAL += n; self.operations += n
        if self.operations > self.cap: raise RuntimeError('synthetic shared cap')
    def live(self, cells):
        if type(cells) is not int or not 0 <= cells <= 48000000: raise ValueError('resident cap')
        self.peak = max(self.peak, cells)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_control_synthesis operations=' + str(TOTAL))


def program(kind=None, alpha='0', mix='0', reserve='1'):
    return dict(auxiliary=None if kind is None else dict(kind=kind, alpha=alpha), mix=mix, reserve=reserve)


def transport(theta='3/4'):
    return dict(cofactor=2, theta=theta, capacity_fraction='1/2', load_multiple=4, keep_failed_windows=True)


def shape(rho='1/2', degree='2'):
    return dict(rho=rho, log_power=degree)


def state(coefficients, meter, D=None):
    """Literal full prefixes/log bank of tiny unrelated signed coefficients."""
    g = [arb(0)] + [arb(value) for value in coefficients]
    G = [arb(0)] * len(g); Bg = [arb(0)] * len(g)
    for n in range(1, len(g)):
        meter.charge(70)
        G[n] = G[n - 1] + g[n]
        Bg[n] = Bg[n - 1] + g[n] * arb(n).log()
    if D is None: D = [arb(0)] * len(g)
    else:
        meter.charge(len(D)); D = [arb(value) for value in D]
    meter.live(4 * len(g) + 4096)
    return dict(H=len(g) - 1, g=g, G=G, Bg=Bg, D=D)


def copy_state(fixture, meter):
    meter.charge(4 * len(fixture['G']) + 1)
    return {key: [arb(value) for value in values] if type(values) is list else values
            for key, values in fixture.items()}


class ControlTests(unittest.TestCase):
    def setUp(self): ctx.prec = 192; self.meter = Meter()
    def ball(self, left, right):
        self.meter.charge(); self.assertTrue(left.overlaps(right), (str(left), str(right)))

    def test_full_signed_cancellation_and_positive_reserve(self):
        fixture = state([3, 0, 0, 0, 0, 0, 0], self.meter, [0] + [-3] * 7)
        mixed = program('transport_error', mix='1', reserve='1/3')
        storage = C.measure(fixture, mixed, 4, self.meter)
        self.ball(storage, arb(3) / 4)  # Full mixed square is0; the reserve is3 per cell.
        self.ball(C.measure(fixture, program(), 4, self.meter), arb(9) / 4)
        positive_cross = C.measure(fixture, program('transport_error', mix='-1', reserve='1/3'), 4, self.meter)
        self.ball(positive_cross, arb(39) / 4)
        certificate = C.certificate(mixed, shape(), transport(), meter=self.meter)
        self.assertEqual(certificate['domination_constant'], '4')
        self.assertEqual(certificate['full_target_storage_constant'], '8')
        self.assertFalse(certificate['all_scale_target_bound_proved'])

    def test_exact_rational_domination_and_sharpness(self):
        for mix in (F(-2), F(-1, 2), F(0), F(1), F(3, 2)):
            for reserve in (F(1, 3), F(1), F(3)):
                p = program('transport_error', mix=str(mix), reserve=str(reserve))
                certificate = C.certificate(p, shape(), transport(), meter=self.meter)
                factor = F(certificate['domination_constant'])
                for G, Q in ((F(2), F(-3)), (F(-1), F(4)), (F(0), F(-2))):
                    self.meter.charge(24)
                    storage = (G + mix * Q) ** 2 + reserve * Q ** 2
                    gap = factor * storage - G ** 2
                    self.assertEqual(gap, (mix * G + (mix * mix + reserve) * Q) ** 2 / reserve)
                    self.assertGreaterEqual(gap, 0)
                self.meter.charge(20)
                extremal_Q = -mix * F(2) / (mix * mix + reserve)
                storage = (2 + mix * extremal_Q) ** 2 + reserve * extremal_Q ** 2
                self.assertEqual(factor * storage, 4)

    def test_complete_log_bank_unit_and_accumulated_head(self):
        fixture = state([2, -3, 5, -7, 1, 4, -2], self.meter)
        p = program('log_bank', mix='1', reserve='1')
        self.ball(C.measure(fixture, p, 1, self.meter), arb(4))  # Bg1=0, denominator log2.
        expected = arb(0)
        for n in range(4, 8):
            self.meter.charge(140)
            bank = sum((fixture['g'][h] * arb(h).log() for h in range(1, n + 1)), arb(0))
            Q = bank / arb(2 * n).log()
            expected += (fixture['G'][n] + Q) ** 2 + Q ** 2
        self.ball(C.measure(fixture, p, 4, self.meter), expected / 16)
        # Deleting the already-completed first three cells changes this observable.
        truncated = copy_state(fixture, self.meter)
        for n in range(4, 8):
            self.meter.charge(3); truncated['Bg'][n] -= fixture['Bg'][3]
        self.assertFalse(C.measure(truncated, p, 4, self.meter).overlaps(expected / 16))

    def test_half_delay_floor_zero_unit_and_fractional_weight(self):
        fixture = state([2, -3, 5, -7, 1, 4, -2], self.meter)
        p = program('half_delay', alpha='1/3', mix='-1', reserve='3')
        self.ball(C.measure(fixture, p, 1, self.meter), arb(4))  # G0=0; unit stays.
        expected = arb(0)
        for n in range(4, 8):
            self.meter.charge(80)
            Q = fixture['G'][n // 2] / arb(n).root(3)
            expected += (fixture['G'][n] - Q) ** 2 + 3 * Q ** 2
        self.ball(C.measure(fixture, p, 4, self.meter), expected / 16)

    def test_conditional_log_degree_and_composed_original_pole_gate(self):
        for theta, rho, degree, witness, excluded, recovery, resulting in (
            ('3/4', '1/2', '3/2', True, True, True, '3/2'),
            ('5/6', '1/2', '3/2', True, True, True, '3/2'),
            ('5/6', '1', '1', True, False, True, '2'),
            ('3/4', '1', '1/2', True, True, True, '3/2'),
            ('3/4', '1/2', '0', False, False, True, '0'),
            ('1', '1/2', '0', True, False, False, '0')):
            result = C.certificate(program(), shape(rho, degree), transport(theta), witness, self.meter)
            self.assertEqual((result['pole_excluded'], result['cofinal_recovery'], result['conditional_log_degree']),
                             (excluded, recovery, resulting))
            self.assertFalse(result['uniform_premise_established'])
            self.assertFalse(result['all_scale_storage_bound_proved']); self.assertFalse(result['RH_proved'])
        p = program('half_delay', mix='-1', reserve='3')
        result = C.certificate(p, shape(), transport(), meter=self.meter)
        p['auxiliary']['alpha'] = '1'; self.assertEqual(result['program']['auxiliary']['alpha'], '0')
        self.assertEqual(result['error_constant'], '50'); self.assertEqual(result['error_power'], '-1/6')

    def test_finite_pass_fail_unresolved_and_exact_base2_weight(self):
        passed = C.check_test({1: arb(0), 2: arb(1), 4: arb(2)}, [1, 2], shape('1/2', '1/2'), 2, self.meter)
        self.assertEqual([row['status'] for row in passed], ['pass', 'pass'])
        failed = C.check_test({1: arb(0), 2: arb(2)}, [1], shape('1/2', '0'), 1, self.meter)
        self.assertEqual(failed[0]['status'], 'fail')
        undecided = C.check_test({1: arb(0), 2: arb('1 +/- 0.5')}, [1], shape('1/2', '0'), 1, self.meter)
        self.assertEqual(undecided[0]['status'], 'unresolved')
        row = C.check_test({4: arb(0), 8: arb(10)}, [4], shape('1', '2'), 1, self.meter)[0]
        self.assertEqual(row['status'], 'fail')  # (1+log2(4))²=9, never ln(8)².
        self.ball(arb(row['upper_bound']), arb(9))

    def test_strict_program_shapes_rationals_and_witness(self):
        malformed = []
        for key, value in (('mix', True), ('mix', '2/4'), ('reserve', '0'), ('reserve', '-1'), ('mix', '0/1')):
            p = program('half_delay'); p[key] = value; malformed.append(p)
        malformed.extend((program(mix='1'), program(reserve='3')))
        for alpha in ('-1/6', '1/0', '00', '-0', '1.0', '1' + '0' * 1400):
            malformed.append(program('half_delay', alpha=alpha))
        malformed.append(program('unknown'))
        p = program(); p['extra'] = 1; malformed.append(p)
        p = program('half_delay'); p['auxiliary']['extra'] = 0; malformed.append(p)
        for p in malformed:
            with self.subTest(p=p), self.assertRaises(ValueError): C.validate(p, self.meter)
        for bad in (shape('2/4'), shape('0'), shape(degree='-1'), {'rho': '1', 'log_power': True}):
            with self.assertRaises(ValueError): C.certificate(program(), bad, transport(), meter=self.meter)
        with self.assertRaises(ValueError): C.certificate(program(), shape(), transport(), 1, self.meter)
        bad = transport(); bad['cofactor'] = True
        with self.assertRaises(ValueError): C.certificate(program(), shape(), bad, meter=self.meter)

    def test_measurement_and_recurrence_domain_failures_preserve_charges(self):
        fixture = state([2, -1, 3, -2, 1, 0, -1], self.meter)
        for X in (True, 0, 3, 8):
            with self.assertRaises(ValueError): C.measure(fixture, program(), X, self.meter)
        for key, value in (('H', True), ('D', [arb(0)] * 7), ('g', None)):
            bad = dict(fixture); bad[key] = value
            with self.assertRaises(ValueError): C.measure(bad, program(), 4, self.meter)
        bad = copy_state(fixture, self.meter); bad['G'][4] = arb('nan')
        with self.assertRaises(ArithmeticError): C.measure(bad, program(), 4, self.meter)
        bad = copy_state(fixture, self.meter); bad['Bg'][0] = arb(1)
        with self.assertRaises(ValueError): C.measure(bad, program(), 4, self.meter)
        for storage, parents, constant in (({1: arb(0)}, [1], 1), ({1: arb(0), 2: arb(1)}, [1, 1], 1),
                ({1: arb(0), 2: arb(1)}, [True], 1), ({1: arb(0), 2: arb(1)}, [1], True),
                ({1: arb(0), 2: arb(-1)}, [1], 1)):
            with self.assertRaises(ValueError): C.check_test(storage, parents, shape(), constant, self.meter)
        ctx.prec = 128
        with self.assertRaises(ValueError): C.measure(fixture, program(), 4, self.meter)
        ctx.prec = 192
        limited = Meter(cap=1)
        with self.assertRaises(RuntimeError): C.measure(fixture, program(), 4, limited)
        self.assertGreater(limited.operations, limited.cap)


if __name__ == '__main__': unittest.main()
