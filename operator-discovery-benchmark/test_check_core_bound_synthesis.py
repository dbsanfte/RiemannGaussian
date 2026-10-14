"""Tiny direct-mode and literal-filter tests; no producer or study inputs."""
import copy
from fractions import Fraction as Q
import unittest
from flint import arb, ctx
import check_core_bound_synthesis as C

METERS = []


class Meter:
    def __init__(self, cap=2000000, cells=6000000):
        self.operations = 0; self.cap = cap; self.cells = cells; self.peak_cells = 0; METERS.append(self)

    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('strict nonnegative charge')
        if n > self.cap - self.operations: raise OverflowError('synthetic cap')
        self.operations += n

    def live(self, cells):
        self.charge(); self.peak_cells = max(self.peak_cells, cells)
        if cells > self.cells: raise MemoryError('resident cap')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_bound_synthesis operations=' + str(sum(m.operations for m in METERS)))


def real(text, meter):
    value = Q(text); meter.charge(3); return arb(value.numerator) / value.denominator


def power(base, text, meter):
    meter.charge(C.POWER_WORK); return arb(base) ** real(text, meter)


def factors(n, meter):
    result = []; p = 2
    while p * p <= n:
        meter.charge()
        if n % p == 0:
            exponent = 0
            while n % p == 0: exponent += 1; n //= p; meter.charge(2)
            result.append((p, exponent))
        p += 1
    if n > 1: result.append((n, 1)); meter.charge()
    return result


def synthetic(H, meter):
    modes = {name: [arb(0)] * (H + 1) for name in C.MODES}
    prefixes = {name: [arb(0)] * (H + 1) for name in C.MODES}
    core = [arb(0)] * (H + 1); F = [arb(0)] * (H + 1)
    coefficients = [arb(2), -arb(3), arb(1) / 2, -arb(1)]; meter.charge(4)
    for n in range(1, H + 1):
        for i, name in enumerate(C.MODES):
            meter.charge(8); modes[name][n] = arb((-1) ** (n + i) * ((n + i) % 4 + 1))
            prefixes[name][n] = prefixes[name][n - 1] + modes[name][n]
            core[n] += coefficients[i] * modes[name][n]
        F[n] = F[n - 1] + core[n]; meter.charge()
    log_prefix = [arb(0)] * (H + 1); log_abel = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        if n == 1: logarithm = arb(0); meter.charge()
        else: meter.charge(C.POWER_WORK); logarithm = arb(n).log()
        log_prefix[n] = log_prefix[n - 1] + core[n] * logarithm; meter.charge(2)
        log_abel[n] = F[n] if n < 64 else log_prefix[n] / logarithm; meter.charge()
    return C.State(H=H, precision=192, modes=modes, prefixes=prefixes, core=core, F=F,
                   log_prefix=log_prefix, log_abel=log_abel, c=coefficients)


def literal(program, X, state, meter):
    target = program['target_filter']; auxiliary = program['auxiliary']; result = [arb(0)] * 3
    for n in range(X, 2 * X):
        F = state['F'][n]
        if target.get('kind', 'delay') == 'log_abel':
            if n < 64: G = F
            else:
                numerator = arb(0)
                for k in range(1, n + 1):
                    if k == 1: logarithm = arb(0); meter.charge()
                    else: meter.charge(C.POWER_WORK); logarithm = arb(k).log()
                    numerator += (state['F'][k] - state['F'][k - 1]) * logarithm; meter.charge(3)
                meter.charge(C.POWER_WORK + 1); G = numerator / arb(n).log()
        else:
            a = arb(0) if target['sign'] == 0 else target['sign'] * power(2, target['theta'], meter)
            G = F - a * state['F'][n // 2]; meter.charge(2)
        H = arb(0)
        if auxiliary is not None:
            b = arb(0) if auxiliary['theta'] is None else power(2, auxiliary['theta'], meter)
            for text, name in zip(auxiliary['coefficients'], C.MODES):
                H += real(text, meter) * (state['prefixes'][name][n] - b * state['prefixes'][name][n // 2]); meter.charge(4)
            H *= power(n, str(-Q(auxiliary['alpha'])), meter); meter.charge()
        result[0] += F ** 2; result[1] += G ** 2; result[2] += H ** 2; meter.charge(6)
    result = [value / (X * X) for value in result]; meter.charge(3)
    weight = arb(0) if auxiliary is None else real(auxiliary['weight'], meter)
    majorant = result[1] + weight * result[2]; meter.charge(2)
    return dict(energy_target=result[0], energy_filtered=result[1], energy_auxiliary=result[2], majorant=majorant)


class CoreBoundCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old_precision = ctx.prec; ctx.prec = 192
        cls.source_meter = Meter(); cls.actual = C.source(31, cls.source_meter)

    @classmethod
    def tearDownClass(cls): ctx.prec = cls.old_precision

    def assertBall(self, actual, expected):
        self.assertTrue(actual.is_finite()); self.assertTrue(actual.overlaps(expected), (actual, expected))

    def test_modes_against_independent_local_prime_power_formulas(self):
        m = Meter(); s = self.actual
        for n in range(1, 32):
            expected = [arb(1)] * 4
            for p, e in factors(n, m):
                t = power(p, '-1/3', m); v = t * t; m.charge(20 + 4 * e)
                nu0 = t - 2 if e == 1 else (1 - t) ** 2 * t ** (e - 2)
                nu1 = t - 1 - v if e == 1 else (t - 1) * (t - v) * t ** (e - 2)
                nu2 = (t - v) * t ** (e - 1)
                mu = arb(-1 if e == 1 else 0)
                expected = [a * b for a, b in zip(expected, (nu0, nu1, nu2, mu))]
            for name, value in zip(C.MODES, expected): self.assertBall(s['modes'][name][n], value)
        for name in C.MODES:
            self.assertTrue(s['modes'][name][0].is_zero()); self.assertTrue(s['prefixes'][name][0].is_zero())
            self.assertTrue(s['modes'][name][1] == 1)

    def test_true_residue_complete_core_prefix_and_log_unit(self):
        m = Meter(); s = self.actual; m.charge(2 * C.ZETA_WORK + 10)
        z = (arb(2) / 3).zeta(); R_u = arb(9) / 2 * ((arb(4) / 3).zeta() / z ** 2 - 1 / z)
        self.assertBall(s['R_u'], R_u); prefix = arb(0)
        for n in range(1, 32):
            m.charge(10); coefficient = arb(9) / 2 * s['nu0'][n] - arb(9) / 2 * s['nu1'][n] - R_u * s['nu2'][n] - arb(9) / 2 * s['mu'][n]
            self.assertBall(s['core'][n], coefficient); prefix += coefficient; self.assertBall(s['F'][n], prefix)
            self.assertBall(s['log_abel'][n], s['F'][n])
        self.assertTrue(s['log_prefix'][1].is_zero()); self.assertFalse(s['F'][1].is_zero())
        self.assertBall(s['core'][1], -R_u - arb(9) / 2)

    def test_all_delay_signs_fractional_storage_and_odd_X(self):
        m = Meter(); state = synthetic(31, m)
        for sign in (-1, 0, 1):
            for auxiliary in (None, dict(coefficients=['1', '-1/2', '2/3', '-2'], theta=None, alpha='1/6', weight='3/2'),
                              dict(coefficients=['-1', '2', '0', '1/3'], theta='2/3', alpha='1/3', weight='1/2')):
                program = dict(target_filter=dict(kind='delay', sign=sign, theta='5/6'), auxiliary=auxiliary)
                for X in (1, 3, 8, 16):
                    result = C.measure(program, X, state, m); reference = literal(program, X, state, m)
                    for key, value in reference.items(): self.assertBall(result[key], value)
                    self.assertFalse(result['RH_proved']); self.assertFalse(result['recovery_premise_established'])

    def test_literal_signed_gram_keeps_off_diagonal_crosses(self):
        m = Meter(); state = synthetic(15, m)
        program = dict(target_filter=dict(sign=1, theta='0'), auxiliary=dict(coefficients=['1', '-2', '1/2', '3'], theta='1/3', alpha='0', weight='2'))
        result = C.measure(program, 5, state, m)
        beta = power(2, '1/3', m); gram = arb(0)
        for n in range(5, 10):
            v = [real(c, m) * (state['prefixes'][name][n] - beta * state['prefixes'][name][n // 2]) for c, name in zip(program['auxiliary']['coefficients'], C.MODES)]
            for a in v:
                for b in v: gram += a * b; m.charge(2)
        self.assertBall(result['energy_auxiliary'], gram / 25)
        self.assertBall(result['majorant'], result['energy_filtered'] + 2 * result['energy_auxiliary'])

    def test_log_abel_threshold_and_finite_head_on_synthetic_H127(self):
        m = Meter(); state = synthetic(127, m)
        self.assertBall(state['log_abel'][63], state['F'][63])
        m.charge(C.POWER_WORK + 1); self.assertBall(state['log_abel'][64], state['log_prefix'][64] / arb(64).log())
        program = dict(target_filter=dict(kind='log_abel', cutoff=64), auxiliary=None)
        for X in (31, 32, 33, 64):
            result = C.measure(program, X, state, m); reference = literal(program, X, state, m)
            for key, value in reference.items(): self.assertBall(result[key], value)
        m.charge(C.POWER_WORK + 1)
        self.assertFalse(state['log_abel'][64].overlaps(state['F'][64] / arb(64).log()))
        self.assertTrue(state['log_prefix'][1].is_zero()); self.assertFalse(state['F'][1].is_zero())

    def test_actual_source_measure_matches_literal(self):
        m = Meter(); program = dict(target_filter=dict(kind='delay', sign=-1, theta='1/2'),
                                   auxiliary=dict(coefficients=['1', '0', '-1', '1/3'], theta='1/6', alpha='1/3', weight='2'))
        for X in (1, 3, 8, 16):
            result = C.measure(program, X, self.actual, m); reference = literal(program, X, self.actual, m)
            for key, value in reference.items(): self.assertBall(result[key], value)

    def test_strict_schema_domains_and_positive_storage(self):
        good = dict(target_filter=dict(kind='delay', sign=1, theta='1/3'), auxiliary=None)
        bad = [{}, dict(good, extra=1), dict(good, target_filter=dict(kind='delay', sign=True, theta='1/3')),
               dict(good, target_filter=dict(kind='delay', sign=2, theta='1/3')),
               dict(good, target_filter=dict(kind='delay', sign=1, theta='2/6')),
               dict(good, target_filter=dict(kind='delay', sign=1, theta='1/13')),
               dict(good, target_filter=dict(kind='log_abel', cutoff=63)), dict(good, target_filter=dict(kind='log_abel', cutoff=True))]
        for p in bad:
            with self.assertRaises(ValueError): C.validate(p)
        for aux in (dict(coefficients=['1'] * 3, theta=None, alpha='0', weight='1'),
                    dict(coefficients=['1'] * 4, theta=None, alpha='0', weight='0'),
                    dict(coefficients=['1'] * 4, theta='-1/6', alpha='0', weight='1'),
                    dict(coefficients=['1'] * 4, theta=None, alpha='7/6', weight='1')):
            with self.assertRaises(ValueError): C.validate(dict(good, auxiliary=aux))
        m = Meter()
        for H in (True, 0, -1, 262144):
            with self.assertRaises(ValueError): C.source(H, m)
        for X in (True, 0, -1, 17):
            with self.assertRaises(ValueError): C.measure(good, X, self.actual, m)
        with self.assertRaises(ValueError): C.measure(good, 1, dict(self.actual), m)

    def test_universal_coarse_reference_and_tampered_domains(self):
        m = Meter()
        def fixture(program):
            Ct = Q(37, 2) if program['target_filter']['kind'] == 'log_abel' else Q(37)
            auxiliary = program['auxiliary']; Ch = weight = Q(0)
            if auxiliary is not None:
                Ch = 2 * sum(abs(Q(v)) for v in auxiliary['coefficients']); weight = Q(auxiliary['weight'])
            m.charge(30)
            return dict(rule='absolute_prefix_majorants', source='actual_mu_candidate10_four_mode_core',
                        imports=['|nu0(n)|<=d2(n); |nu1(n)|,|nu2(n)|,|mu(n)|<=1',
                                 'sum_(n<=x) d2(n)<=x*(1+log x)', '0<R_u<=residue_ceiling'],
                        program=program, residue_ceiling=5, constant=str(72 * (Ct * Ct + weight * Ch * Ch)),
                        gamma='1', log_power=2,
                        statement='for every dyadic X>=1 and rho>=0: A(2X)-rho*A(X)<=constant*X*(1+log2 X)^2',
                        independently_rh_sufficient=False, whole_signed_bound_proved=False, RH_proved=False)
        programs = [dict(target_filter=dict(kind='delay', sign=-1, theta='5/6'),
                         auxiliary=dict(coefficients=['1', '-1/2', '2', '0'], theta='1/2', alpha='1/2', weight='3/2')),
                    dict(target_filter=dict(kind='log_abel', cutoff=64), auxiliary=None)]
        for program in programs:
            certificate = fixture(program); record = C.verify_coarse(certificate, arb(4), m)
            self.assertTrue(record['universal_reference_verified']); self.assertEqual(record['gamma'], '1')
            self.assertFalse(record['cofinal_critical_bound_proved']); self.assertFalse(record['RH_proved'])
            for field, value in (('constant', '1'), ('gamma', '0'), ('log_power', True), ('RH_proved', True),
                                 ('statement', 'for some dyadic X>=64'), ('residue_ceiling', True), ('source', 'one')):
                changed = copy.deepcopy(certificate); changed[field] = value
                with self.assertRaises(ValueError): C.verify_coarse(changed, arb(4), m)
            for residue in (arb(0), arb(-1), arb(6)):
                with self.assertRaises(ValueError): C.verify_coarse(certificate, residue, m)
        bad = fixture(programs[0]); bad['program']['auxiliary']['alpha'] = '-1/6'
        with self.assertRaises(ValueError): C.verify_coarse(bad, arb(4), m)

    def test_shared_meter_precision_and_resource_failure(self):
        m = Meter(); program = dict(target_filter=dict(sign=0, theta='0'), auxiliary=None)
        C.measure(program, 2, self.actual, m); before = m.operations; C.measure(program, 2, self.actual, m)
        self.assertGreater(m.operations, before); self.assertLess(m.peak_cells, 6000000)
        ctx.prec = 160
        try:
            with self.assertRaises(ValueError): C.source(7, m)
            with self.assertRaises(ValueError): C.measure(program, 2, self.actual, m)
        finally: ctx.prec = 192
        with self.assertRaises(OverflowError): C.source(7, Meter(cap=1))
        with self.assertRaises(MemoryError): C.source(7, Meter(cells=1))


if __name__ == '__main__': unittest.main()
