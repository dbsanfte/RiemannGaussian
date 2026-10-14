"""Tiny independent source/log-bank/signed-work and conditional-scope tests."""
import copy
from fractions import Fraction as Q
import unittest
from flint import arb, ctx
import check_core_signed_work as C

TOTAL = 0


class Meter:
    def __init__(self): self.operations = 0; self.peak = 0
    def charge(self, n=1):
        global TOTAL
        if type(n) is not int or n < 0: raise ValueError('strict nonnegative work')
        self.operations += n; TOTAL += n
    def live(self, cells):
        if type(cells) is not int or not 0 <= cells <= 48000000: raise ValueError('resident cells')
        self.peak = max(self.peak, cells)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_signed_work operations=' + str(TOTAL))


def program(sign=0, theta='0', eta='1'):
    return dict(target_filter=dict(kind='delay', sign=sign, theta=theta), eta=eta, cutoff=1024)


def synthetic(H, meter, coefficients=None):
    if coefficients is None: coefficients = [arb(0)] + [arb((n % 5) - 2) for n in range(1, H + 1)]
    F = [arb(0)] * (H + 1); B = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        meter.charge(68)
        F[n] = F[n - 1] + coefficients[n]
        B[n] = B[n - 1] + coefficients[n] * arb(n).log()
    return C.State(H=H, precision=192, core=coefficients, F=F, log_prefix=B)


def reference(p, X, state, meter):
    q = Q(p['target_filter']['theta']); eta = Q(p['eta'])
    a = p['target_filter']['sign'] * arb(2) ** (arb(q.numerator) / q.denominator)
    eta = arb(eta.numerator) / eta.denominator; meter.charge(72)
    # Build delayed increments and their logarithmic prefix independently.
    G = [arb(0)] * (state['H'] + 1); B = [arb(0)] * len(G)
    for n in range(1, len(G)):
        increment = state['core'][n] - (a * state['core'][n // 2] if n % 2 == 0 else arb(0))
        G[n] = G[n - 1] + increment
        B[n] = B[n - 1] + increment * arb(n).log(); meter.charge(74)
    E = N = P = arb(0)
    for n in range(X, 2 * X):
        ell = arb(0) if n == 1 else arb(n).log().expint(1) - arb(n + 1).log().expint(1)
        E += G[n] * G[n]; N += G[n] * G[n] / (n * (n + 1)); P += G[n] * B[n] * ell
        meter.charge(660)
    return E / (X * X), N, P, (1 - eta) * N + eta * P


def recovery(p):
    # Certificate fixtures are assembled from the published schema, not scorer code.
    inverse = C._inverse(p['target_filter'])
    return dict(rule='signed_shell_volterra_history', program=p,
        work='integral_X^(2X) ((1-eta)*G(x)^2+eta*G(x)*B_G(x)/log(x))/x^2 dx',
        exact_filtered_log_bank='B_G(x)=B_F(x)-a*B_F(x/2)-a*log(2)*F(x/2)',
        domain='every dyadic X>=1024; full unit-cell integrals; zero prefixes below1',
        eta_absolute_ceiling='2', log2_lower='69/100', local_volterra_upper='3/5',
        history_geometric_sum_square_upper='6', gap_lower='4/5', history_mass_upper='2/5',
        history='N_G(X)<=2W_eta(X)/g_eta(X)+eta^2*(1+sqrt2)/(2*g_eta(X)^2*log(X)^2)*sum_(k=1)^log2X 2^(-k/2)*N_G(X/2^k)',
        gap='g_eta(X)=1-|eta|*(2-sqrt2)/log(X)',
        assumption='W_eta(X)<=K*(1+log2X)^p for every dyadic X>=1024; K>=0,p>=0',
        head='H0=max_(dyadic Y<1024) E_G(Y), all finite units and delayed heads retained',
        conclusion='E_G(X)<=4*max(H0,5K)*(1+log2X)^p for all dyadic X>=1',
        strict_smaller_scale_dependencies=True, filtered_energy_log_loss=0, target_recovery=inverse,
        all_scale_work_bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)


def weak(p):
    eta = Q(p['eta']); constant = 4 * (abs(1 - eta) + abs(eta)) * Q(111, 2) ** 2
    return dict(rule='complete_absolute_shell_reference', program=p, source_residue_ceiling=5,
        source_coefficient_ceiling='37/2', filtered_coefficient_ceiling='111/2', shell_constant=str(constant),
        step_constant=str(9 * constant), gamma='1', log_power=2,
        scope='all dyadic X>=1024 and0<=rho<=1; |W(X)|<=shell_constant*X*(1+log2X)^2',
        critical_control_proved=False, whole_signed_bound_proved=False, RH_proved=False)


class SignedWorkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 192; cls.source_meter = Meter(); cls.actual = C.source(31, cls.source_meter)

    def setUp(self): self.meter = Meter(); ctx.prec = 192

    def assertBall(self, left, right): self.assertTrue(left.overlaps(right), (str(left), str(right)))

    def test_source_complete_local_rows_and_units(self):
        s = self.actual
        self.assertEqual(s['mu_int'][:11], [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1])
        self.assertBall(s['core'][1], -s['R_u'] - arb(9) / 2)
        self.assertTrue(s['log_prefix'][1].is_zero())
        for p in (2, 3, 5):
            t = 1 / arb(p).root(3); self.meter.charge(70)
            self.assertBall(s['nu0'][p], t - 2)
            self.assertBall(s['nu1'][p], t - 1 - t * t)
            self.assertBall(s['nu2'][p], t - t * t)
            if p * p <= 31:
                self.assertBall(s['nu0'][p * p], t * t - 2 * t + 1)
                self.assertBall(s['nu1'][p * p], t * t - (1 + t * t) * t + t * t)
        for name in C.MODES:
            self.assertBall(s[name][6], s[name][2] * s[name][3]); self.meter.charge()
        self.assertGreater(self.source_meter.operations, 0)
        with self.assertRaises(ValueError): C.source(True, self.meter)
        with self.assertRaises(ValueError): C.source(524288, self.meter)

    def test_full_prime_power_logbank_and_tamper(self):
        result = C.verify_logbank(self.actual, self.meter)
        self.assertTrue(result['all_prime_powers_retained'])
        self.assertTrue(all(v.contains(0) for v in result['coefficient_residual']))
        tamper = C.State(self.actual); tamper['core'] = list(self.actual['core']); tamper['core'][4] += 1
        with self.assertRaises(ValueError): C.verify_logbank(tamper, self.meter)
        tamper = C.State(self.actual); tamper['log_prefix'] = list(self.actual['log_prefix']); tamper['log_prefix'][9] += 1
        with self.assertRaises(ValueError): C.verify_logbank(tamper, self.meter)

    def test_fractional_delay_complete_log_bank(self):
        state = synthetic(31, self.meter); p = program(-1, '1/3', '3/2')
        row = C.measure(p, 8, state, self.meter); expected = reference(p, 8, state, self.meter)
        for name, value in zip(('energy_filtered', 'critical_energy', 'prime_log_work', 'work'), expected):
            self.assertBall(row[name], value)
        a = -arb(2) ** (arb(1) / 3); n = 8; self.meter.charge(70)
        wrong = state['log_prefix'][n] - a * state['log_prefix'][n // 2]
        right = wrong - a * arb(2).log() * state['F'][n // 2]; self.meter.charge(70)
        self.assertFalse(wrong.overlaps(right))
        self.assertBall(row['memory_cross'], row['critical_energy'] - row['prime_log_work'])
        self.assertFalse(row['dyadic_domain']); self.assertFalse(row['RH_proved'])

    def test_signed_work_not_energy_and_irregular_full_block(self):
        coefficients = [arb(0)] * 16; coefficients[1] = arb(1)
        state = synthetic(15, self.meter, coefficients); p = program(0, '0', '2')
        row = C.measure(p, 3, state, self.meter)
        self.assertTrue(row['critical_energy'] > 0); self.assertTrue(row['work'] < 0)
        self.assertTrue(row['prime_log_work'].is_zero())
        for name, value in zip(('energy_filtered', 'critical_energy', 'prime_log_work', 'work'), reference(p, 3, state, self.meter)):
            self.assertBall(row[name], value)
        self.assertFalse(row['dyadic_domain'])

    def test_finite_unit_head_and_full_support(self):
        state = synthetic(7, self.meter); row = C.measure(program(1, '1/2', '2'), 1, state, self.meter)
        self.assertTrue(row['prime_log_work'].is_zero())
        self.assertBall(row['critical_energy'], state['F'][1] ** 2 / 2)
        self.assertBall(row['work'], -row['critical_energy']); self.meter.charge(4)
        self.assertFalse(row['dyadic_domain'])
        with self.assertRaises(ValueError): C.measure(program(), 5, state, self.meter)
        with self.assertRaises(ValueError): C.measure(program(), True, state, self.meter)
        bad = C.State(state); bad['log_prefix'] = list(state['log_prefix']); bad['log_prefix'][1] = arb(1)
        with self.assertRaises(ValueError): C.measure(program(), 1, bad, self.meter)

    def test_whole_integral_weights_and_cache_accounting(self):
        state = synthetic(127, self.meter); C._cache(state, self.meter)
        for n in (2, 7, 64):
            ell = C._ell(n, state, self.meter)
            # Independently enclose the integral with literal interval rectangles.
            lower = upper = arb(0); pieces = 32
            for j in range(pieces):
                left = arb(n) + arb(j) / pieces; right = arb(n) + arb(j + 1) / pieces
                lower += 1 / (right * right * right.log()) / pieces
                upper += 1 / (left * left * left.log()) / pieces; self.meter.charge(150)
            self.assertTrue(ell > lower); self.assertTrue(ell < upper)
            e1 = arb(n).log().expint(1) - arb(n + 1).log().expint(1); self.meter.charge(644)
            self.assertBall(ell, e1)
        first = C.measure(program(1, '1/6', '0'), 8, state, self.meter)
        before = self.meter.operations
        other = C.measure(program(1, '1/6', '1'), 8, state, self.meter)
        self.assertLess(self.meter.operations - before, 20)
        self.assertBall(first['energy_filtered'], other['energy_filtered'])
        fresh = Meter(); C.measure(program(1, '1/6', '1'), 8, state, fresh)
        self.assertGreater(fresh.operations, 1000)
        self.assertGreater(self.meter.peak, 0)

    def test_strict_program_and_precision_schema(self):
        invalid = [program(2), program(True), program(1, '2/4'), program(1, '1/13'), program(1, '-1/6'), program(1, '7/6'), program(eta='5/2')]
        for p in invalid:
            with self.subTest(p=p), self.assertRaises(ValueError): C.validate(p)
        p = program(); p['cutoff'] = True
        with self.assertRaises(ValueError): C.validate(p)
        p = program(); p['target_filter']['kind'] = 'log_abel'
        with self.assertRaises(ValueError): C.validate(p)
        p = program(); p['RH_proved'] = False
        with self.assertRaises(ValueError): C.validate(p)
        ctx.prec = 128
        with self.assertRaises(ValueError): C.source(3, self.meter)
        ctx.prec = 192

    def test_conditional_history_and_paid_inverse_scope(self):
        for sign, theta, cofinal, loss in ((0, '1', True, 0), (1, '1/3', True, 0), (-1, '1/2', True, 2), (1, '2/3', False, None)):
            result = C.verify_recovery(recovery(program(sign, theta)), self.meter)
            self.assertEqual(result['target_recovery']['cofinal'], cofinal)
            self.assertEqual(result['target_recovery']['extra_log_degree'], loss)
            self.assertFalse(result['uniform_premise_discharged'])
        for key, value in (('gap_lower', '3/4'), ('strict_smaller_scale_dependencies', False), ('head', 'head omitted'), ('all_scale_work_bound_proved', True), ('RH_proved', True)):
            cert = recovery(program()); cert[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): C.verify_recovery(cert, self.meter)
        cert = recovery(program()); cert['finite_points_passed'] = 100
        with self.assertRaises(ValueError): C.verify_recovery(cert, self.meter)

    def test_weak_reference_retains_signed_parent_and_domain(self):
        cert = weak(program(-1, '1/2', '2'))
        result = C.verify_weak(cert, self.actual['R_u'], self.meter)
        self.assertFalse(result['critical_control_proved'])
        for key, value in (('step_constant', cert['shell_constant']), ('gamma', '0'), ('scope', 'all integers X>=1'), ('whole_signed_bound_proved', True)):
            bad = copy.deepcopy(cert); bad[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): C.verify_weak(bad, self.actual['R_u'], self.meter)
        with self.assertRaises(ValueError): C.verify_weak(cert, arb(6), self.meter)


    def test_signed_recurrence_zero_forcing_and_open_base(self):
        def make(rho, k, constant):
            p = program(1, '1/3'); B = Q(2); H = Q(3); C0 = Q(constant); r = Q(rho)
            if C0 == 0: K = B; degree = 0
            elif r < 1: K = B + C0 / (1 - r); degree = k
            else: K = B + C0; degree = k + 1
            return dict(rule='signed_upper_dyadic_recurrence', program=p, rho=rho, log_power=k,
                constant=constant, base_scale=1024, base_upper='2', head_energy_upper='3',
                base_requirement='W(1024)<=base_upper; all dyadic E_G(Y)<=head_energy_upper for1<=Y<1024',
                premise='W(2X)<=rho*W(X)+constant*(1+log2X)^log_power for every dyadic X>=1024',
                work_upper_constant=str(K), filtered_log_degree=degree, filtered_energy_constant=str(4 * max(H, 5 * K)),
                conclusion='E_G(X)<=filtered_energy_constant*(1+log2X)^filtered_log_degree for every dyadic X>=1',
                recovery=recovery(p), uniform_step_proved=False, whole_signed_bound_proved=False, RH_proved=False)
        for rho, k, constant, degree in (('1/2', 2, '3', 2), ('1', 1, '3', 2), ('1', 4, '0', 0)):
            cert = make(rho, k, constant); result = C.verify_recurrence(cert, self.meter)
            self.assertEqual(result['filtered_log_degree'], degree)
            self.assertFalse(result['base_and_head_verified']); self.assertFalse(result['uniform_step_proved'])
        for key, value in (('filtered_log_degree', 4), ('uniform_step_proved', True), ('base_upper', '-1'), ('base_scale', 1), ('log_power', True), ('rho', '3/2')):
            cert = make('1', 4, '0'); cert[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): C.verify_recurrence(cert, self.meter)
        cert = make('1/2', 2, '3'); cert['recovery']['program'] = program(1, '1/2')
        with self.assertRaises(ValueError): C.verify_recurrence(cert, self.meter)


if __name__ == '__main__': unittest.main()
