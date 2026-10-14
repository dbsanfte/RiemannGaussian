"""Tiny complete-history/variance/path tests; no actual source computations."""
import copy
from fractions import Fraction as Q
import unittest
from flint import arb, ctx
import check_core_increment_projection as C

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
    print('SYNTHETIC_WORK module=test_check_core_increment_projection operations=' + str(TOTAL))


def storage(kind=None, alpha='0', mix='0', reserve='1'):
    return dict(auxiliary=None if kind is None else dict(kind=kind, alpha=alpha), mix=mix, reserve=reserve)


def synthetic(H, meter, coefficients=None, differences=None):
    g = [arb(0)] + [arb(n % 5 + 1) for n in range(1, H + 1)] if coefficients is None else coefficients
    d = [arb(0)] + [arb(n % 3 - 1) for n in range(1, H + 1)] if differences is None else differences
    G = [arb(0)] * (H + 1); Bg = [arb(0)] * (H + 1); D = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        G[n] = G[n - 1] + g[n]; D[n] = D[n - 1] + d[n]
        Bg[n] = Bg[n - 1] + g[n] * arb(n).log(); meter.charge(70)
    return dict(H=H, g=g, G=G, Bg=Bg, D=D)


def pair_reference(prepared, X, L, meter):
    """Variance by all within-cell pairs; path majorant by Cauchy per pair."""
    weight = prepared['weight']; full = coarse = detail = path = arb(0)
    for start in range(X, 2 * X, L):
        us = prepared['U'][start:start + L]; qs = prepared['Q'][start:start + L]
        su = sum(us, arb(0)); sq = sum(qs, arb(0)); meter.charge(2 * L)
        coarse += (su * su + weight * sq * sq) / L; meter.charge(7)
        for u, q in zip(us, qs): full += u * u + weight * q * q; meter.charge(5)
        for i in range(L):
            for j in range(i + 1, L):
                detail += ((us[j] - us[i]) ** 2 + weight * (qs[j] - qs[i]) ** 2) / L
                steps = arb(0); meter.charge(8)
                for t in range(i + 1, j + 1):
                    steps += (us[t] - us[t - 1]) ** 2 + weight * (qs[t] - qs[t - 1]) ** 2; meter.charge(7)
                path += (j - i) * steps / L; meter.charge(3)
    meter.charge(4)
    return [value / (X * X) for value in (full, coarse, detail, path)]


class IncrementProjectionTests(unittest.TestCase):
    def setUp(self): ctx.prec = 192; self.meter = Meter()
    def ball(self, a, b): self.assertTrue(a.overlaps(b), (str(a), str(b)))

    def test_weighted_delay_prepare_complete_signed_cross(self):
        state = synthetic(31, self.meter); p = storage('half_delay', '1/6', '-2/3', '1/2')
        prepared = C.prepare(state, p, self.meter)
        for n in range(1, 32):
            expected_q = state['G'][n // 2] / arb(n).root(6); self.meter.charge(68)
            expected_u = state['G'][n] - arb(2) * expected_q / 3; self.meter.charge(3)
            self.ball(prepared['Q'][n], expected_q); self.ball(prepared['U'][n], expected_u)
        row = C.project(prepared, 8, '2/3', self.meter)
        separated = arb(0)
        for n in range(8, 16):
            separated += state['G'][n] ** 2 + (arb(4) / 9 + arb(1) / 2) * prepared['Q'][n] ** 2; self.meter.charge(8)
        separated /= 64; self.meter.charge()
        self.assertFalse(row['full_storage'].overlaps(separated))
        self.assertTrue(row['full_storage'] < separated)

    def test_variance_and_cauchy_path_by_all_pairs(self):
        prepared = C.prepare(synthetic(31, self.meter), storage('transport_error', '1/3', '2/3', '3/2'), self.meter)
        for r, L in (('1/3', 2), ('2/3', 4), ('1', 8)):
            row = C.project(prepared, 8, r, self.meter)
            self.assertEqual(row['L'], L)
            expected = pair_reference(prepared, 8, L, self.meter)
            for key, value in zip(('full_storage', 'coarse_storage', 'detail_storage', 'path_bound'), expected): self.ball(row[key], value)
            self.assertTrue(row['identity_residual'].contains(0))
            self.assertIn(row['path_comparison'], ('pass', 'unresolved'))
            covered = [n for cell in row['cell_means'] for n in range(cell['start'], cell['stop'])]
            self.assertEqual(covered, list(range(8, 16)))
            self.assertFalse(row['all_scale_storage_bound_proved']); self.assertFalse(row['RH_proved'])

    def test_global_log_history_half_head_and_error_units(self):
        H = 127; coefficients = [arb(0)] * (H + 1); coefficients[1] = arb(5); coefficients[2] = arb(3)
        differences = [arb(0)] * (H + 1); differences[1] = arb(2)
        state = synthetic(H, self.meter, coefficients, differences)
        log = C.prepare(state, storage('log_bank', '1/3', '1/2', '1'), self.meter)
        for n in (1, 2, 64, 127):
            expected = state['Bg'][n] / arb(2 * n).log() / arb(n).root(3); self.meter.charge(134)
            self.ball(log['Q'][n], expected)
        self.assertTrue(log['Q'][64] > 0) # Earlier coefficient2 remains in the bank.
        delayed = C.prepare(state, storage('half_delay', '0', '1', '1'), self.meter)
        self.assertTrue(delayed['Q'][1].is_zero()); self.ball(delayed['Q'][2], arb(5)); self.ball(delayed['Q'][64], arb(8))
        error = C.prepare(state, storage('transport_error', '0', '-1/2', '2'), self.meter)
        self.ball(error['Q'][1], arb(2)); self.ball(error['Q'][64], arb(2))
        row = C.project(log, 64, '1/2', self.meter)
        self.assertEqual(row['cell_means'][0]['start'], 64)
        self.assertTrue(row['cell_means'][0]['Q_mean'] > 0)

    def test_singletons_exact_zero_detail_and_complete_unit(self):
        state = synthetic(7, self.meter); prepared = C.prepare(state, storage(), self.meter)
        for X, r in ((1, '1'), (4, '1/6')):
            row = C.project(prepared, X, r, self.meter)
            self.assertEqual(row['L'], 1); self.assertTrue(row['detail_storage'].is_zero())
            self.assertTrue(row['path_bound'].is_zero()); self.assertTrue(row['identity_residual'].is_zero())
            self.assertIs(row['coarse_storage'], row['full_storage']); self.assertEqual(row['path_comparison'], 'pass')
        self.ball(C.project(prepared, 1, '1', self.meter)['full_storage'], state['G'][1] ** 2); self.meter.charge()

    def test_interval_equality_is_unresolved_not_failed(self):
        prepared = dict(H=3, U=[arb(0), arb(0), arb('1 +/- 0.125'), arb('1 +/- 0.125')], Q=[arb(0)] * 4, weight=arb(1))
        row = C.project(prepared, 2, '1', self.meter)
        self.assertEqual(row['path_comparison'], 'unresolved')
        self.assertTrue(row['identity_residual'].contains(0))
        exact = dict(prepared, U=[arb(0), arb(0), arb(1), arb(1)])
        row = C.project(exact, 2, '1', self.meter)
        self.assertEqual(row['path_comparison'], 'pass'); self.assertTrue(row['detail_storage'].is_zero())

    def test_rational_detail_payment_and_unpaid_mesh(self):
        p = storage(); K = Q(37, 2)
        sub = C.certificate(p, '1/3', self.meter)
        self.assertEqual(sub['detail_constant'], str(2 * K * K)); self.assertEqual(sub['detail_power'], '-1/3')
        self.assertEqual(sub['bounded_detail_constant'], str(2 * K * K * 96 * 27))
        self.assertEqual(sub['effective_detail_log_degree'], 0); self.assertTrue(sub['bounded_detail'])
        critical = C.certificate(p, '1/2', self.meter)
        self.assertEqual(critical['detail_power'], '0'); self.assertEqual(critical['effective_detail_log_degree'], 3)
        self.assertTrue(critical['cofinal_recovery']); self.assertFalse(critical['bounded_detail'])
        self.assertIsNone(critical['bounded_detail_constant'])
        above = C.certificate(p, '2/3', self.meter)
        self.assertFalse(above['cofinal_recovery']); self.assertIsNone(above['effective_detail_log_degree'])
        self.assertFalse(sub['coefficient_majorant_premise_verified']); self.assertFalse(sub['all_scale_target_bound_proved'])

    def test_all_auxiliary_bound_constants_and_scope(self):
        K = Q(37, 2); mix = Q(-2, 3); w = Q(1, 2); alpha = Q(1, 3)
        for kind, b in (('half_delay', 2 * alpha), ('transport_error', 2 * alpha), ('log_bank', 2 * alpha + 4)):
            cert = C.certificate(storage(kind, '1/3', '-2/3', '1/2'), '1/2', self.meter)
            expected = 4 * K * K * (1 + (2 * mix * mix + w) * (1 + b * b)); self.meter.charge(20)
            self.assertEqual(cert['detail_constant'], str(expected)); self.assertEqual(cert['auxiliary_variation_constant'], str(b))
            self.assertEqual(cert['raw_log_degree'], 3)
            self.assertIn('all integers n>=1', cert['coefficient_majorant_premise'])
        p = storage('half_delay', '1/2', '0', '1')
        C.prepare(synthetic(7, self.meter), p, self.meter) # Generic storage remains evaluable.
        with self.assertRaises(ValueError): C.certificate(p, '1/2', self.meter)

    def test_strict_mesh_state_and_complete_cells(self):
        state = synthetic(15, self.meter); p = storage(); prepared = C.prepare(state, p, self.meter)
        for X, r in ((True, '1/2'), (3, '1/2'), (16, '1/2'), (4, '0'), (4, '7/6'), (4, '2/4')):
            with self.subTest(X=X, r=r), self.assertRaises(ValueError): C.project(prepared, X, r, self.meter)
        for key in ('g', 'G', 'Bg', 'D'):
            bad = copy.copy(state); bad[key] = state[key][:-1]
            with self.subTest(key=key), self.assertRaises(ValueError): C.prepare(bad, p, self.meter)
        missing = copy.copy(state); del missing['Bg']
        with self.assertRaises(ValueError): C.prepare(missing, p, self.meter)
        bad = dict(prepared, Q=prepared['Q'][:-1])
        with self.assertRaises(ValueError): C.project(bad, 4, '1/2', self.meter)
        bad = dict(prepared, weight=arb(0))
        with self.assertRaises(ValueError): C.project(bad, 4, '1/2', self.meter)
        bad = storage(); bad['reserve'] = '-1'
        with self.assertRaises(ValueError): C.prepare(state, bad, self.meter)
        ctx.prec = 160
        with self.assertRaises(ValueError): C.prepare(state, p, self.meter)
        ctx.prec = 192


if __name__ == '__main__': unittest.main()
