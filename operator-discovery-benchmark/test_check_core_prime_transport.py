"""Tiny synthetic transport/guard/recovery tests, no actual source evaluation."""
import copy
from fractions import Fraction as Q
import unittest
from flint import arb, ctx
import check_core_prime_transport as C

TOTAL = 0


class Meter:
    def __init__(self): self.operations = 0; self.peak = 0
    def charge(self, n=1):
        global TOTAL
        if type(n) is not int or n < 0: raise ValueError('strict work')
        TOTAL += n; self.operations += n
    def live(self, cells):
        if type(cells) is not int or not 0 <= cells <= 48000000: raise ValueError('resident cells')
        self.peak = max(self.peak, cells)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_prime_transport operations=' + str(TOTAL))


def program(m=2, theta='1'):
    return dict(cofactor=m, theta=theta, capacity_fraction='1/2', load_multiple=4, keep_failed_windows=True)


def fixture():
    coefficients = [arb(0)] * 32; coefficients[1] = arb(-3)
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31): coefficients[p] = arb(-1)
    for n, value in ((6, 4), (10, 4), (14, 4), (22, 6), (26, 4)): coefficients[n] = arb(value)
    return coefficients


def source_ast():
    return dict(terms=[
        dict(name='B', coefficient='beta', zeta_factors=[['0', '-2'], ['1/3', '1']]),
        dict(name='U', coefficient='-beta', zeta_factors=[['0', '-1'], ['1/3', '1'], ['2/3', '-1']]),
        dict(name='V', coefficient='-beta', zeta_factors=[['0', '-1']]),
        dict(name='power', coefficient='-R_u', zeta_factors=[['1/3', '1'], ['2/3', '-1']])])


class PrimeTransportTests(unittest.TestCase):
    def setUp(self): ctx.prec = 192; self.meter = Meter()
    def ball(self, left, right): self.assertTrue(left.overlaps(right), (str(left), str(right)))

    def test_sorted_round_robin_capacity_and_complete_window_mass(self):
        coefficients = fixture(); result = C.transform(coefficients, program(), self.meter)
        accepted = [window for window in result['windows'] if window['status'] == 'accepted']
        self.assertEqual([w['annulus'] for w in accepted], [4, 8, 16])
        self.assertEqual([(p, t) for p, t, demand in accepted[-1]['assignments']], [(17, 22), (19, 26), (23, 22), (29, 26), (31, 22)])
        self.assertEqual(accepted[-1]['max_load'], 3)
        for n, expected in ((1, -3), (2, -1), (3, -1), (5, 0), (7, 0), (6, 2), (10, 3), (14, 3), (22, 3), (26, 2), (31, 0)):
            self.ball(result['g'][n], arb(expected))
        for window in result['windows']:
            self.assertTrue(window['mass_residual'].contains(0))
            self.assertTrue(result['D'][window['stop'] - 1].contains(0))
            self.assertFalse(set(window['sources']) & set(window['destinations']))
        self.assertFalse(result['arithmetic_error_premise_verified'])
        self.assertFalse(result['transported_source_multiplicative']); self.assertFalse(result['RH_proved'])

    def test_aggregate_capacity_failure_retains_whole_window(self):
        coefficients = fixture(); coefficients[22] = arb(2)
        result = C.transform(coefficients, program(), self.meter)
        last = result['windows'][-1]
        self.assertEqual(last['reason'], 'capacity_not_certified'); self.assertEqual(last['assignments'], [])
        for n in range(16, 32): self.ball(result['g'][n], coefficients[n])
        self.assertTrue(result['g'][11].is_zero())  # Earlier accepted windows survive.
        uncertain = fixture(); uncertain[6] = arb('4 +/- 1')
        row = C.transform(uncertain, program(), self.meter)
        self.assertEqual(row['windows'][2]['reason'], 'capacity_not_certified')
        for n in range(4, 8): self.ball(row['g'][n], uncertain[n])

    def test_all_sign_failures_empty_and_no_destination(self):
        coefficients = fixture(); coefficients[7] = arb('0 +/- 1')
        result = C.transform(coefficients, program(), self.meter)
        self.assertEqual(result['windows'][0]['status'], 'empty')
        self.assertEqual(result['windows'][1]['reason'], 'no_destinations')
        self.assertEqual(result['windows'][2]['reason'], 'source_not_negative')
        for n in range(4, 8): self.ball(result['g'][n], coefficients[n])
        coefficients = fixture(); coefficients[6] = arb(0)
        result = C.transform(coefficients, program(), self.meter)
        self.assertEqual(result['windows'][2]['reason'], 'destination_not_positive')
        self.assertEqual(result['windows'][2]['assignments'], [])

    def test_congestion_guard_without_fake_window_geometry(self):
        coefficients = [arb(0)] * 32
        sources = [2, 3, 5, 7, 11, 13, 17, 19, 23]
        for p in sources: coefficients[p] = arb(-1)
        coefficients[6] = arb(100)
        status, reason, load, assignments = C._plan(coefficients, sources, [6], 2, self.meter)
        self.assertEqual((status, reason, load, assignments), ('rejected', 'congestion', 9, []))
        # This checks only the pure guard; these indices are not asserted to be
        # one arithmetic window, and no transport theorem follows from them.

    def test_fractional_windows_disjoint_complete_support_and_q_condition(self):
        result = C.transform(fixture(), program(theta='1/2'), self.meter)
        covered = [n for w in result['windows'] for n in range(w['start'], w['stop'])]
        self.assertEqual(covered, list(range(1, 32)))
        for window in result['windows']:
            k = window['annulus'].bit_length() - 1
            self.assertEqual(window['length'], 1 << (k // 2))
            self.assertEqual(window['stop'] - window['start'], window['length'])
        self.assertEqual([(p, t) for p, t, demand in result['assignments']], [(7, 6), (11, 10), (23, 22)])
        coefficients = fixture(); coefficients[12] = arb(100); coefficients[20] = arb(6); coefficients[28] = arb(4)
        row = C.transform(coefficients, program(4), self.meter)
        self.assertEqual(row['windows'][3]['destinations'], []) # q3<=m4 excluded.
        self.assertEqual(row['windows'][4]['destinations'], [20, 28])
        self.ball(row['g'][12], arb(100))
        for p, t, demand in row['assignments']:
            self.assertEqual(t % 4, 0); self.assertGreater(t // 4, 4)
        smaller = C.transform(fixture(), program(theta='2/3'), self.meter)
        self.assertEqual(next(w for w in smaller['windows'] if w['annulus'] == 8)['length'], 4)

    def test_global_log_bank_and_literal_signed_shell(self):
        coefficients = fixture(); result = C.transform(coefficients, program(), self.meter)
        expected_g = list(coefficients)
        for p in (5, 7, 11, 13, 17, 19, 23, 29, 31): expected_g[p] = arb(0)
        for n, value in ((6, 2), (10, 3), (14, 3), (22, 3), (26, 2)): expected_g[n] = arb(value)
        F = G = B = Bg = arb(0); prefix_g = [arb(0)] * 32; bank_g = [arb(0)] * 32
        for n in range(1, 32):
            logarithm = arb(n).log(); F += coefficients[n]; G += expected_g[n]
            B += coefficients[n] * logarithm; Bg += expected_g[n] * logarithm
            prefix_g[n] = G; bank_g[n] = Bg; self.meter.charge(76)
            self.ball(result['D'][n], F - G); self.ball(result['B_D'][n], B - Bg); self.meter.charge(2)
        local = sum(((coefficients[n] - expected_g[n]) * arb(n).log() for n in range(16, 32)), arb(0)); self.meter.charge(16 * 68)
        self.assertFalse(result['B_D'][31].overlaps(local))
        for block in result['blocks']:
            X = block['X']; Eg = Ed = W = arb(0)
            for n in range(X, 2 * X):
                Eg += prefix_g[n] ** 2; Ed += result['D'][n] ** 2
                if n > 1:
                    ell = arb(n).log().expint(1) - arb(n + 1).log().expint(1)
                    W += prefix_g[n] * bank_g[n] * ell
                self.meter.charge(660)
            self.ball(block['energy_transformed'], Eg / (X * X)); self.ball(block['energy_error'], Ed / (X * X))
            self.ball(block['prime_log_work'], W); self.meter.charge(3)
        self.assertTrue(result['blocks'][0]['prime_log_work'].is_zero())

    def test_strict_program_horizon_and_precision(self):
        invalid = []
        for key, value in (('cofactor', True), ('cofactor', 1), ('cofactor', 17), ('theta', '0'), ('theta', '2/4'), ('theta', '7/6'), ('capacity_fraction', '2/4'), ('load_multiple', True), ('keep_failed_windows', 1)):
            p = program(); p[key] = value; invalid.append(p)
        p = program(); p['id'] = 1; invalid.append(p)
        for p in invalid:
            with self.subTest(p=p), self.assertRaises(ValueError): C.transform(fixture(), p, self.meter)
        with self.assertRaises(ValueError): C.transform([arb(0)] * 7, program(), self.meter)
        with self.assertRaises(ValueError): C.transform([arb(0)], program(), self.meter)
        coefficients = fixture(); coefficients[0] = arb(1)
        with self.assertRaises(ValueError): C.transform(coefficients, program(), self.meter)
        ctx.prec = 128
        with self.assertRaises(ValueError): C.transform(fixture(), program(), self.meter)
        ctx.prec = 192

    def test_formal_prime_recovery_and_explicit_eventual_import(self):
        for m, theta, cofinal, eventual in ((2, '1/2', True, False), (2, '7/12', True, True), (12, '3/4', True, True), (6, '2/3', True, False), (4, '5/6', True, False), (2, '1', False, False)):
            result = C.verify_recovery(program(m, theta), source_ast(), arb(4), self.meter)
            self.assertEqual(result['cofinal_recovery'], cofinal); self.assertEqual(result['eventual_prime_deletion'], eventual)
            self.assertEqual(result['error_energy_power'], str(2 * Q(theta) - Q(5, 3)))
            self.assertTrue(result['error_energy_bound_proved']); self.assertFalse(result['all_scale_target_bound_proved'])
            self.assertTrue(result['eventual_prime_deletion_is_conditional_on_reviewed_import'])
        result = C.verify_recovery(program(theta='1/3'), source_ast(), arb(4), self.meter)
        self.assertFalse(result['global_log_bank_bound_applicable'])
        for residue in (arb(0), arb(5), arb('4 +/- 2')):
            with self.assertRaises(ValueError): C.verify_recovery(program(), source_ast(), residue, self.meter)
        bad = source_ast(); bad['terms'][0]['zeta_factors'][0][1] = '-1'
        with self.assertRaises(ValueError): C.verify_recovery(program(), bad, arb(4), self.meter)
        bad = source_ast(); bad['terms'][1]['name'] = 'B'
        with self.assertRaises(ValueError): C.verify_recovery(program(), bad, arb(4), self.meter)
        bad = source_ast(); bad['terms'][0]['zeta_factors'].append(['1', '0'])
        with self.assertRaises(ValueError): C.verify_recovery(program(), bad, arb(4), self.meter)


if __name__ == '__main__': unittest.main()
