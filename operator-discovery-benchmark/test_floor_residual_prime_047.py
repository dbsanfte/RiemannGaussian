"""Synthetic exact supplied-profile tests; no scientific candidates or norms."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest

import floor_residual_prime_047 as prime

METERS = []


def meter(**kwargs):
    m = prime.Meter(**kwargs)
    METERS.append(m)
    return m


def mobius(n):
    sign, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def request(p=2, N=6, ones=False):
    return {'prime': p, 'parent_support': N,
            'parent_values': ['1']+[str(Q(1) if ones else Q((-1)**n*(n+2), n+3)) for n in range(2, N+1)],
            'child_values': ['1']+[str(Q(1) if ones else Q((-1)**(n+1)*(2*n+1), n+2)) for n in range(2, p*N+1)]}


def cell(program, k):
    return Q(program['constant'])-sum(Q(r['value'])*Q(k % r['n'], r['n']) for r in program['coefficients'])-sum(Q(r['value']) for r in program['steps'] if k >= r['q'])


def profile_cell(values, k):
    if k < 1:
        return Q(0)
    return 1+sum(mobius(n)*Q(v)*Q(k % n, n) for n, v in enumerate(values, 1))


def signature(program):
    return program['constant'], program['coefficients'], program['steps']


class PrimeTests(unittest.TestCase):
    def setUp(self):
        self.meter = meter()

    def test_complete_program_identity_multiple_primes_fractional_profiles(self):
        for p, N in [(2, 7), (3, 10), (5, 8), (7, 3)]:
            req = request(p, N)
            cert = prime.build_prime_construction(req, self.meter)
            self.assertEqual(cert['source_request'], req)
            for k in range(1, 2*p*N+5):
                expected = profile_cell(req['child_values'], k)+profile_cell(req['parent_values'], k//p)
                self.assertEqual(cell(cert['original_forcing'], k), expected)
                self.assertEqual(sum(cell(row['program'], k) for row in cert['prime_split']['blocks']), expected)
                self.assertEqual(cell(cert['matched']['program'], k)+cell(cert['matched']['conversion_auxiliary'], k), expected)
            for identity in cert['identities']:
                self.assertTrue(identity['holds'])
                self.assertEqual(identity['difference']['constant'], '0')
                self.assertFalse(identity['difference']['coefficients'])
                self.assertFalse(identity['difference']['steps'])

    def test_prime_square_unit_and_exceptional_scalar_retained(self):
        cert = prime.build_prime_construction(request(2, 6, True), self.meter)
        source = {r['n']: r for r in cert['p_adic_source_coefficients']}
        floors = {r['n']: Q(r['value']) for r in cert['original_forcing']['coefficients']}
        self.assertEqual(source[1]['value'], '1')
        self.assertEqual(source[2]['value'], '0')
        self.assertEqual(source[4]['child_term'], '0')
        self.assertEqual(source[4]['parent_term'], '-1')
        self.assertEqual(source[4]['value'], '-1')
        self.assertEqual(source[8]['value'], '0')
        self.assertEqual(floors[4], 1)
        self.assertEqual(floors[2], Q(2, 15))
        self.assertEqual(cert['original_forcing']['steps'], [{'q': 2, 'value': '-1'}])
        self.assertEqual(cert['profile_scalar_sums']['parent_harmonic'], '2/15')
        self.assertEqual(cert['profile_scalar_sums']['child_shift_coprime'], '7/15')
        self.assertEqual(cert['profile_scalar_sums']['square_parent_shift_coprime'], '2/3')

    def test_ordinary_mu_certificate_independently_factored(self):
        cert = prime.build_prime_construction(request(3, 9), self.meter)
        for row in cert['mu_certificate']['rows']:
            product = 1
            for factor in row['factors']:
                p = factor['prime']
                self.assertTrue(all(p % d for d in range(2, p)))
                product *= p**factor['exponent']
            self.assertEqual(product, row['n'])
            self.assertEqual(row['mu'], mobius(row['n']))
        self.assertEqual(cert['mu_certificate']['rows'][0], {'n': 1, 'factors': [], 'mu': 1})

    def test_p_adic_source_rows_match_all_branches(self):
        req = request(3, 10)
        cert = prime.build_prime_construction(req, self.meter)
        U, V, p = [Q(0)]+list(map(Q, req['parent_values'])), [Q(0)]+list(map(Q, req['child_values'])), 3
        for row in cert['p_adic_source_coefficients']:
            n, m, exponent = row['n'], row['prime_free_part'], row['valuation']
            self.assertEqual(n, p**exponent*m)
            self.assertNotEqual(m % p, 0)
            if exponent == 0:
                expected = mobius(m)*V[m]
            elif exponent == 1:
                expected = mobius(m)*(U[m]-V[p*m])
            elif exponent == 2:
                expected = -mobius(m)*U[p*m]
            else:
                expected = Q(0)
            self.assertEqual(Q(row['value']), expected)

    def test_independently_rounded_supplied_values_not_multiplicative(self):
        req = {'prime': 2, 'parent_support': 5,
               'parent_values': ['1']+[str(Q(256//n, 256)) for n in range(2, 6)],
               'child_values': ['1']+[str(Q(1024//(n+1), 1024)) for n in range(2, 11)]}
        cert = prime.build_prime_construction(req, self.meter)
        source6 = cert['p_adic_source_coefficients'][5]
        self.assertEqual(Q(source6['value']), Q(req['child_values'][5])-Q(req['parent_values'][2]))
        self.assertNotEqual(Q(req['child_values'][5]), Q(req['child_values'][1])*Q(req['parent_values'][2]))
        self.assertFalse(cert['supplied_values_independently_source_verified'])
        for row in cert['matched']['cancelled_valuation_one']:
            self.assertEqual(row['value'], '0')

    def test_normalized_parent_and_direct_parent_exact(self):
        req = request(2, 7)
        cert = prime.build_prime_construction(req, self.meter)
        matched, lam = cert['matched'], Q(req['child_values'][1])
        self.assertEqual(matched['lambda'], str(lam))
        self.assertEqual(matched['normalized_parent_values'][0], '1')
        for n, v in enumerate(matched['normalized_parent_values'], 1):
            self.assertEqual(lam*Q(v), Q(req['child_values'][2*n-1]))
        for k in range(1, 32):
            self.assertEqual(lam*cell(matched['parent_program'], k), cell(matched['direct_parent_program'], k))
            self.assertEqual(cell(matched['program'], k), profile_cell(req['child_values'], k)+cell(matched['direct_parent_program'], k//2) if k >= 2 else profile_cell(req['child_values'], k))

    def test_lambda_zero_retains_division_free_matched_and_auxiliary(self):
        req = request(2, 5)
        req['child_values'][1] = '0'
        cert = prime.build_prime_construction(req, self.meter)
        matched = cert['matched']
        self.assertEqual(matched['status'], 'unmatched_only')
        self.assertIsNone(matched['normalized_parent_values'])
        self.assertIsNone(matched['parent_program'])
        self.assertIsNotNone(matched['program'])
        self.assertIsNotNone(matched['conversion_auxiliary'])
        self.assertEqual(matched['direct_parent_program']['constant'], '0')
        self.assertFalse(matched['program']['steps'])
        self.assertEqual(matched['conversion_auxiliary']['steps'], [{'q': 2, 'value': '-1'}])
        for k in range(1, 35):
            self.assertEqual(cell(matched['program'], k)+cell(matched['conversion_auxiliary'], k), cell(cert['original_forcing'], k))
            self.assertEqual(sum(cell(r['program'], k) for r in matched['blocks']), cell(matched['program'], k))
        self.assertTrue(all(row['value'] == '0' for row in matched['cancelled_valuation_one']))

    def test_negative_lambda_has_no_unlicensed_contraction_claim(self):
        req = request(3, 4)
        req['child_values'][2] = '-7/3'
        cert = prime.build_prime_construction(req, self.meter)
        self.assertEqual(cert['matched']['status'], 'available')
        self.assertEqual(cert['matched']['lambda'], '-7/3')
        self.assertFalse(cert['matched']['range_or_contraction_proved'])
        self.assertTrue(cert['identity_only'])
        self.assertEqual(cert['global_bound_status'], 'OPEN')
        self.assertEqual(cert['norm_convergence_status'], 'OPEN')
        self.assertFalse(cert['RH_proved'])
        self.assertFalse(cert['RH_refuted'])

    def test_minimal_support_and_empty_square_blocks(self):
        for p in (2, 3, 7):
            req = request(p, 1)
            cert = prime.build_prime_construction(req, self.meter)
            self.assertEqual(cert['parent_program']['coefficients'], [])
            for k in range(1, 3*p):
                self.assertEqual(cell(cert['original_forcing'], k), profile_cell(req['child_values'], k)+Q(k >= p))
            self.assertFalse(cert['prime_split']['blocks'][3]['program']['coefficients'])
            self.assertFalse(cert['prime_split']['blocks'][5]['program']['coefficients'])

    def test_equal_unit_profiles_make_conversion_zero(self):
        cert = prime.build_prime_construction(request(3, 9, True), self.meter)
        matched = cert['matched']
        self.assertEqual(matched['lambda'], '1')
        self.assertEqual(matched['conversion_auxiliary']['constant'], '0')
        self.assertEqual(matched['conversion_auxiliary']['coefficients'], [])
        self.assertEqual(matched['conversion_auxiliary']['steps'], [])
        self.assertEqual(signature(matched['program']), signature(cert['original_forcing']))

    def test_bounded_cells_independent_floor_and_truncated_divisor_replay(self):
        req = request(3, 5)
        U, V = [Q(0)]+list(map(Q, req['parent_values'])), [Q(0)]+list(map(Q, req['child_values']))
        for K in (1, 2, 8, 32):
            cert = prime.cell_energy_certificate(req, K, self.meter)
            energy, weighted = Q(0), Q(0)
            for row in cert['cells']:
                k, j = row['k'], row['k']//3
                cc = sum(mobius(n)*V[n] for n in range(1, 16) if k % n == 0)
                cp = sum(mobius(n)*U[n] for n in range(1, 6) if j and j % n == 0)
                fc = sum(mobius(n)*V[n]*(k//n) for n in range(1, 16))
                fp = sum(mobius(n)*U[n]*(j//n) for n in range(1, 6))
                self.assertEqual(Q(row['child_truncated_divisor_sum']), cc)
                self.assertEqual(Q(row['parent_truncated_divisor_sum']), cp)
                self.assertEqual(Q(row['child_floor_sum']), fc)
                self.assertEqual(Q(row['parent_floor_sum']), fp)
                value = profile_cell(req['child_values'], k)+profile_cell(req['parent_values'], j)
                self.assertEqual(Q(row['value']), value)
                self.assertEqual(Q(row['weighted_square']), value*value/Q(k*(k+1)))
                energy += value*value
                weighted += value*value/Q(k*(k+1))
            self.assertEqual(Q(cert['energy']), energy)
            self.assertEqual(Q(cert['weighted_norm']), weighted)
            self.assertFalse(cert['unobserved_cells_or_tails_inferred'])
            self.assertFalse(cert['whole_norm_proved'])
            self.assertEqual(cert['global_bound_status'], 'OPEN')

    def test_request_schema_canonical_units_and_composites(self):
        for p in (True, 1, 4, 6, 9):
            with self.assertRaises(ValueError):
                prime.build_prime_construction(request(p, 2), self.meter)
        bads = []
        bad = request(); bad['parent_values'][0] = '0'; bads.append(bad)
        bad = request(); bad['child_values'][0] = '2'; bads.append(bad)
        bad = request(); bad['child_values'][1] = '2/6'; bads.append(bad)
        bad = request(); bad['extra'] = True; bads.append(bad)
        bad = request(); bad['parent_values'].pop(); bads.append(bad)
        for bad in bads:
            with self.assertRaises(ValueError):
                prime.build_prime_construction(bad, self.meter)

    def test_resource_caps_and_snapshot(self):
        req = request()
        before = deepcopy(req)
        cert = prime.build_prime_construction(req, self.meter)
        req['child_values'][1] = '0'
        self.assertEqual(cert['source_request'], before)
        with self.assertRaises(OverflowError):
            prime.build_prime_construction(before, meter(cap=0))
        bad = {'prime': 2, 'parent_support': 3073, 'parent_values': [], 'child_values': []}
        with self.assertRaises(ValueError):
            prime.build_prime_construction(bad, self.meter)
        for K in (True, 0, 3, 131072):
            with self.assertRaises(ValueError):
                prime.cell_energy_certificate(before, K, self.meter)
        oversized = request(2, 1)
        oversized['child_values'][1] = str(Q(2**4096))
        with self.assertRaises(OverflowError):
            prime.build_prime_construction(oversized, self.meter)


if __name__ == '__main__':
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=1).run(unittest.defaultTestLoader.loadTestsFromTestCase(PrimeTests))
    invocation = {'returncode': 0 if result.wasSuccessful() else 1, 'tests': result.testsRun,
                  'failures': len(result.failures), 'errors': len(result.errors),
                  'elapsed_seconds': time.monotonic()-started,
                  'operations': sum(m.operations for m in METERS),
                  'max_rational_bits': max((m.max_rational_bits for m in METERS), default=0),
                  'estimated_peak_bytes': max((m.estimated_peak_bytes for m in METERS), default=0),
                  'cell_rows': sum(m.cell_rows for m in METERS),
                  'exposure': 'synthetic supplied rational profiles and exact bounded cell blocks only'}
    path = Path(__file__).with_name('floor_residual_prime_047_development.json')
    receipt = json.loads(path.read_text()) if path.exists() else {
        'schema': 'floor-prime-development-v1', 'invocations': [],
        'actual_scientific_candidates_evaluated': False, 'actual_source_arrays_read': False,
        'actual_norm_study_run': False, 'frozen_files_modified': False,
        'old_suites_or_studies_rerun': False, 'hashes_generated': False}
    receipt['invocations'].append(invocation)
    receipt['cumulative_operations'] = sum(row['operations'] for row in receipt['invocations'])
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    raise SystemExit(invocation['returncode'])
