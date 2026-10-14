"""New synthetic tests; fixtures use trial factorization and scalar products.

No producer, saved scientific record, frozen historical suite or LP is run.
Each invocation appends its full result to the checker development receipt.
"""
import copy
from fractions import Fraction as Q
from math import isqrt
import json
from pathlib import Path
import resource
import time
import traceback
import unittest
from unittest import mock
import check_mobius_signed_lag_067 as C


class ChargeOnly:
    def __init__(self):
        self.operations = 0

    def charge(self, n=1):
        self.operations += n


METER = ChargeOnly()


def trial_mu(n):
    sign, divisor = 1, 2
    while divisor*divisor <= n:
        if n % divisor == 0:
            n //= divisor
            sign = -sign
            if n % divisor == 0:
                return 0
        divisor += 1
    return -sign if n > 1 else sign


def W(N, base, d):
    return 4*N//(base*d)-3*(2*N//(base*d))+2*(N//(base*d))


def sqrt_grid(value):
    scaled = value.numerator*(1 << 48)
    root = isqrt(scaled//value.denominator)
    while root*root*value.denominator < scaled:
        root += 1
    return Q(root, 1 << 24)


def fixture(N=12, y=3, H=12, p=2, q=3, exponents=None, tau=True):
    D, H = 4*N//p, min(H, 4*N//p)
    exponents = ['0', '1/2', '1/257', '1'] if exponents is None else exponents
    parameters = dict(primes=[p, q], p=p, q=q, alpha='1/2', gamma='1/3')
    if tau:
        parameters['tau'] = '1/4'
    cert = dict(schema=C.SCHEMA, N=N, y=y, H=H, parameters=parameters,
        head_stop=(H+1)//2-1, exponent_requests=exponents,
        rounding_denominator=1 << 24, endpoints=[],
        uniform_full_head_bound_proved=False, RH_proved=False)
    for ratio in (Q(p, q), Q(1)):
        den = ratio.denominator
        full = [Q(0)]+[Q(W(N, p, d))-ratio*W(N, q, d) for d in range(1, D+1)]+[Q(0)]
        g = [Q(0)]+[-full[d] if d > y else Q(0) for d in range(1, D+1)]+[Q(0)]
        # Pointwise jumps, not a supplied sparse tail dictionary.
        M1 = sum((T*abs(g[T]-g[T+1]) for T in range(1, D+1)), Q(0))
        # Independent full inverse contraction proves each direct term.
        floors = {}
        for j in range(1, D+1):
            direct = sum((trial_mu(n)*(full[j*n]-(full[(j+1)*n] if (j+1)*n <= D else 0))
                          for n in range(1, D//j+1)), Q(0))
            if direct:
                floors[j] = direct
        floor_l1 = sum(map(abs, floors.values()), Q(0))
        endpoint = dict(ratio=str(ratio), denominator=den, step_first_moment=str(M1),
                        floor_l1=str(floor_l1), blocks=[])
        L = 1
        while L <= cert['head_stop']:
            stop = min(2*L-1, cert['head_stop'])
            R = [0]*(D//L)
            sums, directs, kernel_l1, max_kernel = [], [], Q(0), Q(0)
            for j in range(L, stop+1):
                weights = [g[j*n]-(g[(j+1)*n] if (j+1)*n <= D else 0)
                           for n in range(1, D//j+1)]
                values = [int(den*a)*trial_mu(n) for n, a in enumerate(weights, 1)]
                kernel_l1 += sum(map(abs, weights), Q(0))
                max_kernel = max(max_kernel, max(map(abs, weights), default=Q(0)))
                sums.append(sum(values))
                directs.append(floors.get(j, Q(0)))
                for h in range(len(values)):
                    R[h] += sum(values[n]*values[n+h] for n in range(len(values)-h))
            diag, cross = Q(R[0], den*den), Q(2*sum(R[1:]), den*den)
            moment = Q(sum(a*a for a in sums), den*den)
            absolute_direct = sum(map(abs, directs), Q(0))
            count = stop-L+1
            block = dict(start=L, stop=stop, correlation_numerators=R,
                row_sums_scaled=sums, direct_coefficients=list(map(str, directs)),
                joined_kernel_l1=str(kernel_l1), max_kernel=str(max_kernel),
                diagonal=str(diag), signed_cross=str(cross), moment=str(moment),
                diagonal_upper=str(4*kernel_l1), uniform_diagonal_upper=str(4*M1/L),
                actual_head_variation=str(sum((abs(a+Q(b, den)) for a, b in zip(directs, sums)), Q(0))),
                cauchy_upper=str(absolute_direct+sqrt_grid(count*moment)), candidates=[])
            for exponent in [None]+exponents:
                if exponent is None:
                    requested = 0
                else:
                    delta = Q(exponent)
                    # Scalar enumeration instead of producer binary search.
                    requested = max(b for b in range(1, N+1)
                                    if b**delta.denominator <= N**delta.numerator)
                B = min(requested, len(R)-1)
                near = Q(2*sum(R[1:B+1]), den*den)
                far = cross-near
                paid = (4+8*B)*M1/L
                upper = paid+max(far, Q(0))
                block['candidates'].append(dict(exponent=exponent, requested_cutoff=requested,
                    used_cutoff=B, near_signed=str(near), far_signed=str(far),
                    paid_moment_upper=str(paid), finite_moment_upper=str(upper),
                    finite_head_upper=str(absolute_direct+sqrt_grid(count*upper)),
                    paid_head_upper=str(sqrt_grid(count*paid)),
                    unpaid_risk_upper=str(sqrt_grid(count*max(far, Q(0)))),
                    far_nonpositive_observed=far <= 0, uniform_far_bound_proved=False))
            endpoint['blocks'].append(block)
            L *= 2
        cert['endpoints'].append(endpoint)
    return cert


def accept(cert):
    return C.verify_lag(cert, METER)


class Tests(unittest.TestCase):
    def reject(self, cert):
        with self.assertRaises((ValueError, OverflowError, MemoryError)):
            accept(cert)

    def test_scope_and_source_identity(self):
        out = accept(fixture())
        for field in ('verified', 'all_lags_independently_verified',
                      'original_source_inverse_identity_proved', 'ordinary_mu_unit_retained',
                      'squareful_mu_zero_retained', 'diagonal_and_individual_lag_rule_proved',
                      'endpoint_convexity_proved', 'independent_parent_066_admission_required'):
            self.assertIs(out[field], True)
        for field in ('original_source_binding_proved', 'uniform_far_bound_proved',
                      'uniform_full_head_bound_proved', 'uniform_N_growth_proved',
                      'whole_signed_target_bound_proved', 'RH_proved', 'scientific_source_or_LP_evaluated'):
            self.assertIs(out[field], False)
        self.assertEqual(out['arithmetic_query_horizon'], 24)

    def test_tiny_unit_cutoff_and_head_boundaries(self):
        for H in range(1, 5):
            for y in range(1, 5):
                accept(fixture(N=2, y=y, H=H))

    def test_exhaustive_small_source_and_every_prefix(self):
        for N in range(2, 11):
            for y in range(1, 2*N+1):
                accept(fixture(N=N, y=y, H=min(9, 2*N), exponents=['0', '1/3', '1']))

    def test_exact_fractional_cutoffs_unrestricted_denominators(self):
        cert = fixture(N=16, exponents=['0', '1/257', '1/17', '1/2', '3/4', '1'])
        accept(cert)
        values = [t['requested_cutoff'] for t in cert['endpoints'][0]['blocks'][0]['candidates']]
        self.assertEqual(values, [0, 1, 1, 1, 4, 8, 16])

    def test_unit_prime_squareful_ordinary_mu(self):
        mu = C._ordinary_mu(128, C._Context(ChargeOnly()))
        self.assertEqual(mu, [0]+[trial_mu(n) for n in range(1, 129)])
        self.assertEqual(mu[1], 1)
        self.assertEqual([mu[n] for n in (4, 8, 9, 12, 16, 18, 25)], [0]*7)

    def test_unit_omission_rejected(self):
        cert = fixture(N=2, y=1, H=4)
        row = cert['endpoints'][0]['blocks'][0]['row_sums_scaled']
        self.assertNotEqual(row[0], 0)
        row[0] = 0
        self.reject(cert)

    def test_squareful_prime_sign_substitution_rejected(self):
        cert = fixture(N=32, y=7, H=16)
        ratio, den = Q(2, 3), 3
        g = lambda d: -(Q(W(32, 2, d))-ratio*W(32, 3, d)) if d > 7 else Q(0)
        change = den*(g(4)-g(8))
        self.assertNotEqual(change, 0)
        cert['endpoints'][0]['blocks'][0]['row_sums_scaled'][0] += int(change)
        self.reject(cert)

    def test_every_lag_mutation_rejected(self):
        baseline = fixture()
        for ei, endpoint in enumerate(baseline['endpoints']):
            for bi, block in enumerate(endpoint['blocks']):
                for hi in range(len(block['correlation_numerators'])):
                    cert = copy.deepcopy(baseline)
                    cert['endpoints'][ei]['blocks'][bi]['correlation_numerators'][hi] += 1
                    self.reject(cert)

    def test_lag_mutation_preserving_total_rejected(self):
        cert = fixture()
        R = cert['endpoints'][0]['blocks'][0]['correlation_numerators']
        R[1] += 1
        R[2] -= 1
        self.reject(cert)

    def test_complete_lag_domain_last_zero_and_order(self):
        for mutate in ('pop', 'append', 'reverse'):
            cert = fixture()
            R = cert['endpoints'][0]['blocks'][0]['correlation_numerators']
            getattr(R, mutate)(0) if mutate == 'append' else getattr(R, mutate)()
            self.reject(cert)

    def test_all_blocks_required_and_exact_boundaries(self):
        for index in (0, 1, -1):
            cert = fixture(); cert['endpoints'][0]['blocks'].pop(index); self.reject(cert)
        for field in ('start', 'stop'):
            cert = fixture(); cert['endpoints'][0]['blocks'][1][field] += 1; self.reject(cert)
        cert = fixture(); cert['head_stop'] += 1; self.reject(cert)

    def test_direct_terms_at_small_prefix_and_atom_in_head(self):
        cert = fixture(N=12, y=1, H=24)
        accept(cert)
        self.assertTrue(any(Q(d) for e in cert['endpoints'] for b in e['blocks']
                            for d in b['direct_coefficients']))
        cert['endpoints'][0]['blocks'][-1]['direct_coefficients'][-1] = '999'
        self.reject(cert)

    def test_full_prefix_empty_correction(self):
        cert = fixture(N=12, y=24, H=24)
        accept(cert)
        for endpoint in cert['endpoints']:
            self.assertEqual(endpoint['step_first_moment'], '0')
            self.assertTrue(all(not any(b['correlation_numerators']) for b in endpoint['blocks']))

    def test_different_prime_pairs_optional_tau(self):
        for p, q in ((2, 3), (3, 5), (5, 7)):
            accept(fixture(N=15, y=2, H=9, p=p, q=q, tau=False))

    def test_all_block_rational_fields(self):
        baseline = fixture()
        for field in ('joined_kernel_l1', 'max_kernel', 'diagonal', 'signed_cross', 'moment',
                      'diagonal_upper', 'uniform_diagonal_upper', 'actual_head_variation', 'cauchy_upper'):
            cert = copy.deepcopy(baseline)
            block = cert['endpoints'][0]['blocks'][0]
            block[field] = str(Q(block[field])+1)
            self.reject(cert)

    def test_row_sums_and_direct_complete_domain(self):
        for field in ('row_sums_scaled', 'direct_coefficients'):
            cert = fixture(); cert['endpoints'][0]['blocks'][1][field].pop(); self.reject(cert)
            cert = fixture(); cert['endpoints'][0]['blocks'][1][field][0] = 99 if field.startswith('row') else '99'; self.reject(cert)

    def test_all_candidate_fields(self):
        baseline = fixture()
        for field in ('near_signed', 'far_signed', 'paid_moment_upper', 'finite_moment_upper',
                      'finite_head_upper', 'paid_head_upper', 'unpaid_risk_upper'):
            cert = copy.deepcopy(baseline)
            trial = cert['endpoints'][0]['blocks'][0]['candidates'][2]
            trial[field] = str(Q(trial[field])+1)
            self.reject(cert)

    def test_cutoff_changes_and_exponent_order(self):
        for field in ('requested_cutoff', 'used_cutoff'):
            cert = fixture(); cert['endpoints'][0]['blocks'][0]['candidates'][2][field] += 1; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['blocks'][0]['candidates'].reverse(); self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['blocks'][0]['candidates'].pop(); self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['blocks'][0]['candidates'][0]['exponent'] = '0'; self.reject(cert)

    def test_finite_observations_and_uniform_claims(self):
        for field in ('uniform_full_head_bound_proved', 'RH_proved'):
            cert = fixture(); cert[field] = True; self.reject(cert)
        for field in ('far_nonpositive_observed', 'uniform_far_bound_proved'):
            cert = fixture()
            trial = cert['endpoints'][0]['blocks'][0]['candidates'][0]
            trial[field] = not trial[field]
            self.reject(cert)
        cert = fixture(); cert['infinite_extension_bound'] = '0'; self.reject(cert)

    def test_endpoint_ratios_denominator_and_moments(self):
        cert = fixture(); cert['endpoints'].pop(); self.reject(cert)
        cert = fixture(); cert['endpoints'].reverse(); self.reject(cert)
        for field in ('ratio', 'step_first_moment', 'floor_l1'):
            cert = fixture(); cert['endpoints'][0][field] = '99'; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['denominator'] = 6; self.reject(cert)

    def test_parameters_and_capacity_integer_gates(self):
        for field, value in (('p', 3), ('q', 2), ('alpha', '0'), ('gamma', '0'), ('tau', '1'),
                             ('primes', [2, 4]), ('primes', [3, 2])):
            cert = fixture(); cert['parameters'][field] = value; self.reject(cert)
        for field, value in (('N', True), ('N', 1), ('N', 65537), ('H', True), ('H', 0),
                             ('y', 0), ('y', 25), ('rounding_denominator', 8)):
            cert = fixture(); cert[field] = value; self.reject(cert)

    def test_strict_bool_integer_scalar_gates(self):
        cert = fixture(); cert['endpoints'][0]['blocks'][0]['correlation_numerators'][0] = True; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['blocks'][0]['row_sums_scaled'][0] = False; self.reject(cert)
        cert = fixture(); cert['uniform_full_head_bound_proved'] = 0; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['blocks'][0]['candidates'][0]['used_cutoff'] = False; self.reject(cert)

    def test_noncanonical_rationals_and_exponent_limits(self):
        for value in ('2/2', '0.5', ' 1', '1/0', '', str(1 << 4096)):
            cert = fixture(); cert['endpoints'][0]['ratio'] = value; self.reject(cert)
        for requests in ([], ['1/2', '1/2'], ['-1'], ['2'], ['2/4'], ['1/100001']):
            cert = fixture(); cert['exponent_requests'] = requests; self.reject(cert)

    def test_unknown_fields_not_free_sign_or_repaired(self):
        for field in ('core_inverse', 'prime_signs', 'repair', 'scientific_bound'):
            cert = fixture(); cert[field] = []; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['blocks'][0]['segments'] = []; self.reject(cert)
        cert = fixture(); cert['schema'] = 'mobius-sparse-prefix-inverse-v1'; self.reject(cert)

    def test_direct_integer_correlation_and_overflow_guard(self):
        c = C._Context(ChargeOnly())
        self.assertEqual(C._correlate([1, -2, 0, 3], c), [14, -2, -6, 3])
        with self.assertRaises(OverflowError):
            C._correlate([1 << 40, 1 << 40], c)
        with mock.patch.object(C.np, 'correlate', side_effect=AssertionError('must not execute')):
            with self.assertRaises(OverflowError):
                C._correlate([1 << 40], c)

    def test_work_memory_entries_and_power_guards(self):
        cert = fixture()
        with self.assertRaises(OverflowError):
            C.verify_lag(cert, C.Meter(cap=0))
        with mock.patch.object(C, 'MAX_WORK', 20):
            with self.assertRaises(OverflowError):
                accept(cert)
        with mock.patch.object(C, 'MAX_MEMORY_BYTES', 9000):
            with self.assertRaises(MemoryError):
                accept(cert)
        with mock.patch.object(C, 'MAX_ENTRIES', 3):
            with self.assertRaises(OverflowError):
                accept(cert)
        with self.assertRaises(OverflowError):
            C._Context(ChargeOnly()).bounded(Q(1 << 4096))


if __name__ == '__main__':
    started = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
    test_ids = [t.id() for t in suite]
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    attempt = dict(tests_run=result.testsRun, test_ids=test_ids,
        failures=[dict(test=t.id(), traceback=s) for t, s in result.failures],
        errors=[dict(test=t.id(), traceback=s) for t, s in result.errors],
        successful=result.wasSuccessful(), charged_work_units=METER.operations,
        wall_seconds=time.monotonic()-started,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    path = Path(__file__).with_name('mobius_signed_lag_checker_067_development.json')
    report = json.loads(path.read_text()) if path.exists() else dict(
        schema='mobius-signed-lag-checker-development-v1', synthetic_only=True, attempts=[])
    report['attempts'].append(attempt)
    report['successful'] = result.wasSuccessful()
    report['total_test_invocations'] = sum(a['tests_run'] for a in report['attempts'])
    report['charged_work_units'] = sum(a['charged_work_units'] for a in report['attempts'])
    report['wall_seconds'] = sum(a['wall_seconds'] for a in report['attempts'])
    report['peak_rss_kib'] = max(a['peak_rss_kib'] for a in report['attempts'])
    path.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(attempt, sort_keys=True))
    raise SystemExit(0 if result.wasSuccessful() else 1)
