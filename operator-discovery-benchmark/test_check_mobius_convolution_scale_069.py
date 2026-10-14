"""Fresh scalar and adversarial 069 tests; no producer or old suite imports."""
import copy
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
import json
from math import isqrt, prod
from pathlib import Path
import resource
import time
import unittest
from unittest import mock
import check_mobius_convolution_scale_069 as C


class ChargeOnly:
    def __init__(self):
        self.operations = 0

    def charge(self, n=1):
        self.operations += n


METER = ChargeOnly()


def context():
    return C._Context(METER)


def trial_mu(n):
    answer, divisor = 1, 2
    while divisor*divisor <= n:
        if n % divisor == 0:
            n //= divisor
            answer = -answer
            if n % divisor == 0:
                return 0
        divisor += 1
    return -answer if n > 1 else answer


def W(N, base, d):
    return 4*N//(base*d)-3*(2*N//(base*d))+2*(N//(base*d))


def rounded_weight(index_product, text):
    sigma = Q(text)
    target = C.GRID**sigma.denominator*index_product**sigma.numerator
    proposal = int(C.GRID*index_product**float(sigma))
    while proposal**sigma.denominator < target:
        proposal += 1
    while proposal and (proposal-1)**sigma.denominator >= target:
        proposal -= 1
    return Q(proposal, C.GRID)


def tensor_fixture_polynomial(kappa, cutoffs, direct=0):
    """Tiny scalar forward differences complement checker's tuple expansion."""
    R, degree = len(kappa)-1, len(cutoffs)

    @lru_cache(None)
    def kernel(v, level):
        if v > R:
            return 0
        if level == 1:
            return kappa[v]
        return sum(kernel(v*t, level-1) for t in range(1, R//v+1))

    polynomial = {(): direct}
    for mask in range(1, 1 << degree):
        sizes = [cutoffs[i] for i in range(degree) if mask & (1 << i)]
        m = len(sizes)
        for indices in product(*(range(1, size+1) for size in sizes)):
            value = 0
            for bits in product((0, 1), repeat=m):
                shifted = tuple(a+b for a, b in zip(indices, bits))
                if any(a > size for a, size in zip(shifted, sizes)):
                    continue
                value += (-1)**sum(bits)*kernel(prod(shifted), m)
            key = tuple(sorted(a for a in indices if a != 1))
            polynomial[key] = polynomial.get(key, 0)+(-1)**(m+1)*value
    return {key: value for key, value in polynomial.items() if value}


def fixture(N=6, y=3, max_j=12, requests=None, sigmas=None, p=2, q=3):
    requests = ([['1/2', '1/2'], ['1/3', '2/3'], ['1/3']*3]
                if requests is None else requests)
    sigmas = ['0', '1/2', '2/3', '1'] if sigmas is None else sigmas
    D = 4*N//p
    cert = dict(schema=C.SCHEMA, N=N, y=y, max_j=max_j,
        parameters=dict(primes=[p, q], p=p, q=q, alpha='1/2', gamma='1/3', tau='1/4'),
        requests=requests, price_exponents=sigmas, coefficient_grid=C.GRID,
        annihilators=[], endpoints=[], universal_convolution_identity_proved=True,
        smaller_mu_query_radius_verified=True, conditional_prefix_bounds_paid=False,
        uniform_head_bound_proved=False, RH_proved=False)
    for degree in sorted({len(request) for request in requests}):
        cert['annihilators'].append(dict(degree=degree,
            coefficients=[(-1)**mask.bit_count() for mask in range(1 << degree)],
            system_rank=1 << degree))
    for ratio in (Q(p, q), Q(1)):
        den = ratio.denominator
        full = [0]+[den*W(N, p, d)-ratio.numerator*W(N, q, d) for d in range(1, D+1)]+[0]
        tail = [0]+[-full[d] if d > y else 0 for d in range(1, D+1)]+[0]
        endpoint = dict(ratio=str(ratio), denominator=den, rows=[])
        for j in range(1, max_j+1):
            R = D//j
            kappa = [0]+[tail[j*n]-(tail[(j+1)*n] if (j+1)*n <= D else 0) for n in range(1, R+1)]
            direct = sum(trial_mu(n)*(full[j*n]-(full[(j+1)*n] if (j+1)*n <= D else 0))
                         for n in range(1, R+1))
            row = dict(j=j, R=R, direct_scaled=direct, unit_kernel_scaled=kappa[1],
                       models=[], plans=[], selected_model=0)
            cutoffs_seen = []
            for request in requests:
                cutoffs = [max(v for v in range(1, R+1)
                    if v**Q(text).denominator <= R**Q(text).numerator) for text in request]
                if cutoffs not in cutoffs_seen:
                    cutoffs_seen.append(cutoffs)
                    degree = len(cutoffs)
                    poly = tensor_fixture_polynomial(kappa, cutoffs, direct)
                    prices = []
                    for sigma in sigmas:
                        values = [Q(0)]*(degree+1)
                        values[0] = Q(abs(poly.get((), 0)), den)
                        for indices, coefficient in poly.items():
                            if indices:
                                values[len(indices)] += Q(abs(coefficient), den)*rounded_weight(prod(indices), sigma)
                        prices.append(dict(sigma=sigma, coefficients=[str(v) for v in values]))
                    constant = poly.get((), 0)
                    row['models'].append(dict(degree=degree, cutoffs=cutoffs,
                        support_min=prod(v+1 for v in cutoffs), mu_query_radius=max(cutoffs),
                        constant_scaled=constant,
                        terms=[dict(indices=list(indices), coefficient_scaled=value)
                               for indices, value in sorted(poly.items()) if indices],
                        conditional_prices=prices,
                        scalar_box_witness=dict(prefix_values='M(1)=1,M(s)=0 for s>=2',
                            value=str(Q(constant, den)), actual_mobius_assignment=False)))
                row['plans'].append(dict(exponents=request, cutoffs=cutoffs, model_index=cutoffs_seen.index(cutoffs)))
            row['selected_model'] = min(range(len(row['models'])), key=lambda i: (
                sum(Q(v) for v in row['models'][i]['conditional_prices'][0]['coefficients']),
                row['models'][i]['mu_query_radius'], len(row['models'][i]['terms']), i))
            endpoint['rows'].append(row)
        cert['endpoints'].append(endpoint)
    return cert


def accept(cert):
    return C.verify_control(cert, METER)


class Tests(unittest.TestCase):
    def reject(self, cert):
        with self.assertRaises((ValueError, OverflowError, MemoryError)):
            accept(cert)

    def test_complete_mixed_certificate_and_actual_unit_rows(self):
        cert = fixture()
        verdict = accept(cert)
        self.assertTrue(verdict['verified'])
        self.assertTrue(verdict['independent_scalar_convolution_replay'])
        self.assertFalse(verdict['conditional_prefix_bounds_paid'])
        self.assertFalse(verdict['original_source_binding_proved'])
        self.assertFalse(verdict['scalar_box_witness_is_actual_mobius'])
        for endpoint in verdict['endpoints']:
            self.assertEqual(endpoint['rows'][-1]['R'], 1)
            self.assertEqual(endpoint['rows'][-1]['models'][0]['mu_query_radius'], 1)

    def test_empty_row_domain_keeps_face_audit(self):
        verdict = accept(fixture(max_j=0))
        self.assertEqual(verdict['endpoints'][0]['actual_head_variation'], '0')

    def test_degree_eight_complete_repeated_faces(self):
        verdict = accept(fixture(N=2, max_j=4, y=1, requests=[['1/8']*8]))
        self.assertTrue(verdict['full_face_system_verified'])

    def test_rectangle_boundary_product_difference(self):
        kappa = [0, 2, -1, 3, 0, -2, 5, 1, -4, 0, 2, 0, 1]
        cutoffs = [2, 5]
        expected = tensor_fixture_polynomial(kappa, cutoffs)
        actual = C._prefix_polynomial(kappa, cutoffs, [1, -1, -1, 1], context())
        self.assertEqual(actual, expected)
        self.assertTrue(any(5 in indices for indices in actual))

    def test_three_rectangle_edges_and_sorted_coalescing(self):
        kappa = [0]+[((n*7) % 5)-2 for n in range(1, 19)]
        cutoffs = [2, 2, 4]
        expected = tensor_fixture_polynomial(kappa, cutoffs)
        actual = C._prefix_polynomial(kappa, cutoffs, [(-1)**m.bit_count() for m in range(8)], context())
        self.assertEqual(actual, expected)
        self.assertTrue(all(tuple(sorted(k)) == k and 1 not in k for k in actual))

    def test_ordered_factor_count_matches_enumeration(self):
        for n in range(1, 25):
            for slots in range(4):
                expected = int(n == 1) if slots == 0 else sum(prod(v) == n for v in product(range(1, n+1), repeat=slots))
                self.assertEqual(C._factor_count(n, slots, context()), expected)

    def test_exact_scalar_kernels_against_nested_divisor_loops(self):
        kappa = [0, 2, -3, 0, 4, 1, -5, 2]
        actual = C._scalar_kernels(kappa, 4, context())
        for level in range(1, 5):
            for v in range(1, 8):
                expected = sum(kappa[v*prod(factors)] for factors in product(range(1, 8//v+1), repeat=level-1) if v*prod(factors) <= 7)
                self.assertEqual(actual[level][v], expected)

    def test_rational_cutoff_exact_near_root(self):
        self.assertEqual(C._power_floor(81, '1/2', context()), 9)
        self.assertEqual(C._power_floor(80, '1/2', context()), 8)
        self.assertEqual(C._power_floor(1, '1/257', context()), 1)
        self.assertEqual(C._power_floor(97, '0', context()), 1)

    def test_upward_rounding_perfect_and_irrational(self):
        self.assertEqual(C._ceil_weight(9, Q(1, 2), context()), Q(3))
        rounded = C._ceil_weight(2, Q(1, 2), context())
        self.assertEqual(rounded.numerator*C.GRID//rounded.denominator, isqrt(2*C.GRID*C.GRID)+1)
        self.assertGreaterEqual(rounded**2, 2)
        self.assertLess((rounded-Q(1, C.GRID))**2, 2)
        self.assertEqual(C._ceil_weight(111, Q(0), context()), 1)
        self.assertEqual(C._ceil_weight(111, Q(1), context()), 111)

    def test_exact_degree_prices_keep_constant_and_all_signs(self):
        poly = {(): -7, (2,): -3, (2, 3): 5, (3, 3): -4}
        values = C._degree_prices(poly, 3, Q(0), 3, context())
        self.assertEqual(values, [Q(7, 3), Q(1), Q(3), Q(0)])

    def test_false_paid_prefix_premise(self):
        cert = fixture()
        cert['conditional_prefix_bounds_paid'] = True
        self.reject(cert)

    def test_false_uniform_head_claim(self):
        cert = fixture()
        cert['uniform_head_bound_proved'] = True
        self.reject(cert)

    def test_false_RH_claim(self):
        cert = fixture()
        cert['RH_proved'] = True
        self.reject(cert)

    def test_fake_scalar_assignment_not_actual_arithmetic(self):
        cert = fixture()
        cert['endpoints'][0]['rows'][0]['models'][0]['scalar_box_witness']['actual_mobius_assignment'] = True
        self.reject(cert)

    def test_fake_scalar_box_linear_witness_on_new_small_sources(self):
        for k in range(1, 7):
            cert = fixture(N=15*k, y=16*k, max_j=1, p=3, q=5,
                           requests=[['1/2', '1/2'], ['1/3', '2/3']], sigmas=['1/2'])
            verdict = accept(cert)
            for model in cert['endpoints'][1]['rows'][0]['models']:
                self.assertGreaterEqual(min(model['cutoffs']), 2)
                self.assertEqual(model['constant_scaled'], (k+1)//2)
                self.assertEqual(model['scalar_box_witness']['value'], str((k+1)//2))
            self.assertFalse(verdict['scalar_box_witness_is_actual_mobius'])

    def test_wrong_scalar_box_value(self):
        cert = fixture()
        cert['endpoints'][0]['rows'][0]['models'][0]['scalar_box_witness']['value'] = '100'
        self.reject(cert)

    def test_duplicate_scalar_price_exponent(self):
        cert = fixture()
        cert['price_exponents'][1] = cert['price_exponents'][0]
        self.reject(cert)

    def test_nonprime_registered_source_rejected(self):
        cert = fixture()
        cert['parameters']['primes'] = [2, 3, 4]
        self.reject(cert)

    def test_input_tree_and_integer_capacity(self):
        with self.assertRaises(OverflowError):
            context().preflight(1 << (C.MAX_BITS+1))
        recursive = []
        recursive.append(recursive)
        with self.assertRaises(OverflowError):
            context().preflight(recursive)

    def test_input_and_scratch_share_storage_cap(self):
        ctx = context()
        ctx.preflight(['a'*1000]*10)
        ctx.scratch_base = 8192
        with mock.patch.object(C, 'MAX_MEMORY_BYTES', 32000):
            with self.assertRaises(MemoryError):
                ctx.prospective(100, 192)

    def test_omitted_signed_term(self):
        cert = fixture()
        model = next(m for e in cert['endpoints'] for r in e['rows'] for m in r['models'] if m['terms'])
        model['terms'].pop()
        self.reject(cert)

    def test_changed_sign_before_absolute_price(self):
        cert = fixture()
        term = next(t for e in cert['endpoints'] for r in e['rows'] for m in r['models'] for t in m['terms'])
        term['coefficient_scaled'] *= -1
        self.reject(cert)

    def test_duplicate_uncoalesced_term(self):
        cert = fixture()
        model = next(m for e in cert['endpoints'] for r in e['rows'] for m in r['models'] if m['terms'])
        model['terms'].append(copy.deepcopy(model['terms'][0]))
        self.reject(cert)

    def test_unit_prefix_cannot_remain_in_terms(self):
        cert = fixture()
        term = next(t for e in cert['endpoints'] for r in e['rows'] for m in r['models'] for t in m['terms'])
        term['indices'].insert(0, 1)
        self.reject(cert)

    def test_changed_signed_constant(self):
        cert = fixture()
        cert['endpoints'][0]['rows'][0]['models'][0]['constant_scaled'] += 1
        self.reject(cert)

    def test_price_rounding_cannot_be_downward(self):
        cert = fixture()
        prices = cert['endpoints'][0]['rows'][0]['models'][0]['conditional_prices'][1]['coefficients']
        index = next(i for i, text in enumerate(prices) if i and Q(text))
        prices[index] = str(Q(prices[index])-Q(1, C.GRID))
        self.reject(cert)

    def test_every_degree_price_must_be_present(self):
        cert = fixture()
        cert['endpoints'][0]['rows'][0]['models'][0]['conditional_prices'][0]['coefficients'].pop()
        self.reject(cert)

    def test_wrong_face_even_with_normalized_unit(self):
        cert = fixture()
        cert['annihilators'][0]['coefficients'][-1] = -1
        self.reject(cert)

    def test_wrong_face_rank_claim(self):
        cert = fixture()
        cert['annihilators'][0]['system_rank'] -= 1
        self.reject(cert)

    def test_missing_annihilator_degree(self):
        cert = fixture()
        cert['annihilators'].pop()
        self.reject(cert)

    def test_exponent_one_cannot_query_same_scale(self):
        cert = fixture()
        cert['requests'][0] = ['0', '1']
        self.reject(cert)

    def test_insufficient_exponent_sum(self):
        cert = fixture()
        cert['requests'][0] = ['1/3', '1/3']
        self.reject(cert)

    def test_unsorted_mixed_exponents(self):
        cert = fixture()
        cert['requests'][1].reverse()
        self.reject(cert)

    def test_duplicate_request(self):
        cert = fixture()
        cert['requests'].append(copy.deepcopy(cert['requests'][0]))
        self.reject(cert)

    def test_noncanonical_rational(self):
        cert = fixture()
        cert['price_exponents'][0] = '0/2'
        self.reject(cert)

    def test_boolean_scaled_coefficient_rejected(self):
        cert = fixture()
        cert['endpoints'][0]['rows'][0]['direct_scaled'] = False
        self.reject(cert)

    def test_cutoff_power_tampering(self):
        cert = fixture()
        cert['endpoints'][0]['rows'][0]['plans'][1]['cutoffs'][0] += 1
        self.reject(cert)

    def test_support_gate_tampering(self):
        cert = fixture()
        cert['endpoints'][0]['rows'][0]['models'][0]['support_min'] -= 1
        self.reject(cert)

    def test_query_radius_cannot_be_current_support(self):
        cert = fixture()
        row = cert['endpoints'][0]['rows'][0]
        row['models'][0]['mu_query_radius'] = row['R']
        self.reject(cert)

    def test_realized_rectangles_reuse_model(self):
        cert = fixture(requests=[['1/2', '1/2'], ['3/7', '4/7']])
        verdict = accept(cert)
        self.assertTrue(verdict['verified'])
        unit = cert['endpoints'][0]['rows'][-1]
        self.assertEqual(len(unit['models']), 1)
        self.assertEqual([p['model_index'] for p in unit['plans']], [0, 0])

    def test_incorrect_reuse_model_index(self):
        cert = fixture()
        cert['endpoints'][0]['rows'][-1]['plans'][1]['model_index'] = 1
        self.reject(cert)

    def test_selection_is_exact_conditional_first_sigma(self):
        cert = fixture()
        row = next(r for e in cert['endpoints'] for r in e['rows'] if len(r['models']) > 1)
        row['selected_model'] = (row['selected_model']+1) % len(row['models'])
        self.reject(cert)

    def test_both_endpoints_and_every_row_required(self):
        cert = fixture()
        cert['endpoints'][0]['rows'].pop()
        self.reject(cert)
        cert = fixture()
        cert['endpoints'].reverse()
        self.reject(cert)

    def test_unknown_scientific_or_scope_field_rejected(self):
        cert = fixture()
        cert['mu_signs'] = [1, -1]
        self.reject(cert)

    def test_checker_has_no_producer_dependency(self):
        source = Path(C.__file__).read_text()
        self.assertNotIn('import numpy', source)
        self.assertNotIn('import mobius_convolution_scale_069', source)
        self.assertNotIn('import check_mobius_floor_control_068', source)

    def test_actual_mu_not_used_in_polynomial_or_price(self):
        with mock.patch.object(C, '_ordinary_mu', side_effect=AssertionError('actual arithmetic used')):
            poly = C._prefix_polynomial([0, 1, -2, 3, -1], [2, 2], [1, -1, -1, 1], context())
            prices = C._degree_prices(poly, 1, Q(1, 2), 2, context())
        self.assertEqual(len(prices), 3)

    def test_resource_work_storage_and_power_caps(self):
        with self.assertRaises(OverflowError):
            C.verify_control(fixture(), C.Meter(cap=0))
        with self.assertRaises(OverflowError):
            context().prospective(C.MAX_ENTRIES+1)
        with self.assertRaises(MemoryError):
            context().prospective(1, C.MAX_MEMORY_BYTES)
        with self.assertRaises(OverflowError):
            C._power_floor(100, '1/100000', context())

    def test_meter_deadline_and_bad_configuration(self):
        for cap in (-1, True, C.MAX_WORK+1):
            with self.assertRaises(ValueError):
                C.Meter(cap=cap)
        meter = C.Meter()
        meter.deadline = time.monotonic()-1
        with self.assertRaises(TimeoutError):
            meter.charge()


if __name__ == '__main__':
    started = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    path = Path(__file__).with_name('mobius_convolution_scale_checker_069_development.json')
    history = json.loads(path.read_text()) if path.exists() else dict(schema='mobius-convolution-scale-checker-development-v1', attempts=[])
    status = Path('/proc/self/status').read_text().splitlines()
    linux_peak = next(int(line.split()[1])*1024 for line in status if line.startswith('VmHWM:'))
    history['attempts'].append(dict(attempt=len(history['attempts'])+1,
        tests_run=result.testsRun, passed=result.wasSuccessful(),
        failures=[dict(test=str(test), traceback=trace) for test, trace in result.failures],
        errors=[dict(test=str(test), traceback=trace) for test, trace in result.errors],
        charged_work_units=METER.operations, elapsed_seconds=time.monotonic()-started,
        process_peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,
        rusage_peak_may_include_inherited_launcher_high_water=True,
        linux_current_process_peak_rss_bytes=linux_peak,
        unchanged_historical_suite_replayed=False, scientific_study_replayed=False,
        producer_imported=False, scientific_arrays_read=False, hashes_created=False))
    path.write_text(json.dumps(history, indent=2)+'\n')
    raise SystemExit(0 if result.wasSuccessful() else 1)
