"""Hand-built lifts; no producer or saved scientific-source import/read."""
import itertools
import unittest
from fractions import Fraction as Q
import check_mobius_quadratic_contraction_064 as C
from prime_bank_candidates import Meter as PipelineMeter

METERS = []


def meter():
    m = C.Meter(cap=1_000_000_000)
    METERS.append(m)
    return m


def lift(H, K, pf=None, pg=None):
    y = (H + 1)*K if K else 1
    if pf is None:
        pf = [['0']*H for _ in range(2)]
    if pg is None:
        pg = [[['0']*K for _ in range(H)] for _ in range(2)]
    return {'schema': 'mobius-factored-quadratic-repair-v1',
        'parameters': {'alpha': '1/5', 'gamma': '5/28', 'tau': '1/2',
            'primes': [2, 3, 5], 'p': 3, 'q': 5},
        'N': max(64, y), 'y': y, 'H': H, 'K': K, 'rule': 'raw',
        'arithmetic_radius': max(H, K), 'ordinary_mu_through_radius': [0]*max(H, K),
        'linear_terms': pf, 'long_kernels_after_fill': pg,
        'expression': 'hand-built conditional local fixture',
        'same_u_sequence_in_both_factors': True, 'arithmetic_degree_at_most': 2,
        'formal_source_only_factorization_reviewed': True, 'producer_exact_replay': True,
        'independent_quadratic_schema_admission': False,
        'independent_whole_completion_admission_still_required': True,
        'uniform_quadratic_variation_bound_proved': False, 'RH_proved': False}


def certificate(source, rows, primes=()):
    endpoints = []
    for ratio, endpoint in zip(('3/5', '1'), rows):
        terms = [{'j': j, 'terms': [{'index': k, 'coefficient': str(Q(v))}
            for k, v in sorted(row.items())]} for j, row in enumerate(endpoint, 1)]
        price = sum((abs(Q(v)) for row in endpoint for v in row.values()), Q(0))
        endpoints.append({'ratio': ratio, 'rows': terms, 'l1': str(price)})
    return {'schema': 'mobius-quadratic-contraction-v1',
        **{k: source[k] for k in ('N', 'y', 'H', 'K')},
        'conditioned_primes': list(primes), 'endpoints': endpoints,
        'budget': str(max(Q(e['l1']) for e in endpoints))}


def diagonal():
    source = lift(2, 2, [['0', '0'], ['0', '3']],
        [[['0', '0'], ['0', '1']], [['0', '0'], ['0', '2']]])
    rows = [[{1: -1, 2: 1}, {2: -1}], [{1: -5, 2: 5}, {1: 3, 2: -2}]]
    return source, certificate(source, rows)


def parity(primes=()):
    source = lift(6, 0, [['0']*5 + ['1'] for _ in range(2)])
    if primes == (2, 3):
        row = [{1: 2}, {}, {1: -1}, {}, {1: -1}, {1: 1}]
    elif primes == (2,):
        row = [{3: -2}, {1: 1, 3: 1}, {1: -1}, {}, {1: -1}, {1: 1}]
    else:
        row = [{3: -1, 6: 1}, {2: -1, 3: 1}, {2: 1}, {}, {1: -1}, {1: 1}]
    return source, certificate(source, [row, row], primes)


def sign_mu(n, signs, m):
    value = 1
    d = 2
    while d*d <= n:
        m.charge(8)
        if n % d == 0:
            n //= d
            if n % d == 0:
                return 0
            value *= signs[d]
        d += 1
    if n > 1:
        value *= signs[n]
    return value


def floor_inverse(filled, m):
    # Independent triangular elimination of the full floor matrix.
    result = [Q(0)]*len(filled)
    for d in range(len(filled), 0, -1):
        result[d-1] = filled[d-1]
        for j in range(d+1, len(filled)+1):
            result[d-1] -= result[j-1]*(j // d)
            m.charge(100)
    return result


class ContractionCheckerTests(unittest.TestCase):
    def test_shared_prime_diagonal_is_constant_not_mu_of_four(self):
        m = meter(); source, cert = diagonal()
        out = C.verify_contraction(source, cert, m)
        self.assertEqual(out['endpoint_l1'], ['3', '15'])
        self.assertTrue(out['shared_prime_overlap_preserved'])
        self.assertEqual(cert['endpoints'][0]['rows'][0]['terms'][0],
            {'index': 1, 'coefficient': '-1'})

    def test_gcd_overlap_six_times_ten_gives_fifteen(self):
        m = meter(); source = lift(6, 10)
        for endpoint in source['long_kernels_after_fill']:
            endpoint[5][9] = '1'
        rows = [{15: -1, 30: 1}, {5: 1, 30: -1}, {5: -1}, {}, {10: 1}, {10: -1}]
        out = C.verify_contraction(source, certificate(source, [rows, rows]), m)
        self.assertEqual(out['budget'], '7')

    def test_squareful_outer_index_zero_without_deleting_squareful_d(self):
        m = meter(); source = lift(4, 0, [['0', '0', '0', '1'] for _ in range(2)])
        rows = [{2: -1}, {2: 1}, {1: -1}, {1: 1}]
        out = C.verify_contraction(source, certificate(source, [rows, rows]), m)
        self.assertEqual(out['budget'], '4')

    def test_squareful_inner_index_zero(self):
        m = meter(); source = lift(1, 4)
        for endpoint in source['long_kernels_after_fill']:
            endpoint[0][3] = '999'
        self.assertEqual(C.verify_contraction(source, certificate(source, [[{}], [{}]]), m)['budget'], '0')

    def test_linear_quadratic_cancellation_inside_absolute_value(self):
        m = meter(); source = lift(2, 1, [['0', '9'] for _ in range(2)],
            [[['0'], ['9']] for _ in range(2)])
        cert = certificate(source, [[{}, {}], [{}, {}]])
        out = C.verify_contraction(source, cert, m)
        self.assertEqual(out['budget'], '0')
        self.assertTrue(out['linear_minus_quadratic_coalesced'])

    def test_empty_conditioning_and_two_prime_parity(self):
        m = meter()
        for primes, budget in (((), '7'), ((2,), '7'), ((2, 3), '5')):
            source, cert = parity(primes)
            out = C.verify_contraction(source, cert, m)
            self.assertEqual(out['budget'], budget)
            self.assertEqual(out['all_radius_primes_conditioned'], False)

    def test_conditioning_shared_diagonal_does_not_flip_constant(self):
        m = meter(); source, _ = diagonal()
        cert = certificate(source, [[{1: -2}, {1: 1}], [{1: -10}, {1: 5}]], (2,))
        out = C.verify_contraction(source, cert, m)
        self.assertTrue(out['all_radius_primes_conditioned'])
        self.assertEqual(out['budget'], '15')
        self.assertTrue(out['all_conditioned_is_finite_arithmetic_only'])

    def test_independent_floor_inverse_all_prime_signs_and_intermediate_ratios(self):
        m = meter(); source, cert = diagonal()
        out = C.verify_contraction(source, cert, m)
        for sign in (-1, 1):
            signs = {2: sign}
            endpoint_coefficients = []
            for e in range(2):
                filled = []
                for d in range(source['H']):
                    filled.append(Q(source['linear_terms'][e][d]) - sum((Q(v)*sign_mu(ell, signs, m)
                        for ell, v in enumerate(source['long_kernels_after_fill'][e][d], 1)), Q(0)))
                coefficients = ([Q(-1 + sign), Q(-sign)] if e == 0
                    else [Q(-5 + 5*sign), Q(3 - 2*sign)])
                if sign == -1:
                    self.assertEqual(coefficients, floor_inverse(filled, m))
                endpoint_coefficients.append(coefficients)
                for row, actual in zip(cert['endpoints'][e]['rows'], coefficients):
                    symbolic = sum((Q(t['coefficient'])*sign_mu(t['index'], signs, m) for t in row['terms']), Q(0))
                    self.assertEqual(symbolic, actual)
            for t in (Q(0), Q(1, 7), Q(1, 2), Q(5, 6), Q(1)):
                price = sum((abs((1-t)*a+t*b) for a, b in zip(*endpoint_coefficients)), Q(0))
                m.charge(100)
                self.assertLessEqual(price, Q(out['budget']))

    def test_conditioned_bound_all_remaining_sign_assignments(self):
        m = meter(); source, cert = parity((2,))
        out = C.verify_contraction(source, cert, m)
        for s3, s5 in itertools.product((-1, 1), repeat=2):
            signs = {2: -1, 3: s3, 5: s5}
            # Hand-derived A_j sequence, including both empty middle rows.
            A = [sign_mu(6, signs, m), sign_mu(3, signs, m), sign_mu(2, signs, m), 0, 0, 1, 0]
            values = [A[j]-A[j+1] for j in range(6)]
            self.assertEqual(values, [sum((Q(t['coefficient'])*sign_mu(t['index'], signs, m)
                for t in row['terms']), Q(0)) for row in cert['endpoints'][0]['rows']])
            self.assertLessEqual(sum(map(abs, values)), Q(out['budget']))

    def test_unit_zero_kernel_and_fractional_endpoints(self):
        m = meter(); source = lift(1, 0, [['1/257'], ['-257/1026']])
        cert = certificate(source, [[{1: '1/257'}], [{1: '-257/1026'}]])
        out = C.verify_contraction(source, cert, m)
        self.assertEqual(out['budget'], '257/1026')
        self.assertTrue(out['all_radius_primes_conditioned'])

    def test_recorded_mu_values_and_producer_flags_do_not_pay_source(self):
        m = meter(); source, cert = diagonal()
        source['ordinary_mu_through_radius'] = [123, 456]
        out = C.verify_contraction(source, cert, m)
        self.assertFalse(out['recorded_ordinary_mu_used'])
        self.assertFalse(out['original_source_binding_proved'])
        self.assertTrue(out['independent_source_admission_required'])
        self.assertIn('verify_quadratic(lift,repair)', out['source_binding_condition'])
        for key in ('uniform_N_growth_proved', 'whole_signed_target_bound_proved', 'RH_proved', 'scientific_source_or_LP_evaluated'):
            self.assertFalse(out[key])

    def test_missing_extra_zero_and_signed_terms(self):
        m = meter()
        for mutation in ('missing', 'extra', 'zero', 'sign'):
            source, cert = diagonal(); terms = cert['endpoints'][0]['rows'][0]['terms']
            if mutation == 'missing': terms.pop()
            elif mutation == 'extra': terms.append({'index': 3, 'coefficient': '1'})
            elif mutation == 'zero': terms[0]['coefficient'] = '0'
            else: terms[0]['coefficient'] = '1'
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)

    def test_squareful_duplicate_unsorted_and_boolean_indices(self):
        m = meter()
        for value in (0, 4, True, 1000000000):
            source, cert = diagonal(); cert['endpoints'][0]['rows'][0]['terms'][1]['index'] = value
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)
        for mutation in ('duplicate', 'unsorted'):
            source, cert = diagonal(); terms = cert['endpoints'][0]['rows'][0]['terms']
            if mutation == 'duplicate': terms[1]['index'] = 1
            else: terms.reverse()
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)

    def test_both_endpoint_prices_and_maximum_budget(self):
        m = meter()
        for e in (0, 1):
            for value in ('0', '999'):
                source, cert = diagonal(); cert['endpoints'][e]['l1'] = value
                with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)
        for value in ('3', '0', '999'):
            source, cert = diagonal(); cert['budget'] = value
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)

    def test_both_ratios_and_affine_endpoint_coverage(self):
        m = meter()
        for e in (0, 1):
            source, cert = diagonal(); cert['endpoints'][e]['ratio'] = '2/3'
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)
            source, cert = diagonal(); source['linear_terms'][e][0] = '1'
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)

    def test_actual_distinct_bounded_conditioned_primes(self):
        m = meter()
        for primes in ([1], [True], [2, 2], [3, 2], [4], [7], '2'):
            source, cert = parity(); cert['conditioned_primes'] = primes
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)

    def test_exact_schema_and_forged_scope_flags(self):
        m = meter()
        for key, value in (('schema', 'wrong'), ('RH_proved', True), ('source_verified', True), ('uniform_N_growth_proved', True)):
            source, cert = diagonal(); cert[key] = value
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)
        for section in ('lift', 'endpoint', 'row', 'term'):
            source, cert = diagonal()
            obj = {'lift': source, 'endpoint': cert['endpoints'][0], 'row': cert['endpoints'][0]['rows'][0],
                'term': cert['endpoints'][0]['rows'][0]['terms'][0]}[section]
            obj['unexpected'] = True
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)

    def test_parameter_copy_and_strict_horizon_capacities(self):
        m = meter()
        for key in ('N', 'y', 'H', 'K'):
            source, cert = diagonal(); cert[key] = True
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)
        for key, value in (('H', 0), ('H', True), ('H', 4097), ('K', -1), ('K', True), ('N', True), ('y', 0)):
            source, cert = diagonal(); source[key] = value
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)
        for H, K in ((1, 65537), (4096, 256)):
            source, cert = diagonal(); source.update(H=H, K=K)
            with self.assertRaises(OverflowError): C.verify_contraction(source, cert, m)
        source, cert = diagonal(); source['K'] = 1
        with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)

    def test_complete_source_and_claimed_array_shapes(self):
        m = meter()
        for key in ('linear_terms', 'long_kernels_after_fill'):
            for mutation in ('endpoint', 'row', 'column'):
                source, cert = diagonal()
                if mutation == 'endpoint': source[key].pop()
                elif mutation == 'row' or key == 'linear_terms': source[key][1].pop()
                else: source[key][1][0].pop()
                with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)
        for mutation in ('endpoint', 'row', 'j'):
            source, cert = diagonal()
            if mutation == 'endpoint': cert['endpoints'].pop()
            elif mutation == 'row': cert['endpoints'][1]['rows'].pop()
            else: cert['endpoints'][1]['rows'][1]['j'] = 1
            with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)

    def test_canonical_rational_caps_at_all_boundaries(self):
        m = meter()
        for value in (True, 1.0, '1.0', '2/2', '-0', '1/0', str(1 << 4097)):
            for field in ('pf', 'pg', 'term', 'ratio', 'l1', 'budget'):
                source, cert = diagonal()
                if field == 'pf': source['linear_terms'][1][0] = value
                elif field == 'pg': source['long_kernels_after_fill'][1][0][0] = value
                elif field == 'term': cert['endpoints'][1]['rows'][0]['terms'][0]['coefficient'] = value
                elif field == 'budget': cert['budget'] = value
                else: cert['endpoints'][1][field] = value
                with self.assertRaises(ValueError): C.verify_contraction(source, cert, m)

    def test_charge_only_pipeline_meter_work_memory_and_intermediate_caps(self):
        m = PipelineMeter(); METERS.append(m); source, cert = diagonal()
        self.assertTrue(C.verify_contraction(source, cert, m)['verified'])
        self.assertGreater(m.operations, 100)
        tiny = C.Meter(cap=1); METERS.append(tiny)
        with self.assertRaises(OverflowError): C.verify_contraction(source, cert, tiny)
        m = meter()
        with self.assertRaises(MemoryError): C._memory(C.MAX_MEMORY_BYTES+1, m)
        with self.assertRaises(OverflowError): C.MASS._bounded(Q(1 << 32769), m)


if __name__ == '__main__':
    try:
        unittest.main()
    finally:
        print('SYNTHETIC_WORK module=check_mobius_quadratic_contraction_064 operations='
            + str(sum(m.operations for m in METERS)))
