"""Independent squarefree quadratic contraction, conditional on lift admission.

No producer, saved scientific arrays, or recorded ordinary-mu values are used.
The source-binding rule is check_mobius_quadratic_source_064.verify_quadratic;
this local checker proves a finite bound for the supplied Pf/PG arrays only.
"""
from fractions import Fraction as Q
from math import gcd, isqrt
import check_mobius_mass_conservation_060 as MASS

Meter = MASS.Meter
MAX_H = 4096
MAX_B = 65536
MAX_KERNEL_CELLS = 1_000_000
MAX_MEMORY_BYTES = 512 * 1024 * 1024
LIFT_FIELDS = ('schema', 'parameters', 'N', 'y', 'H', 'rule', 'K',
    'arithmetic_radius', 'ordinary_mu_through_radius', 'linear_terms',
    'long_kernels_after_fill', 'expression', 'same_u_sequence_in_both_factors',
    'arithmetic_degree_at_most', 'formal_source_only_factorization_reviewed',
    'producer_exact_replay', 'independent_quadratic_schema_admission',
    'independent_whole_completion_admission_still_required',
    'uniform_quadratic_variation_bound_proved', 'RH_proved')


def _memory(size, m):
    m.charge()
    if size > MAX_MEMORY_BYTES:
        raise MemoryError('quadratic contraction prospective storage cap')


def _qbytes(value):
    # Conservative local-object estimate, including dict/list references.
    return 384 + (abs(value.numerator).bit_length() + value.denominator.bit_length() + 7) // 8


def _squarefree(n, m):
    for d in range(2, isqrt(n) + 1):
        m.charge(4)
        if n % (d*d) == 0:
            return False
    return True


def _sieve(B, m):
    sf = bytearray(b'\x01') * (B + 1)
    sf[0] = 0
    m.charge(B + 1)
    for d in range(2, isqrt(B) + 1):
        for n in range(d*d, B + 1, d*d):
            sf[n] = 0
            m.charge(2)
    return sf


def _condition(index, conditioned, m):
    # Called only on squarefree keys. Each prime is removed exactly once.
    key, sign, rest, d = index, 1, index, 2
    while d*d <= rest:
        m.charge(4)
        if rest % d == 0:
            rest //= d
            if d in conditioned:
                key //= d
                sign = -sign
        d += 1
    if rest > 1 and rest in conditioned:
        key //= rest
        sign = -sign
    return key, sign


def _endpoint_arrays(lift, e, H, K, m):
    fs, kernels = lift['linear_terms'][e], lift['long_kernels_after_fill'][e]
    if type(fs) is not list or len(fs) != H or type(kernels) is not list or len(kernels) != H:
        raise ValueError('every Pf/PG short row at each endpoint')
    size = 4096 + 128*H + 2*MAX_B
    pf, pg = [], []
    for text in fs:
        value = MASS._rational(text, m)
        size += _qbytes(value)
        _memory(size, m)
        pf.append(value)
    for row in kernels:
        if type(row) is not list or len(row) != K:
            raise ValueError('every PG inverse column at each endpoint')
        parsed = []
        for text in row:
            value = MASS._rational(text, m)
            size += _qbytes(value)
            _memory(size, m)
            parsed.append(value)
        pg.append(parsed)
    return pf, pg, size


def _add(terms, index, value, m, base_size, memory):
    m.charge(4)
    if not value:
        return
    old = terms.get(index, Q(0))
    new = MASS._bounded(old + value, m)
    memory[0] -= _qbytes(old) if index in terms else 0
    if new:
        terms[index] = new
        memory[0] += _qbytes(new)
    else:
        del terms[index]
    _memory(base_size + memory[0], m)


def _expand(j, pf, pg, H, K, sf, conditioned, m, base_size):
    raw, memory = {}, [0]
    for a, direction in ((j, 1), (j + 1, -1)):
        for u in range(1, H // a + 1):
            m.charge(4)
            if not sf[u]:
                continue
            d = a*u - 1
            _add(raw, u, direction*pf[d], m, base_size, memory)
            for ell in range(1, K + 1):
                m.charge(8)
                if not sf[ell]:
                    continue
                overlap = gcd(u, ell)
                key = (u // overlap) * (ell // overlap)
                _add(raw, key, -direction*pg[d][ell-1], m, base_size, memory)
    reduced, reduced_memory = {}, [0]
    for key, value in raw.items():
        index, sign = _condition(key, conditioned, m)
        _add(reduced, index, sign*value, m, base_size + memory[0], reduced_memory)
    return reduced, base_size + memory[0] + reduced_memory[0]


def verify_contraction(lift, cert, meter=None):
    m = Meter() if meter is None else meter
    MASS._fields(lift, LIFT_FIELDS)
    MASS._expect(lift['schema'], 'mobius-factored-quadratic-repair-v1')
    MASS._fields(cert, ('schema', 'N', 'y', 'H', 'K', 'conditioned_primes', 'endpoints', 'budget'))
    MASS._expect(cert['schema'], 'mobius-quadratic-contraction-v1')
    N, y, H, K = (lift[k] for k in ('N', 'y', 'H', 'K'))
    if type(N) is not int or not 2 <= N < 2**64 or type(y) is not int or not 1 <= y < 2**64:
        raise ValueError('bounded positive finite source scale and prefix')
    if type(H) is not int or not 1 <= H <= MAX_H or type(K) is not int or K < 0:
        raise ValueError('bounded short and inverse horizons')
    B = max(H, K)
    if B > MAX_B or H*K > MAX_KERNEL_CELLS:
        raise OverflowError('quadratic contraction horizon/cell capacity')
    if K != y // (H + 1):
        raise ValueError('lift inverse horizon')
    for key in ('N', 'y', 'H', 'K'):
        MASS._expect(cert[key], lift[key])
    _, _, _, _, p, q, _ = MASS._parameters(lift['parameters'], m)
    if y > 4*N // p:
        raise ValueError('source prefix exceeds full horizon')
    for key in ('linear_terms', 'long_kernels_after_fill'):
        if type(lift[key]) is not list or len(lift[key]) != 2:
            raise ValueError('both complete source endpoints')
    ps = cert['conditioned_primes']
    if type(ps) is not list or len(ps) > B:
        raise ValueError('bounded conditioned prime list')
    for prime in ps:
        if type(prime) is not int or not 2 <= prime <= B:
            raise ValueError('conditioned actual prime within arithmetic radius')
        MASS._prime(prime, m)
    if ps != sorted(set(ps)):
        raise ValueError('conditioned primes ascending and distinct')
    endpoints = cert['endpoints']
    if type(endpoints) is not list or len(endpoints) != 2:
        raise ValueError('both complete contraction endpoints')
    sf, costs, peak = _sieve(B, m), [], 0
    conditioned = set(ps)
    max_index = max(H, H*K)
    for e, ratio in enumerate((Q(p, q), Q(1))):
        endpoint = endpoints[e]
        MASS._fields(endpoint, ('ratio', 'rows', 'l1'))
        if MASS._rational(endpoint['ratio'], m) != ratio:
            raise ValueError('exact source endpoint ratio')
        rows = endpoint['rows']
        if type(rows) is not list or len(rows) != H:
            raise ValueError('every contraction j row at both endpoints')
        pf, pg, size = _endpoint_arrays(lift, e, H, K, m)
        cost = Q(0)
        for j, row in enumerate(rows, 1):
            MASS._fields(row, ('j', 'terms'))
            if type(row['j']) is not int or row['j'] != j:
                raise ValueError('complete ascending contraction j rows')
            terms = row['terms']
            if type(terms) is not list or len(terms) > max_index:
                raise ValueError('bounded complete monomial rows')
            expected, live_size = _expand(j, pf, pg, H, K, sf, conditioned, m, size)
            peak = max(peak, live_size)
            if len(terms) != len(expected):
                raise ValueError('every nonzero contracted term required')
            last = 0
            for term in terms:
                MASS._fields(term, ('index', 'coefficient'))
                index = term['index']
                if type(index) is not int or not last < index <= max_index or not _squarefree(index, m):
                    raise ValueError('ascending unique positive squarefree monomial indices')
                coefficient = MASS._rational(term['coefficient'], m)
                if not coefficient or coefficient != expected.get(index):
                    raise ValueError('exact coalesced conditioned coefficient')
                cost = MASS._bounded(cost + abs(coefficient), m)
                last = index
            del expected
        if MASS._rational(endpoint['l1'], m) != cost:
            raise ValueError('exact complete endpoint contraction L1 price')
        costs.append(cost)
        del pf, pg
    budget = max(costs)
    if MASS._rational(cert['budget'], m) != budget:
        raise ValueError('exact maximum endpoint budget')
    # The all-conditioned case is finite evaluation, not an exponent theorem.
    all_conditioned = all(n in conditioned for n in range(2, B + 1)
        if sf[n] and _is_prime(n, m))
    m.charge(100)
    return {'verified': True, 'schema': 'verified-mobius-quadratic-contraction-v1',
        'N': N, 'y': y, 'H': H, 'K': K, 'arithmetic_radius': B,
        'conditioned_primes': ps, 'endpoint_ratios': [str(Q(p, q)), '1'],
        'endpoint_l1': list(map(str, costs)), 'budget': str(budget),
        'rows_checked_per_endpoint': H, 'squareful_inputs_zero': True,
        'shared_prime_overlap_preserved': True, 'linear_minus_quadratic_coalesced': True,
        'endpoint_convexity_proved': True, 'finite_variation_bound_proved': True,
        'bound_domain': 'fixed supplied N,y,H, every real r in [p/q,1], every +/-1 assignment to unconditioned prime signs',
        'source_binding_condition': 'check_mobius_quadratic_source_064.verify_quadratic(lift,repair) must independently accept',
        'original_source_binding_proved': False, 'independent_source_admission_required': True,
        'all_radius_primes_conditioned': all_conditioned,
        'all_conditioned_is_finite_arithmetic_only': True,
        'prospective_peak_storage_bytes': peak,
        'uniform_N_growth_proved': False, 'whole_signed_target_bound_proved': False,
        'RH_proved': False, 'recorded_ordinary_mu_used': False,
        'scientific_source_or_LP_evaluated': False}


def _is_prime(n, m):
    for d in range(2, isqrt(n) + 1):
        m.charge(4)
        if n % d == 0:
            return False
    m.charge()
    return True
