"""Independent scalar audit of finite convolution scale certificates.

No producer, historical checker, optimizer, or scientific array is imported.
Pointwise floor channels and ordered-factor counts replay the signed polynomial
by products of ordinary-prefix differences, not by producer tensor differences.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb, isqrt, prod
import sys
import time

SCHEMA = 'mobius-convolution-scale-v1'
GRID = 1 << 20
MAX_N = 65536
MAX_J = 4096
MAX_WORK = 300_000_000_000
MAX_BITS = 4096
MAX_POWER_BITS = 100000
MAX_ENTRIES = 4_000_000
MAX_MEMORY_BYTES = 512 * 1024 * 1024


class Meter:
    def __init__(self, cap=MAX_WORK, seconds=7200):
        if type(cap) is not int or not 0 <= cap <= MAX_WORK:
            raise ValueError('bounded nonnegative work cap')
        if type(seconds) not in (int, float) or not 0 < seconds <= 7200:
            raise ValueError('bounded positive deadline')
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, n=1):
        if type(n) is not int or not 0 <= n <= self.cap-self.operations:
            raise OverflowError('convolution checker work cap')
        self.operations += n
        if time.monotonic() > self.deadline:
            raise TimeoutError('convolution checker deadline')


class _Context:
    def __init__(self, meter):
        self.m, self.work, self.storage = meter, 0, 8192
        self.input_storage, self.input_entries = 0, 0
        self.scratch_base = 0

    def preflight(self, obj, depth=0):
        """Bound the admitted in-memory JSON tree before allocating replay."""
        self.charge()
        self.input_entries += 1
        self.input_storage += sys.getsizeof(obj)
        if self.input_entries > MAX_ENTRIES or depth > 24:
            raise OverflowError('convolution checker input entry capacity')
        if self.input_storage+8192 > MAX_MEMORY_BYTES:
            raise MemoryError('convolution checker input storage capacity')
        if type(obj) is dict:
            for key, value in obj.items():
                if type(key) is not str:
                    raise ValueError('JSON string fields required')
                self.preflight(key, depth+1)
                self.preflight(value, depth+1)
        elif type(obj) is list:
            for value in obj:
                self.preflight(value, depth+1)
        elif type(obj) is str:
            if len(obj) > 10000:
                raise ValueError('bounded certificate text')
            self.charge(len(obj))
        elif type(obj) is int:
            if abs(obj).bit_length() > MAX_BITS:
                raise OverflowError('certificate integer bit capacity')
        elif type(obj) is not bool:
            raise ValueError('finite JSON certificate types required')

    def charge(self, n=1):
        if type(n) is not int or not 0 <= n <= MAX_WORK-self.work:
            raise OverflowError('independent convolution work capacity')
        self.work += n
        self.m.charge(n)

    def prospective(self, count, size=192, extra_bytes=0):
        if type(count) is not int or not 0 <= count <= MAX_ENTRIES-self.input_entries:
            raise OverflowError('convolution checker entry capacity')
        storage = 8192+self.input_storage+self.scratch_base+count*size+extra_bytes
        if storage > MAX_MEMORY_BYTES:
            raise MemoryError('convolution checker prospective storage capacity')
        self.storage = max(self.storage, storage)
        self.charge()

    def bounded(self, value):
        value = Q(value)
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        self.charge(bits+1)
        if bits > MAX_BITS:
            raise OverflowError('convolution checker rational capacity')
        return value

    def q(self, value):
        if type(value) is not str or not 1 <= len(value) <= 2500:
            raise ValueError('bounded rational text')
        self.charge(len(value)+1)
        try:
            result = Q(value)
        except (ValueError, ZeroDivisionError):
            raise ValueError('rational text') from None
        if str(result) != value:
            raise ValueError('canonical rational required')
        return self.bounded(result)


def _fields(obj, names):
    if type(obj) is not dict or set(obj) != set(names):
        raise ValueError('exact convolution scale schema')


def _integer(value, lo, hi, description):
    if type(value) is not int or not lo <= value <= hi:
        raise ValueError(description)
    return value


def _parameters(obj, c):
    if type(obj) is not dict or set(obj) not in (
            {'primes', 'p', 'q', 'alpha', 'gamma'},
            {'primes', 'p', 'q', 'alpha', 'gamma', 'tau'}):
        raise ValueError('source parameter schema')
    if not 0 < c.q(obj['alpha']) < 1 or c.q(obj['gamma']) <= 0:
        raise ValueError('source fractional gates')
    if 'tau' in obj and not 0 < c.q(obj['tau']) < 1:
        raise ValueError('source tau gate')
    primes = obj['primes']
    if type(primes) is not list or not 2 <= len(primes) <= 8:
        raise ValueError('bounded prime registration')
    for prime in primes:
        _integer(prime, 2, 1000000, 'bounded source prime')
        for divisor in range(2, isqrt(prime)+1):
            c.charge(4)
            if prime % divisor == 0:
                raise ValueError('actual prime required')
    if primes != sorted(set(primes)):
        raise ValueError('canonical prime registration')
    p, q = obj['p'], obj['q']
    if type(p) is not int or type(q) is not int or p not in primes or q not in primes or p >= q:
        raise ValueError('ordered registered source primes')
    return p, q


def _power_floor(R, theta, c):
    theta = c.q(theta)
    if not 0 <= theta < 1:
        raise ValueError('strictly smaller-scale exponent')
    bits = R.bit_length()*max(theta.numerator, theta.denominator)
    if bits > MAX_POWER_BITS:
        raise OverflowError('exact power intermediate bit capacity')
    c.charge(3*(1+bits*max(1, bits.bit_length())))
    target, lo, hi = R**theta.numerator, 1, R+1
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**theta.denominator <= target:
            lo = mid
        else:
            hi = mid
    return lo


def _source(N, y, D, p, q, ratio, c):
    """Direct pointwise joined channels, with integer denominator cleared."""
    den, num = ratio.denominator, ratio.numerator
    c.prospective(4*(D+2), 40)
    full, tail, head = [0]*(D+2), [0]*(D+2), [0]*(D+2)
    for d in range(1, D+1):
        c.charge(24)
        wp = 4*N//(p*d)-3*(2*N//(p*d))+2*(N//(p*d))
        wq = 4*N//(q*d)-3*(2*N//(q*d))+2*(N//(q*d))
        if abs(wp) > 1 or abs(wq) > 1:
            raise ArithmeticError('floor-channel amplitude')
        full[d] = den*wp-num*wq
        if d <= y:
            head[d] = full[d]
        else:
            tail[d] = -full[d]
    direct = {}
    for base, scale in ((p, den), (q, -num)):
        for v, a in ((4, 1), (2, -3), (1, 2)):
            j = v*N//base
            if j:
                direct[j] = direct.get(j, 0)+scale*a
    return head, tail, full, direct


def _factor_count(n, slots, c):
    """Number of ordered positive factors in 'slots', by prime exponents."""
    if slots == 0:
        return int(n == 1)
    if slots == 1:
        return 1
    result, divisor = 1, 2
    while divisor*divisor <= n:
        c.charge(4)
        exponent = 0
        while n % divisor == 0:
            n //= divisor
            exponent += 1
            c.charge(4)
        if exponent:
            result *= comb(exponent+slots-1, slots-1)
        divisor += 1
    if n > 1:
        result *= slots
    return result


def _scalar_kernels(kappa, degree, c):
    """Integer ordered-divisor counts, independent of tensor recurrence."""
    R = len(kappa)-1
    c.prospective((2*degree+5)*(R+1), 40)
    multiplicities = [[_factor_count(t, m-1, c) for t in range(1, R+1)]
                      for m in range(1, degree+1)]
    kernels = [[0]*(R+1) for _ in range(degree+1)]
    for m in range(1, degree+1):
        for v in range(1, R+1):
            value = 0
            for t in range(1, R//v+1):
                c.charge(4)
                value += kappa[v*t]*multiplicities[m-1][t-1]
            kernels[m][v] = value
    return kernels


def _prefix_polynomial(kappa, cutoffs, coefficients, c, kernels=None):
    """Expand each scalar convolution tuple using mu(a)=M(a)-M(a-1)."""
    degree, R = len(cutoffs), len(kappa)-1
    kernels = _scalar_kernels(kappa, degree, c) if kernels is None else kernels
    kernel_degree = len(kernels)-1
    polynomial = {}

    def add_tuple(indices, value):
        if not value:
            return
        for choices in product((0, 1), repeat=len(indices)):
            c.charge(8*len(indices)+4)
            prefix_indices = [a-choice for a, choice in zip(indices, choices)]
            if 0 in prefix_indices:
                continue
            key = tuple(sorted(a for a in prefix_indices if a != 1))
            if key not in polynomial:
                c.prospective(2*(len(polynomial)+1), 192,
                              (2*kernel_degree+5)*(R+1)*40)
            polynomial[key] = polynomial.get(key, 0)+value*(-1)**sum(choices)
            if abs(polynomial[key]).bit_length() > MAX_BITS:
                raise OverflowError('signed polynomial coefficient bit capacity')

    for mask in range(1, 1 << degree):
        axes = [cutoffs[i] for i in range(degree) if mask & (1 << i)]
        m = len(axes)

        def tuples(at, running, indices):
            if at == m:
                add_tuple(indices, -coefficients[mask]*kernels[m][running])
                return
            for a in range(1, min(axes[at], R//running)+1):
                c.charge(4)
                tuples(at+1, running*a, indices+(a,))

        tuples(0, 1, ())
    return {key: value for key, value in polynomial.items() if value}


def _ceil_weight(index_product, sigma, c):
    """Exact ceil(G*index_product**sigma)/G, including irrational powers."""
    bits = (index_product.bit_length()+GRID.bit_length())*max(sigma.numerator, sigma.denominator)
    if bits > MAX_POWER_BITS:
        raise OverflowError('rounded price power capacity')
    c.charge(3*(1+bits*max(1, bits.bit_length())))
    target = GRID**sigma.denominator*index_product**sigma.numerator
    lo, hi = 0, GRID*index_product
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**sigma.denominator >= target:
            hi = mid
        else:
            lo = mid
    return Q(hi, GRID)


def _degree_prices(polynomial, den, sigma, degree, c):
    prices = [Q(0) for _ in range(degree+1)]
    prices[0] = Q(abs(polynomial.get((), 0)), den)
    weights = {}
    for indices, coefficient in polynomial.items():
        if not indices:
            continue
        index_product = prod(indices)
        if index_product not in weights:
            weights[index_product] = _ceil_weight(index_product, sigma, c)
        prices[len(indices)] += Q(abs(coefficient), den)*weights[index_product]
        c.bounded(prices[len(indices)])
    return prices


def _ordinary_mu(D, c):
    """Evaluator-only elementary sieve; never used to construct the price."""
    c.prospective(3*(D+1), 40)
    mu, composite = [1]*(D+1), bytearray(D+1)
    mu[0] = 0
    for p in range(2, D+1):
        c.charge()
        if composite[p]:
            continue
        for n in range(p, D+1, p):
            c.charge(3)
            mu[n] = -mu[n]
            if n != p:
                composite[n] = 1
        for n in range(p*p, D+1, p*p):
            c.charge(2)
            mu[n] = 0
    return mu


def _annihilators(supplied, degrees, c):
    if type(supplied) is not list or len(supplied) != len(degrees):
        raise ValueError('complete requested annihilator degrees')
    answer = {}
    for obj, degree in zip(supplied, degrees):
        _fields(obj, ('degree', 'coefficients', 'system_rank'))
        _integer(obj['degree'], degree, degree, 'sorted annihilator degrees')
        size = 1 << degree
        _integer(obj['system_rank'], size, size, 'full face system rank')
        coeff = obj['coefficients']
        if type(coeff) is not list or len(coeff) != size or any(type(v) is not int for v in coeff):
            raise ValueError('complete integer face coefficients')
        # h_empty and one parent equation per nonempty mask form a triangular
        # full-rank subsystem. Audit every additional face as well.
        if coeff[0] != 1:
            raise ValueError('unit-normalized annihilator')
        for mask in range(size):
            for i in range(degree):
                c.charge(4)
                if not mask & (1 << i) and coeff[mask]+coeff[mask | (1 << i)] != 0:
                    raise ValueError('every multilinear face vanishes')
        answer[degree] = coeff
    return answer


def _equal_q(supplied, expected, c, description):
    if c.q(supplied) != c.bounded(expected):
        raise ValueError(description)


def verify_control(cert, meter=None):
    """Strictly replay all finite models, then audit actual ordinary mu."""
    c = _Context(Meter() if meter is None else meter)
    c.preflight(cert)
    _fields(cert, ('schema', 'N', 'y', 'max_j', 'parameters', 'requests',
                   'price_exponents', 'coefficient_grid', 'annihilators', 'endpoints',
                   'universal_convolution_identity_proved',
                   'smaller_mu_query_radius_verified', 'conditional_prefix_bounds_paid',
                   'uniform_head_bound_proved', 'RH_proved'))
    if cert['schema'] != SCHEMA:
        raise ValueError('convolution scale schema')
    for flag in ('universal_convolution_identity_proved', 'smaller_mu_query_radius_verified'):
        if cert[flag] is not True:
            raise ValueError('exact identity and smaller-scale scope '+flag)
    for flag in ('conditional_prefix_bounds_paid', 'uniform_head_bound_proved', 'RH_proved'):
        if cert[flag] is not False:
            raise ValueError('unpaid uniform premise scope '+flag)
    p, q = _parameters(cert['parameters'], c)
    N = _integer(cert['N'], 2, MAX_N, 'bounded source scale')
    D = 4*N//p
    c.scratch_base = 6*(D+2)*40
    y = _integer(cert['y'], 1, D, 'bounded original prefix')
    max_j = _integer(cert['max_j'], 0, min(D, MAX_J), 'complete bounded row domain')
    _integer(cert['coefficient_grid'], GRID, GRID, 'fixed upward price grid')
    requests = cert['requests']
    if type(requests) is not list or not 1 <= len(requests) <= 64:
        raise ValueError('bounded nonempty cutoff requests')
    seen, degrees = set(), set()
    for request in requests:
        if type(request) is not list or not 2 <= len(request) <= 8:
            raise ValueError('bounded convolution degree')
        exponents = [c.q(text) for text in request]
        if exponents != sorted(exponents) or any(not 0 <= v < 1 for v in exponents) or sum(exponents) < 1:
            raise ValueError('ordered smaller-scale exponents with sufficient sum')
        key = tuple(request)
        if key in seen:
            raise ValueError('distinct cutoff requests')
        seen.add(key)
        degrees.add(len(request))
    annihilators = _annihilators(cert['annihilators'], sorted(degrees), c)
    price_texts = cert['price_exponents']
    if type(price_texts) is not list or not 1 <= len(price_texts) <= 32:
        raise ValueError('bounded nonempty scalar price exponents')
    sigmas = [c.q(text) for text in price_texts]
    if len(set(sigmas)) != len(sigmas) or any(not 0 <= s <= 1 for s in sigmas):
        raise ValueError('distinct scalar price exponents in unit interval')
    endpoints = cert['endpoints']
    if type(endpoints) is not list or len(endpoints) != 2:
        raise ValueError('both ordered ratio endpoints required')
    # Ordinary arithmetic enters only the final evaluation of a model that
    # was fully specified by source geometry, cutoffs and face constraints.
    mu = _ordinary_mu(D, c)
    prefix, running = [0]*(D+1), 0
    for n in range(1, D+1):
        c.charge(2)
        running += mu[n]
        prefix[n] = running
    checked_endpoints = []
    for endpoint, ratio in zip(endpoints, (Q(p, q), Q(1))):
        _fields(endpoint, ('ratio', 'denominator', 'rows'))
        _equal_q(endpoint['ratio'], ratio, c, 'ordered exact ratio endpoint')
        den = ratio.denominator
        _integer(endpoint['denominator'], den, den, 'reduced endpoint denominator')
        rows = endpoint['rows']
        if type(rows) is not list or len(rows) != max_j:
            raise ValueError('complete source row domain')
        head, tail, full, direct_atoms = _source(N, y, D, p, q, ratio, c)
        checked_rows, actual_head, conditional_heads = [], Q(0), [Q(0)]*len(sigmas)
        for j, row in enumerate(rows, 1):
            _fields(row, ('j', 'R', 'direct_scaled', 'unit_kernel_scaled',
                          'models', 'plans', 'selected_model'))
            _integer(row['j'], j, j, 'complete canonical row order')
            R = D//j
            _integer(row['R'], R, R, 'exact source support radius')
            kappa = [0]+[tail[j*n]-(tail[(j+1)*n] if (j+1)*n <= D else 0)
                         for n in range(1, R+1)]
            c.charge(16*R)
            direct = direct_atoms.get(j, 0)
            _integer(row['direct_scaled'], direct, direct, 'exact full-source direct atom')
            _integer(row['unit_kernel_scaled'], kappa[1], kappa[1], 'actual retained unit kernel')
            plans = row['plans']
            if type(plans) is not list or len(plans) != len(requests):
                raise ValueError('complete cutoff request plans')
            cutoffs_list, cache = [], {}
            for plan, request in zip(plans, requests):
                _fields(plan, ('exponents', 'cutoffs', 'model_index'))
                if type(plan['exponents']) is not list or plan['exponents'] != request:
                    raise ValueError('exact exponent request order')
                cutoffs = [_power_floor(R, text, c) for text in request]
                supplied = plan['cutoffs']
                if type(supplied) is not list or any(type(v) is not int for v in supplied) or supplied != cutoffs:
                    raise ValueError('exact rational cutoff powers')
                key = tuple(cutoffs)
                if key not in cache:
                    cache[key] = len(cutoffs_list)
                    cutoffs_list.append(cutoffs)
                _integer(plan['model_index'], cache[key], cache[key], 'reuse exact cutoff rectangle')
            models = row['models']
            if type(models) is not list or len(models) != len(cutoffs_list):
                raise ValueError('one complete model per realized cutoff rectangle')
            kernels = _scalar_kernels(kappa, max(map(len, cutoffs_list)), c)
            replayed = []
            for model, cutoffs in zip(models, cutoffs_list):
                _fields(model, ('degree', 'cutoffs', 'support_min', 'mu_query_radius',
                                'constant_scaled', 'terms', 'conditional_prices', 'scalar_box_witness'))
                degree = len(cutoffs)
                _integer(model['degree'], degree, degree, 'exact convolution degree')
                if type(model['cutoffs']) is not list or any(type(v) is not int for v in model['cutoffs']) or model['cutoffs'] != cutoffs:
                    raise ValueError('complete cutoff rectangle')
                support_min, radius = prod(v+1 for v in cutoffs), max(cutoffs)
                _integer(model['support_min'], support_min, support_min, 'exact omitted-product support gate')
                _integer(model['mu_query_radius'], radius, radius, 'exact ordinary mu query radius')
                if support_min <= R or (R > 1 and radius >= R) or (R == 1 and radius != 1):
                    raise ValueError('all convolution mu inputs strictly smaller, except unit row')
                polynomial = _prefix_polynomial(kappa, cutoffs, annihilators[degree], c, kernels)
                polynomial[()] = polynomial.get((), 0)+direct
                if not polynomial[()]:
                    polynomial.pop(())
                constant = polynomial.get((), 0)
                _integer(model['constant_scaled'], constant, constant, 'complete signed constant')
                terms = model['terms']
                expected = sorted((indices, value) for indices, value in polynomial.items() if indices)
                if type(terms) is not list or len(terms) != len(expected):
                    raise ValueError('all coalesced signed monomials required')
                c.prospective(3*len(terms)+4*(D+2), 192)
                for supplied, (indices, value) in zip(terms, expected):
                    _fields(supplied, ('indices', 'coefficient_scaled'))
                    index_list = supplied['indices']
                    if type(index_list) is not list or any(type(v) is not int for v in index_list) or index_list != list(indices):
                        raise ValueError('sorted canonical monomial indices without M(1)')
                    if any(not 2 <= v <= radius for v in index_list) or len(index_list) > degree:
                        raise ValueError('ordinary-prefix degree and smaller support')
                    _integer(supplied['coefficient_scaled'], value, value, 'complete signed coalesced coefficient')
                supplied_prices = model['conditional_prices']
                if type(supplied_prices) is not list or len(supplied_prices) != len(sigmas):
                    raise ValueError('every scalar conditional price required')
                prices, premise_at_one = [], []
                for supplied, sigma, text in zip(supplied_prices, sigmas, price_texts):
                    _fields(supplied, ('sigma', 'coefficients'))
                    if supplied['sigma'] != text or type(supplied['sigma']) is not str:
                        raise ValueError('canonical conditional price order')
                    values = _degree_prices(polynomial, den, sigma, degree, c)
                    if type(supplied['coefficients']) is not list or len(supplied['coefficients']) != degree+1:
                        raise ValueError('all degrees including paid constant')
                    for actual, value in zip(supplied['coefficients'], values):
                        _equal_q(actual, value, c, 'exact upward-rounded complete degree price')
                    prices.append(values)
                    # The finite C=1 premise is merely audited, never asserted
                    # uniformly. Raise each side to sigma.denominator exactly.
                    bits = (D.bit_length()+1)*max(sigma.numerator, sigma.denominator)
                    if bits > MAX_POWER_BITS:
                        raise OverflowError('finite premise power capacity')
                    okay = True
                    for t in range(2, radius+1):
                        c.charge(3*(1+bits*max(1, bits.bit_length())))
                        if abs(prefix[t])**sigma.denominator > t**sigma.numerator:
                            okay = False
                    premise_at_one.append(okay)
                witness = model['scalar_box_witness']
                _fields(witness, ('prefix_values', 'value', 'actual_mobius_assignment'))
                if witness['prefix_values'] != 'M(1)=1,M(s)=0 for s>=2' or witness['actual_mobius_assignment'] is not False:
                    raise ValueError('formal scalar witness cannot be claimed actual arithmetic')
                _equal_q(witness['value'], Q(constant, den), c, 'exact formal scalar-box value')
                evaluated = sum(value*prod(prefix[t] for t in indices)
                                for indices, value in polynomial.items())
                c.charge(sum(4+4*len(indices) for indices in polynomial))
                actual = direct+sum(mu[n]*kappa[n] for n in range(1, R+1))
                raw = sum(mu[n]*(head[j*n]-(head[(j+1)*n] if (j+1)*n <= D else 0))
                          for n in range(1, R+1))
                c.charge(24*R)
                if evaluated != actual or actual != raw:
                    raise ArithmeticError('ordinary-Mobius original-source polynomial identity')
                for values, paid in zip(prices, premise_at_one):
                    if paid and abs(Q(actual, den)) > sum(values):
                        raise ArithmeticError('finite conditional price violated')
                replayed.append(dict(prices=prices, premise_at_one=premise_at_one,
                    radius=radius, term_count=len(terms), constant=constant, actual=Q(actual, den)))
            selected = min(range(len(models)), key=lambda i: (
                sum(replayed[i]['prices'][0]), replayed[i]['radius'], replayed[i]['term_count'], i))
            _integer(row['selected_model'], selected, selected, 'exact deterministic conditional-price selection')
            actual = replayed[selected]['actual']
            actual_head += abs(actual)
            for s in range(len(sigmas)):
                conditional_heads[s] += sum(replayed[selected]['prices'][s])
            checked_rows.append(dict(j=j, R=R, actual_coefficient=str(actual), selected_model=selected,
                models=[dict(mu_query_radius=m['radius'], constant=str(Q(m['constant'], den)),
                             term_count=m['term_count'], finite_C1_prefix_premise=m['premise_at_one'],
                             conditional_C1_prices=[str(sum(values)) for values in m['prices']])
                        for m in replayed]))
        checked_endpoints.append(dict(ratio=str(ratio), denominator=den, rows=checked_rows,
            actual_head_variation=str(actual_head),
            conditional_C1_head_prices=[str(v) for v in conditional_heads]))
    return dict(verified=True, schema='verified-'+SCHEMA, N=N, y=y, max_j=max_j, D=D,
        parameters=cert['parameters'], endpoints=checked_endpoints,
        independent_scalar_convolution_replay=True,
        full_face_system_verified=True, universal_convolution_identity_proved=True,
        complete_signed_prefix_polynomial_verified=True, exact_upward_price_rounding_verified=True,
        ordinary_mu_unit_retained=True, smaller_mu_query_radius_verified=True,
        checker_actual_mobius_signs_evaluated=True, learner_mobius_signs_accessed=False,
        original_source_inverse_identity_proved=True, original_source_binding_proved=False,
        independent_parent_source_admission_required=True,
        scalar_box_witness_is_actual_mobius=False, conditional_prefix_bounds_paid=False,
        uniform_head_bound_proved=False, uniform_N_growth_proved=False,
        whole_signed_target_bound_proved=False, RH_proved=False, raw_head_only=True,
        arithmetic_query_horizon=D, charged_work_units=c.work,
        prospective_peak_storage_bytes=c.storage)


verify_convolution_scale = verify_control
