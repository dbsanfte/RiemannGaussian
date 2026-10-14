"""Bound-program and exact relation search for an unresolved integral core.

No scientific values or anticipated winning cutoffs enter this search.
The grammar supplies reviewed proof rules; independent checking is separate.
"""
from fractions import Fraction as Q
from functools import reduce
from itertools import combinations, product
from math import gcd, isqrt, lcm, prod
import time

INTEGRAND = 'R^-t*sum_(d<=4N,gcd(d,R)=1)mu(d)*d^-t*sum_(e|R)mu(e)*W(N/(d*e))'
COMMON = 'Psi_P(N)=Psi(4N)-3*Psi(2N)+2*Psi(N)'
EXCEPTION = 'b_p(N)=log(p)*(floor(log_p(4N))-3*floor(log_p(2N))+2*floor(log_p(N)))'
JET_IDENTITY = "sum_i a_i*h_(S_i)'(0)=common_coefficient*Psi_P(N)+sum_p exception_coefficient(p)*b_p(N)"


class Meter:
    def __init__(self, cap=100_000_000, seconds=600):
        self.cap, self.operations = cap, 0
        self.deadline = time.monotonic()+seconds

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or self.operations+amount > self.cap:
            raise OverflowError('proof search operation cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('proof search time cap')


def rational(s, lower=None, upper=None):
    if type(s) is not str or not 1 <= len(s) <= 512:
        raise ValueError('canonical bounded rational string')
    x = Q(s)
    if str(x) != s or (lower is not None and x < lower) or (upper is not None and x > upper):
        raise ValueError('rational outside declared domain')
    if max(abs(x.numerator).bit_length(), x.denominator.bit_length()) > 1024:
        raise OverflowError('rational bit cap')
    return x


def primes(values):
    if (type(values) is not list or len(values) > 12
            or any(type(p) is not int or not 2 <= p <= 10000 for p in values)
            or values != sorted(set(values))):
        raise ValueError('canonical finite prime set')
    if any(any(p % d == 0 for d in range(2, isqrt(p)+1)) for p in values):
        raise ValueError('ordinary prime generators')
    return values


def validate_features(features):
    if type(features) is not list or not 1 <= len(features) <= 32:
        raise ValueError('bounded feature family')
    for feature in features: primes(feature)
    if len(set(tuple(f) for f in features)) != len(features):
        raise ValueError('distinct insertion words')
    return sorted(set(p for feature in features for p in feature))


def cutoff_grammar(max_denominator=12, maximum='2', meter=None):
    """All reduced positive rationals within a resource bound, no root whitelist."""
    meter = meter or Meter()
    maximum = rational(maximum, Q(0), Q(64))
    if maximum <= 0 or type(max_denominator) is not int or not 1 <= max_denominator <= 128:
        raise ValueError('finite positive cutoff grammar')
    values = set()
    for denominator in range(1, max_denominator+1):
        for numerator in range(1, int(maximum*denominator)+1):
            values.add(Q(numerator, denominator)); meter.charge()
    return [str(x) for x in sorted(values)]


def tail_certificate(request, meter=None):
    meter = meter or Meter()
    if type(request) is not dict or set(request) != {'alpha', 'primes', 'tau'}:
        raise ValueError('exact tail request')
    alpha = rational(request['alpha'], Q(0), Q(1))
    tau = rational(request['tau'], Q(0), Q(64))
    if not 0 < alpha < 1 or tau <= 0:
        raise ValueError('alpha inside(0,1), positive cutoff')
    generators = primes(request['primes']); multiplicity = 2**len(generators)
    if tau < 1:
        power, constant, log = 1-tau, 16*multiplicity/tau**2/(1-tau), Q(0)
    elif tau == 1:
        power, constant, log = Q(0), Q(12*multiplicity), Q(4*multiplicity)
    else:
        power, constant, log = Q(0), 4*multiplicity*tau/(tau-1), Q(0)
    meter.charge(64+8*len(generators))
    return {'schema': 'prime-insertion-finite-cutoff-tail-v1', 'request': request,
        'product': prod(generators), 'integer_N_minimum': 2,
        'filter': {'q': 2, 'coefficients': [2, -3, 1], 'normalization': 'divide_by_alpha'},
        'integrand': INTEGRAND, 'normalizer': '1/(alpha*I_alpha)',
        'upper_bound': {'N_power': str(power), 'constant': str(constant),
            'log_coefficient': str(log), 'logarithm_base': 'e'},
        'unpaid_core': '0<t<tau', 'tail_bound_proved': True,
        'complete_target_bound_proved': False, 'RH_proved': False}


def recovery_certificate(request, meter=None):
    meter = meter or Meter()
    if type(request) is not dict or set(request) != {'tail_request', 'low_core'}:
        raise ValueError('exact conditional recovery request')
    low = request['low_core']
    if type(low) is not dict or set(low) != {'constant', 'log_power', 'status'} or low['status'] != 'OPEN':
        raise ValueError('explicit unpaid low-core hypothesis')
    constant = rational(low['constant'], Q(0)); eta = rational(low['log_power'], Q(0))
    tail = tail_certificate(request['tail_request'], meter)
    compatible = Q(request['tail_request']['tau']) >= Q(1, 2)
    bound = tail['upper_bound']
    tail_constant = Q(bound['constant'])+2*Q(bound['log_coefficient']) if compatible else None
    return {'schema': 'prime-insertion-low-core-recovery-v1', 'request': request,
        'tail_square_root_compatible': compatible,
        'tail_square_root_constant': None if tail_constant is None else str(tail_constant),
        'full_constant': None if tail_constant is None else str(constant+tail_constant),
        'log_power': str(eta), 'minimum': 2,
        'status': 'PAID_CONDITIONAL_IMPLICATION_WITH_OPEN_PREMISE' if compatible else 'TAIL_PROVIDER_INSUFFICIENT',
        'source_split': 't_S(N)=low_core_(0,tau)(N)+tail_(tau,infinity)(N)',
        'log_weight': '(1+log(N))^log_power',
        'conditional_original_target_implication': not request['tail_request']['primes'] and compatible,
        'low_core_bound_proved': False, 'complete_target_bound_proved': False, 'RH_proved': False}


def recovery_schema_certificate(request, meter=None):
    if type(request) is not dict or set(request) != {'tail_request', 'log_power'}:
        raise ValueError('exact universal conditional recovery request')
    eta = rational(request['log_power'], Q(0))
    example = recovery_certificate({'tail_request': request['tail_request'],
        'low_core': {'constant': '0', 'log_power': str(eta), 'status': 'OPEN'}}, meter)
    example['schema'] = 'prime-insertion-low-core-recovery-schema-v1'
    example['request'] = request
    offset = example['tail_square_root_constant']
    example['full_constant'] = None if offset is None else {'C_low_coefficient': '1', 'offset': offset}
    example['low_core_constant_quantifier'] = 'FOR EVERY finite C_low>=0'
    example['open_premise'] = '|low_core_(0,tau)(N)|<=C_low*sqrt(N)*(1+log(N))^log_power for EVERY integer N>=2'
    return example


def admits_growth(bound, target_power, target_log_power='0'):
    beta = rational(target_power, Q(0), Q(16))
    eta = rational(target_log_power, Q(0), Q(16))
    exponent = Q(bound['N_power'])
    log_degree = int(Q(bound['log_coefficient']) != 0)
    return exponent < beta or (exponent == beta and log_degree <= eta)


def search_cutoffs(alpha, features, cutoffs, target_power, target_log_power='0', meter=None):
    meter = meter or Meter(); validate_features(features)
    rows, selected = [], []
    for feature in features:
        local = []
        for tau in cutoffs:
            request = {'alpha': alpha, 'primes': feature, 'tau': tau}
            cert = tail_certificate(request, meter)
            row = {'request': request, 'certificate': cert,
                'growth_sufficient': admits_growth(cert['upper_bound'], target_power, target_log_power),
                'proof_program': ['ordinary_source_finite_divisor_expansion',
                    'integer_unit_cancellation' if not feature else 'retain_unit_with_R_at_least_two',
                    'absolute_cofactor_sum', 'normalizer_less_than_two',
                    'log_Rd_at_least_one_half', 'parameter_weight_envelope',
                    'exponential_tail_integral', 'finite_power_sum_envelope'],
                'independently_verified': False, 'low_core_bound_proved': False}
            rows.append(row); local.append(row)
        eligible = [r for r in local if r['growth_sufficient']]
        if eligible:
            # Minimize the unpaid parameter interval, not the numerical constant.
            selected.append(min(eligible, key=lambda r: Q(r['request']['tau'])))
    return {'rows': rows, 'selected': selected,
        'target_growth': {'N_power': target_power, 'log_power': target_log_power},
        'selection': 'smallest cutoff whose proved tail growth suffices',
        'source_values_read': False, 'RH_proved': False}


def microscopic_certificate(request, meter=None):
    meter = meter or Meter()
    if type(request) is not dict or set(request) != {'alpha', 'primes', 'gamma'}:
        raise ValueError('exact microscopic bound request')
    alpha = rational(request['alpha'], Q(0), Q(1))
    gamma = rational(request['gamma'], Q(0), Q(64))
    generators = primes(request['primes'])
    if not 0 < alpha < 1 or gamma <= 0 or not generators:
        raise ValueError('nonempty prime insertion, fractional alpha, positive cutoff exponent')
    count, R = len(generators), prod(generators)
    constant, power = 12*R/(count-alpha), 1-gamma*(count-alpha)
    meter.charge(64+8*count)
    return {'schema': 'prime-insertion-microscopic-bound-v1', 'request': request,
        'product': R, 'prime_count': count, 'integer_N_minimum': 2,
        'operator': 'E_R K(n)=K(R*n), n>=2',
        'filter': {'q': 2, 'coefficients': [2, -3, 1], 'normalization': 'divide_by_alpha'},
        'integrand': 'sum_(2<=n<=4N)w_P(n,N)*prod_(p|R*n)(1-p^-t)',
        'filter_absolute_mass': '4*N', 'cutoff': 'epsilon_N=min(1/2,N^-gamma)',
        'upper_bound': {'constant': str(constant), 'N_power': str(power)},
        'unpaid_middle': 'epsilon_N<t<1/2', 'near_zero_bound_proved': True,
        'complete_target_bound_proved': False, 'RH_proved': False}


def search_microscopic(alpha, words, gammas, target_power, meter=None):
    meter = meter or Meter(); rows, selected = [], []
    for word in words:
        local = []
        for gamma in gammas:
            request = {'alpha': alpha, 'primes': word['primes'], 'gamma': gamma}
            cert = microscopic_certificate(request, meter)
            shape = dict(cert['upper_bound'], log_coefficient='0')
            row = {'request': request, 'certificate': cert,
                'growth_sufficient': admits_growth(shape, target_power),
                'proof_program': ['complete_prime_inserted_source',
                    'positive_product_factor_envelope', 'complete_filter_absolute_mass',
                    'integrate_positive_power', 'parameterized_cutoff_substitution'],
                'independently_verified': False, 'middle_bound_proved': False}
            local.append(row); rows.append(row)
        eligible = [row for row in local if row['growth_sufficient']]
        if eligible: selected.append(min(eligible, key=lambda row: Q(row['request']['gamma'])))
    return {'rows': rows, 'selected': selected, 'target_N_power': target_power,
        'selection': 'smallest cutoff exponent whose proved near-zero growth suffices',
        'source_values_read': False, 'middle_bound_proved': False, 'RH_proved': False}


def first_jet_matrix(features, meter=None):
    """Collect coefficients of first-order formal prime factors.

    A singleton radical contributes its prime logarithm unless masked; all
    radicals of size>=2 have zero first jet. The outside class is universal,
    not one sampled prime standing in for all primes.
    """
    meter = meter or Meter(); generators = validate_features(features)
    classes = ['outside_generator_union']+generators
    matrix = []
    for prime_class in classes:
        row = [int(prime_class == classes[0] or prime_class not in feature) for feature in features]
        matrix.append(row); meter.charge(len(features))
    return {'classes': classes, 'matrix': matrix, 'higher_radical_first_jet': 'zero',
        'complete_source_not_replaced_by_prime_terms': True}


def primitive(vector):
    denominator = lcm(*(x.denominator for x in vector))
    integers = [int(x*denominator) for x in vector]
    common = reduce(gcd, (abs(x) for x in integers), 0)
    if not common: return tuple(integers)
    sign = 1 if next(x for x in integers if x) > 0 else -1
    return tuple(sign*x//common for x in integers)


def nullspace(matrix, ncols, meter=None):
    """Ordinary exact row reduction; no preferred relation is supplied."""
    meter = meter or Meter()
    if type(ncols) is not int or not 1 <= ncols <= 32 or len(matrix) > 400:
        raise ValueError('bounded rational matrix')
    if any(len(row) != ncols for row in matrix): raise ValueError('rectangular matrix')
    rows = [[Q(x) for x in row] for row in matrix]
    pivots, rank = [], 0
    for column in range(ncols):
        pivot = next((r for r in range(rank, len(rows)) if rows[r][column]), None)
        if pivot is None: continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        divisor = rows[rank][column]
        rows[rank] = [x/divisor for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][column]:
                coefficient = rows[r][column]
                rows[r] = [x-coefficient*y for x, y in zip(rows[r], rows[rank])]
                meter.charge(2*ncols)
        pivots.append(column); rank += 1; meter.charge(ncols)
    basis = []
    for free in (c for c in range(ncols) if c not in pivots):
        vector = [Q(0)]*ncols; vector[free] = Q(1)
        for r, column in enumerate(pivots): vector[column] = -rows[r][free]
        basis.append(primitive(vector)); meter.charge(ncols)
    return {'rank': rank, 'basis': [list(row) for row in basis]}


def jet_certificate(request, meter=None):
    meter = meter or Meter()
    if type(request) is not dict or set(request) != {'features', 'coefficients'}:
        raise ValueError('exact first-jet request')
    features = request['features']; generators = validate_features(features)
    if type(request['coefficients']) is not list or len(request['coefficients']) != len(features):
        raise ValueError('one coefficient per feature')
    coefficients = [rational(s) for s in request['coefficients']]
    if not any(coefficients): raise ValueError('nonzero mixture')
    common = sum(coefficients, Q(0))
    exceptions = [{'prime': p,
        'coefficient': str(-sum((a for a, s in zip(coefficients, features) if p in s), Q(0))),
        'rational_abs_bound': str(1 if p == 2 else 2*p)} for p in generators]
    exact = not common and all(Q(row['coefficient']) == 0 for row in exceptions)
    upper = None if common else str(sum((abs(Q(row['coefficient']))*Q(row['rational_abs_bound']) for row in exceptions), Q(0)))
    status = 'COMMON_PRIME_TERM_OPEN' if common else 'EXACT_FIRST_JET_ZERO' if exact else 'UNIFORM_FIRST_JET_BOUND'
    meter.charge(len(features)*(len(generators)+1))
    return {'schema': 'prime-insertion-first-jet-v1', 'request': request,
        'generator_primes': generators, 'integer_N_minimum': 2,
        'common_coefficient': str(common), 'exception_rows': exceptions,
        'common_prime_term': COMMON, 'prime_exception_term': EXCEPTION, 'identity': JET_IDENTITY,
        'status': status, 'uniform_absolute_upper': upper,
        'first_jet_identity_proved': True, 'first_jet_exact_zero_proved': bool(exact),
        'full_kernel_cancellation_proved': False, 'low_core_bound_proved': False, 'RH_proved': False}


def search_relations(features, promotion=True, meter=None):
    meter = meter or Meter(); source = first_jet_matrix(features, meter)
    ncols = len(features)
    coarse = nullspace(source['matrix'][:1], ncols, meter)
    complete = nullspace(source['matrix'], ncols, meter)
    vectors = {tuple(int(i == j) for i in range(ncols)): 'singleton_control' for j in range(ncols)}
    if promotion:
        for family, basis in [('outside_class_nullspace', coarse['basis']), ('all_classes_nullspace', complete['basis'])]:
            for vector in basis: vectors[tuple(vector)] = family
        # Compose inferred productions under fixed, answer-independent rules.
        for left, right in combinations(complete['basis'], 2):
            for sign in (-1, 1):
                vector = primitive([Q(a+sign*b) for a, b in zip(left, right)])
                if any(vector): vectors[vector] = 'sum_of_inferred_relations'
    rows = []
    for vector, origin in sorted(vectors.items()):
        request = {'features': features, 'coefficients': [str(x) for x in vector]}
        certificate = jet_certificate(request, meter)
        rows.append({'origin': origin, 'request': request, 'certificate': certificate,
            'independently_verified': False,
            'unpaid_obligation': 'full low-core integral, including every higher jet and uniform remainder'})
    return {'source_matrix': source, 'outside_nullspace': coarse, 'complete_nullspace': complete,
        'promotion_enabled': promotion, 'rows': rows, 'source_values_read': False,
        'full_kernel_cancellation_proved': False, 'RH_proved': False}


def factor_boolean_word(features, coefficients, meter=None):
    """Identify inferred operators by exact coefficient expansion, not names."""
    meter = meter or Meter(); generators = validate_features(features)
    if len(generators) > 10 or len(coefficients) != len(features):
        raise ValueError('bounded Boolean word matching')
    target = {tuple(s): Q(a) for s, a in zip(features, coefficients) if Q(a)}
    if not target: raise ValueError('nonzero relation word')
    for states in product((0, 1, 2), repeat=len(generators)):
        # 0=unused, 1=E_p=I-D_p, 2=D_p.
        expansion = {(): Q(1)}
        for p, state in zip(generators, states):
            if state == 0: continue
            next_terms = {}
            for word, a in expansion.items():
                joined = tuple(sorted(word+(p,)))
                if state == 1: next_terms[word] = next_terms.get(word, Q(0))+a
                next_terms[joined] = next_terms.get(joined, Q(0))+(-a if state == 1 else a)
            expansion = {word: a for word, a in next_terms.items() if a}
            meter.charge(2*len(expansion))
        if expansion == target:
            return {'E_primes': [p for p, s in zip(generators, states) if s == 1],
                'D_primes': [p for p, s in zip(generators, states) if s == 2],
                'source_domain': 'radical-invariant K, integer n>=2',
                'source_identity': 'product(E_p)*product(D_p)*K(n)',
                'full_source_bound_proved': False}
    return None


def verify_boolean_word(features, coefficients, word, meter=None):
    """Independent truth-table check of a proposed multilinear factorization.

    Combined with055's checked commuting idempotents, equality on the whole
    Boolean cube proves the operator identity on the declared source space.
    """
    meter = meter or Meter(); generators = validate_features(features)
    if word is None: return False
    if (set(word) != {'E_primes', 'D_primes', 'source_domain', 'source_identity', 'full_source_bound_proved'}
            or word['source_domain'] != 'radical-invariant K, integer n>=2'
            or word['source_identity'] != 'product(E_p)*product(D_p)*K(n)'
            or word['full_source_bound_proved'] is not False):
        raise ValueError('exact scoped Boolean factorization')
    E, D = primes(word['E_primes']), primes(word['D_primes'])
    if set(E)&set(D) or not set(E+D) <= set(generators): raise ValueError('disjoint known generators')
    if len(generators) > 10 or len(coefficients) != len(features): raise ValueError('bounded Boolean truth table')
    for values in product((0, 1), repeat=len(generators)):
        assignment = dict(zip(generators, values))
        left = sum((Q(a)*prod(assignment[p] for p in s) for a, s in zip(coefficients, features)), Q(0))
        right = prod(1-assignment[p] for p in E)*prod(assignment[p] for p in D)
        meter.charge(len(features)+len(E)+len(D))
        if left != right: raise ValueError('Boolean factorization mismatch')
    return True
