"""Exact ordinary-prime identities for supplied rational floor profiles.

Supplied profiles are inputs, not independently verified source recipes.
This layer proves finite algebra, not a global bound or convergence.
"""
from fractions import Fraction as Q
import math
import time

MAX_PARENT_SUPPORT = 3072
MAX_INDEX = 4096
MAX_INPUT_BITS = 4096
MAX_LATTICE_BITS = 8192
MAX_RESULT_BITS = 32768
MAX_ENERGY_BITS = 400000
MAX_BLOCK_LENGTH = 65536
MAX_ESTIMATED_BYTES = 4*1024**3


class Meter:
    def __init__(self, cap=2_000_000_000, seconds=1200):
        if type(cap) is not int or cap < 0:
            raise ValueError('nonnegative integer work cap')
        if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
            raise ValueError('positive finite time cap')
        self.cap, self.operations, self.deadline = cap, 0, time.monotonic()+seconds
        self.sieve_updates = self.rational_operations = self.cell_rows = self.program_columns = 0
        self.max_rational_bits = self.input_lattice_bits = self.estimated_peak_bytes = 0

    def charge(self, amount=1):
        if type(amount) is not int or amount < 0 or amount > self.cap-self.operations:
            raise OverflowError('prime construction work cap')
        self.operations += amount
        if time.monotonic() > self.deadline:
            raise TimeoutError('prime construction deadline')

    def rational(self, value, bit_cap=MAX_RESULT_BITS):
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        if bits > bit_cap:
            raise OverflowError('prime rational result bit cap')
        self.max_rational_bits = max(self.max_rational_bits, bits)
        self.rational_operations += 1
        self.charge(1+abs(value.numerator).bit_length()+value.denominator.bit_length())
        return value

    def counts(self):
        return {name: getattr(self, name) for name in ('operations', 'sieve_updates',
                'rational_operations', 'cell_rows', 'program_columns', 'max_rational_bits',
                'input_lattice_bits', 'estimated_peak_bytes')}


def _meter(meter):
    return meter if meter is not None else Meter()


def _decimal(value):
    # The admitted exact cell energies can exceed Python's 4300-digit
    # int-string limit. Keep that process-wide protection enabled.
    if abs(value).bit_length() < 12000:
        return str(value)
    negative, value = value < 0, abs(value)
    chunks = []
    while value:
        value, chunk = divmod(value, 10**18)
        chunks.append(chunk)
    text = str(chunks[-1])+''.join(str(c).zfill(18) for c in reversed(chunks[:-1]))
    return '-'+text if negative else text


def _text(value):
    value = Q(value)
    numerator = _decimal(value.numerator)
    return numerator if value.denominator == 1 else numerator+'/'+_decimal(value.denominator)


def _value(text):
    """Read this producer's bounded emitted program scalars, including large ones."""
    if len(text) < 4000:
        return Q(text)
    if len(text) > 2*MAX_RESULT_BITS:
        raise OverflowError('emitted prime program scalar text cap')
    def integer(digits):
        negative = digits.startswith('-')
        if negative: digits = digits[1:]
        result = 0
        for start in range(0, len(digits), 18):
            chunk = digits[start:start+18]
            result = result*10**len(chunk)+int(chunk)
        return -result if negative else result
    parts = text.split('/')
    if len(parts) not in (1, 2):
        raise ValueError('emitted rational scalar')
    return Q(integer(parts[0]), integer(parts[1]) if len(parts) == 2 else 1)


def rational(text):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational input')
    value = Q(text)
    if str(value) != text:
        raise ValueError('canonical rational input')
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_INPUT_BITS:
        raise OverflowError('prime input rational bit cap')
    return value


def _prime(p, meter):
    if type(p) is not int or not 2 <= p <= MAX_INDEX:
        raise ValueError('actual integer prime2..4096 required')
    for divisor in range(2, math.isqrt(p)+1):
        meter.charge(4)
        if p % divisor == 0:
            raise ValueError('dilation index must be an actual prime')
    return p


def _request(request, meter):
    if type(request) is not dict or set(request) != {'prime', 'parent_support', 'parent_values', 'child_values'}:
        raise ValueError('exact prime construction request')
    p, N = _prime(request['prime'], meter), request['parent_support']
    if type(N) is not int or not 1 <= N <= MAX_PARENT_SUPPORT or p*N > MAX_INDEX:
        raise ValueError('parent support1..3072 and child index<=4096')
    U, V = request['parent_values'], request['child_values']
    if type(U) is not list or type(V) is not list or len(U) != N or len(V) != p*N:
        raise ValueError('profiles indexed exactly1..N and1..pN')
    U, V = [rational(x) for x in U], [rational(x) for x in V]
    if U[0] != 1 or V[0] != 1:
        raise ValueError('both profile units must be exactly1')
    D = 1
    for value in U+V:
        meter.rational(value)
        D = math.lcm(D, value.denominator)
        meter.charge(D.bit_length())
        if D.bit_length() > MAX_LATTICE_BITS:
            raise OverflowError('prime profile common lattice bit cap')
    meter.input_lattice_bits = max(meter.input_lattice_bits, D.bit_length())
    source = {'prime': p, 'parent_support': N,
              'parent_values': [str(v) for v in U], 'child_values': [str(v) for v in V]}
    return p, N, [Q(0)]+U, [Q(0)]+V, D, source


def _mobius(H, meter):
    least = [0]*(H+1)
    for p in range(2, H+1):
        if not least[p]:
            for n in range(p, H+1, p):
                if not least[n]:
                    least[n] = p
                meter.sieve_updates += 1
                meter.charge(1)
    mu, rows = [0]*(H+1), []
    for n in range(1, H+1):
        remaining, factors = n, []
        while remaining > 1:
            p, e = least[remaining], 0
            while remaining % p == 0:
                remaining //= p
                e += 1
                meter.charge(4)
            factors.append({'prime': p, 'exponent': e})
        mu[n] = 0 if any(row['exponent'] > 1 for row in factors) else (-1)**len(factors)
        rows.append({'n': n, 'factors': factors, 'mu': mu[n]})
    return mu, rows


def _program(identifier, coefficients=None, steps=None, constant=Q(0), meter=None):
    meter = _meter(meter)
    coefficients, steps = coefficients or {}, steps or {}
    if any(type(n) is not int or not 2 <= n <= MAX_INDEX for n in coefficients):
        raise ValueError('floor basis index2..4096')
    if any(type(q) is not int or not 2 <= q <= MAX_INDEX for q in steps):
        raise ValueError('indicator threshold2..4096')
    floor_rows = [{'n': n, 'value': _text(meter.rational(Q(c)))} for n, c in sorted(coefficients.items()) if c]
    step_rows = [{'q': q, 'value': _text(meter.rational(Q(c)))} for q, c in sorted(steps.items()) if c]
    meter.program_columns += len(floor_rows)+len(step_rows)+1
    return {'id': identifier, 'constant': _text(meter.rational(Q(constant))),
            'coefficients': floor_rows, 'steps': step_rows}


def _add(identifier, weighted_programs, meter):
    coefficients, steps, constant = {}, {}, Q(0)
    for weight, program in weighted_programs:
        constant = meter.rational(constant+weight*_value(program['constant']))
        for row in program['coefficients']:
            n = row['n']
            coefficients[n] = meter.rational(coefficients.get(n, Q(0))+weight*_value(row['value']))
        for row in program['steps']:
            q = row['q']
            steps[q] = meter.rational(steps.get(q, Q(0))+weight*_value(row['value']))
    return _program(identifier, coefficients, steps, constant, meter)


def _dilate(identifier, program, p, meter):
    coefficients, steps = {}, {}
    if _value(program['constant']):
        steps[p] = -_value(program['constant'])
    for row in program['coefficients']:
        n, c = row['n'], _value(row['value'])
        coefficients[p*n] = meter.rational(coefficients.get(p*n, Q(0))+c)
        coefficients[p] = meter.rational(coefficients.get(p, Q(0))-c/n)
    for row in program['steps']:
        q, d = row['q'], _value(row['value'])
        steps[p*q] = meter.rational(steps.get(p*q, Q(0))+d)
    return _program(identifier, coefficients, steps, Q(0), meter)


def _identity(name, left, right, meter):
    difference = _add(name+'_difference', [(Q(1), left), (Q(-1), right)], meter)
    holds = difference['constant'] == '0' and not difference['coefficients'] and not difference['steps']
    if not holds:
        raise ArithmeticError('prime construction program identity failed: '+name)
    return {'name': name, 'left': left, 'right': right, 'difference': difference, 'holds': True,
            'comparison': 'constant and every signed floor/indicator column'}


def _B(identifier, limit, profile, mu, p, meter, sign=Q(1)):
    return _program(identifier, {n: -sign*mu[n]*profile(n) for n in range(2, limit+1) if n % p}, meter=meter)


def _T(limit, profile, mu, p, meter):
    result = Q(0)
    for n in range(1, limit+1):
        if n % p and mu[n]:
            result = meter.rational(result+mu[n]*profile(n)/n)
    return result


def _harmonic(values, mu, limit, meter):
    result = Q(0)
    for n in range(1, limit+1):
        if mu[n] and values[n]:
            result = meter.rational(result+mu[n]*values[n]/n)
    return result


def _sum_blocks(identifier, blocks, meter):
    return _add(identifier, [(Q(1), block['program']) for block in blocks], meter)


def _memory(meter, estimated):
    if estimated > MAX_ESTIMATED_BYTES:
        raise OverflowError('prime construction prospective memory cap')
    meter.estimated_peak_bytes = max(meter.estimated_peak_bytes, estimated)


def build_prime_construction(request, meter=None):
    meter = _meter(meter)
    p, N, U, V, D, source = _request(request, meter)
    # Generous ceiling for copies of coefficients, factors and identity rows.
    _memory(meter, (p*N+N+1)*(16384+32*((D.bit_length()+4096+7)//8)))
    mu, mu_rows = _mobius(p*N, meter)
    parent = _program('parent', {n: -mu[n]*U[n] for n in range(2, N+1)}, constant=Q(1), meter=meter)
    child = _program('child', {n: -mu[n]*V[n] for n in range(2, p*N+1)}, constant=Q(1), meter=meter)
    original = _add('original_forcing', [(Q(1), child), (Q(1), _dilate('dilated_parent', parent, p, meter))], meter)
    S_U = _harmonic(U, mu, N, meter)
    Tv = _T(N, lambda n: V[p*n], mu, p, meter)
    Tu = _T(N//p, lambda n: U[p*n], mu, p, meter)
    unit = _program('unit_and_indicator', steps={p: Q(-1)}, constant=Q(1), meter=meter)
    child_B = _B('coprime_child', p*N, lambda n: V[n], mu, p, meter)
    difference_B = _B('profile_difference_before_dilation', N, lambda n: U[n]-V[p*n], mu, p, meter)
    square_B = _B('square_parent_before_dilation', N//p, lambda n: U[p*n], mu, p, meter, Q(-1))
    blocks = [
        {'label': 'unit_and_indicator', 'program': unit},
        {'label': 'coprime_child', 'program': child_B},
        {'label': 'dilated_coprime_profile_difference', 'program': _dilate('dilated_coprime_profile_difference', difference_B, p, meter)},
        {'label': 'square_dilated_coprime_parent', 'program': _dilate('square_dilated_coprime_parent', square_B, p*p, meter) if N//p >= 2 else _program('square_dilated_coprime_parent', meter=meter)},
        {'label': 'scalar_child_shift', 'program': _program('scalar_child_shift', {p: Tv}, meter=meter)},
        {'label': 'scalar_square_parent_shift', 'program': _dilate('scalar_square_parent_shift', _program('scalar_parent_before_dilation', {p: Tu}, meter=meter), p, meter) if Tu else _program('scalar_square_parent_shift', meter=meter)}]
    split_sum = _sum_blocks('prime_split_sum', blocks, meter)
    split_identity = _identity('prime_split_equals_original', split_sum, original, meter)
    source_rows = []
    for n in range(1, p*N+1):
        part, valuation = n, 0
        while part % p == 0:
            part //= p
            valuation += 1
            meter.charge(2)
        child_term = meter.rational(mu[n]*V[n])
        parent_term = meter.rational(mu[n//p]*U[n//p]) if n % p == 0 else Q(0)
        source_rows.append({'n': n, 'valuation': valuation, 'prime_free_part': part,
                            'child_term': _text(child_term), 'parent_term': _text(parent_term),
                            'value': _text(meter.rational(child_term+parent_term))})
    lam = V[p]
    identities = [split_identity]
    if lam:
        Qvalues = [Q(0)]+[meter.rational(V[p*n]/lam) for n in range(1, N+1)]
        matched_parent = _program('matched_parent', {n: -mu[n]*Qvalues[n] for n in range(2, N+1)}, constant=Q(1), meter=meter)
    else:
        Qvalues, matched_parent = None, None
    # This direct vector is lambda*e_Q when normalization exists, but is
    # defined without division even at lambda0.
    direct_parent = _program('direct_shifted_parent',
        {n: -mu[n]*V[p*n] for n in range(2, N+1)}, constant=lam, meter=meter)
    matched_program = _add('matched_forcing', [(Q(1), child), (Q(1), _dilate('dilated_direct_shifted_parent', direct_parent, p, meter))], meter)
    matched_unit = _program('matched_unit_and_indicator', steps={p: -lam}, constant=Q(1), meter=meter)
    square_child_B = _B('matched_square_before_dilation', N//p, lambda n: V[p*p*n], mu, p, meter, Q(-1))
    Tvv = _T(N//p, lambda n: V[p*p*n], mu, p, meter)
    matched_blocks = [
        {'label': 'matched_unit_and_indicator', 'program': matched_unit},
        {'label': 'coprime_child', 'program': child_B},
        {'label': 'square_dilated_shifted_child', 'program': _dilate('square_dilated_shifted_child', square_child_B, p*p, meter) if N//p >= 2 else _program('square_dilated_shifted_child', meter=meter)},
        {'label': 'scalar_child_shift', 'program': _program('matched_scalar_child_shift', {p: Tv}, meter=meter)},
        {'label': 'scalar_square_child_shift', 'program': _dilate('scalar_square_child_shift', _program('matched_scalar_square_before_dilation', {p: Tvv}, meter=meter), p, meter) if Tvv else _program('scalar_square_child_shift', meter=meter)}]
    matched_sum = _sum_blocks('matched_prime_split_sum', matched_blocks, meter)
    identities.append(_identity('matched_split_equals_forcing', matched_sum, matched_program, meter))
    if lam:
        scaled_normalized = _add('scaled_normalized_parent', [(lam, matched_parent)], meter)
        identities.append(_identity('direct_parent_equals_scaled_normalized_parent', direct_parent, scaled_normalized, meter))
    conversion_inner = _program('conversion_before_dilation',
        {n: -mu[n]*(U[n]-V[p*n]) for n in range(2, N+1)}, constant=1-lam, meter=meter)
    conversion = _dilate('conversion_auxiliary', conversion_inner, p, meter)
    converted_sum = _add('matched_plus_conversion', [(Q(1), matched_program), (Q(1), conversion)], meter)
    identities.append(_identity('matched_plus_conversion_equals_original', converted_sum, original, meter))
    cancelled = []
    for n in range(1, N+1):
        if n % p:
            child_term, parent_term = -mu[n]*V[p*n], mu[n]*V[p*n]
            cancelled.append({'prime_free_index': n, 'source_index': p*n,
                              'child_term': _text(child_term), 'parent_term': _text(parent_term),
                              'value': _text(meter.rational(child_term+parent_term))})
    matched = {'status': 'available' if lam else 'unmatched_only', 'lambda': str(lam),
               'normalized_parent_values': [_text(v) for v in Qvalues[1:]] if lam else None,
               'parent_program': matched_parent, 'direct_parent_program': direct_parent,
               'program': matched_program, 'blocks': matched_blocks, 'sum': matched_sum,
               'conversion_auxiliary': conversion, 'cancelled_valuation_one': cancelled,
               'square_child_shift_coprime_scalar': _text(Tvv),
               'range_or_contraction_proved': False,
               'reason': 'normalized parent available' if lam else 'normalization undefined at lambda0; division-free matched and conversion vectors retained'}
    return {'schema': 'floor-prime-construction-v1', 'source_request': source,
            'supplied_values_independently_source_verified': False,
            'mu_certificate': {'kind': 'ordinary-mobius-factorization', 'rows': mu_rows},
            'parent_program': parent, 'child_program': child, 'original_forcing': original,
            'profile_scalar_sums': {'parent_harmonic': _text(S_U),
                                    'child_shift_coprime': _text(Tv), 'square_parent_shift_coprime': _text(Tu)},
            'prime_split': {'blocks': blocks, 'sum': split_sum, 'identity': split_identity},
            'p_adic_source_coefficients': source_rows, 'matched': matched, 'identities': identities,
            'identity_only': True, 'global_bound_status': 'OPEN', 'norm_convergence_status': 'OPEN',
            'RH_proved': False, 'RH_refuted': False, 'counts': meter.counts()}


def _divisor_prefix(source, endpoint, meter):
    divisors = [Q(0)]*(endpoint+1)
    for n in range(1, min(len(source)-1, endpoint)+1):
        if source[n]:
            for k in range(n, endpoint+1, n):
                divisors[k] = meter.rational(divisors[k]+source[n])
    prefix = [Q(0)]*(endpoint+1)
    for k in range(1, endpoint+1):
        prefix[k] = meter.rational(prefix[k-1]+divisors[k])
    return divisors, prefix


def cell_energy_certificate(request, K, meter=None):
    """Exact energy on cells K..2K-1 only, with all truncated divisor tails."""
    meter = _meter(meter)
    if type(K) is not int or not 1 <= K <= MAX_BLOCK_LENGTH or K & (K-1):
        raise ValueError('power-of-two block K1..65536')
    p, N, U, V, D, source = _request(request, meter)
    end, parent_end = 2*K-1, (2*K-1)//p
    mu, mu_rows = _mobius(p*N, meter)
    a = [Q(0)]+[meter.rational(mu[n]*V[n]) for n in range(1, p*N+1)]
    b = [Q(0)]+[meter.rational(mu[n]*U[n]) for n in range(1, N+1)]
    S_V, S_U = _harmonic(V, mu, p*N, meter), _harmonic(U, mu, N, meter)
    # Estimate actual harmonic numerator/denominator sizes and the integer
    # scaled source bound before allocating prefix tables or output rows.
    scaled_sum = sum(abs(value*D) for value in a+b)
    source_bits = int(scaled_sum).bit_length()+end.bit_length()+4
    scalar_bits = max(source_bits, S_V.numerator.bit_length(), S_V.denominator.bit_length(),
                      S_U.numerator.bit_length(), S_U.denominator.bit_length())+end.bit_length()+4
    scalar_bytes = 256+8*((scalar_bits+7)//8)
    estimated = 4*(end+parent_end+2)*scalar_bytes+K*(1024+20*scalar_bytes)
    _memory(meter, estimated)
    Cc, Pc = _divisor_prefix(a, end, meter)
    Cp, Pp = _divisor_prefix(b, parent_end, meter)
    rows, energy, weighted = [], Q(0), Q(0)
    for k in range(K, 2*K):
        j, unit = k//p, Q(1+int(k >= p))
        child_harmonic, parent_harmonic = meter.rational(k*S_V), meter.rational(j*S_U)
        value = meter.rational(unit+child_harmonic+parent_harmonic-Pc[k]-Pp[j])
        square = meter.rational(value*value, MAX_ENERGY_BITS)
        weight = Q(1, k*(k+1))
        weighted_square = meter.rational(square*weight, MAX_ENERGY_BITS)
        energy = meter.rational(energy+square, MAX_ENERGY_BITS)
        weighted = meter.rational(weighted+weighted_square, MAX_ENERGY_BITS)
        meter.cell_rows += 1
        rows.append({'k': k, 'parent_cell': j, 'unit_and_indicator': _text(unit),
                     'child_truncated_divisor_sum': _text(Cc[k]), 'parent_truncated_divisor_sum': _text(Cp[j]),
                     'child_harmonic_term': _text(child_harmonic), 'parent_harmonic_term': _text(parent_harmonic),
                     'child_floor_sum': _text(Pc[k]), 'parent_floor_sum': _text(Pp[j]),
                     'value': _text(value), 'weight': _text(weight), 'weighted_square': _text(weighted_square)})
    return {'schema': 'floor-prime-cell-energy-v1', 'source_request': source,
            'supplied_values_independently_source_verified': False,
            'mu_certificate': {'kind': 'ordinary-mobius-factorization', 'rows': mu_rows},
            'K': K, 'end_exclusive': 2*K, 'source_harmonic_sums': {'child': _text(S_V), 'parent': _text(S_U)},
            'cells': rows, 'energy': _text(energy), 'weighted_norm': _text(weighted),
            'domain': 'cells K..2K-1, x in (1/(2K),1/K]',
            'unobserved_cells_or_tails_inferred': False, 'whole_norm_proved': False,
            'global_bound_status': 'OPEN', 'RH_proved': False, 'RH_refuted': False,
            'counts': meter.counts()}
