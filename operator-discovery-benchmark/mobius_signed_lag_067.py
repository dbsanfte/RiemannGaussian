"""Compile the unpaid raw head into exact, joined signed lag moments.

The algebra and diagonal/short-lag inequalities are supplied proof rules.
No finite correlation value is admitted as a uniform arithmetic estimate.
"""
from fractions import Fraction as Q
from math import isqrt

from flint import fmpz_poly

from prime_transfer_algebra_058 import Meter
from mobius_prefix_completion_062 import ordinary_mu


SCHEMA = 'mobius-signed-head-lag-v1'
MAX_N = 65536
MAX_H = 4096
MAX_POWER_BITS = 100000
ROUNDING_DENOMINATOR = 2**24
DEFAULT_EXPONENTS = list(map(str, sorted(
    {Q(a, b) for b in range(1, 8) for a in range(b+1)} |
    {Q(1, 2**k+1) for k in range(9)})))


def rational(text):
    if type(text) is not str or not 1 <= len(text) <= 2500:
        raise ValueError('bounded canonical rational')
    value = Q(text)
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > 4096:
        raise ValueError('canonical rational capacity')
    return value


def power_cutoff(N, text, meter=None):
    """Exact floor(N**delta); denominators have no mathematical whitelist."""
    meter = Meter() if meter is None else meter
    if type(N) is not int or not 2 <= N <= MAX_N:
        raise ValueError('bounded scale')
    delta = rational(text)
    if not 0 <= delta <= 1:
        raise ValueError('lag exponent in[0,1]')
    bits = N.bit_length()*max(delta.numerator, delta.denominator)
    if bits > MAX_POWER_BITS:
        raise OverflowError('exact power intermediate bit capacity')
    meter.charge(1+bits*max(1, bits.bit_length()))
    target = N**delta.numerator
    lo, hi = 0, N+1
    while hi-lo > 1:
        mid = (lo+hi)//2
        meter.charge(1+bits*max(1, bits.bit_length()))
        if mid**delta.denominator <= target:
            lo = mid
        else:
            hi = mid
    return lo


def sqrt_upper(value):
    value = Q(value)
    if value < 0:
        raise ValueError('nonnegative radicand')
    den = ROUNDING_DENOMINATOR
    a = isqrt(value.numerator*den*den//value.denominator)
    if a*a*value.denominator < value.numerator*den*den:
        a += 1
    return Q(a, den)


def exact_correlations(values, meter):
    """R(h)=sum_n values[n]values[n+h], using exact integer polynomials."""
    size = len(values)
    if not size:
        return []
    height = max(map(abs, values), default=0)
    # A conservative scalar/bit work proxy, not a count of FLINT internals.
    bits = max(1, (size*height*height).bit_length())
    meter.charge(64*size*max(1, size.bit_length())**2*bits)
    product = fmpz_poly(values)*fmpz_poly(list(reversed(values)))
    return [int(product[size-1+h]) for h in range(size)]


def programs(N, exponents, meter):
    if type(exponents) is not list or not 1 <= len(exponents) <= 128:
        raise ValueError('bounded nonempty exponent requests')
    if any(type(t) is not str for t in exponents) or len(set(exponents)) != len(exponents):
        raise ValueError('distinct canonical exponent requests')
    return [{'exponent': None, 'requested_cutoff': 0}] + [
        {'exponent': delta, 'requested_cutoff': power_cutoff(N, delta, meter)}
        for delta in exponents]


def construct(source, exponents=None, meter=None):
    """Consume a separately admitted066 source; never select a different fill."""
    meter = Meter() if meter is None else meter
    exponents = list(DEFAULT_EXPONENTS) if exponents is None else exponents
    N, y, H = (source[k] for k in ('N', 'y', 'H'))
    if source.get('schema') != 'mobius-sparse-prefix-inverse-v1':
        raise ValueError('same raw sparse source required')
    if any(type(v) is not int for v in (N, y, H)) or not 2 <= N <= MAX_N:
        raise ValueError('bounded scale and horizon')
    p, q = source['parameters']['p'], source['parameters']['q']
    D = 4*N//p
    if not 1 <= y <= D or not 1 <= H <= min(D, MAX_H):
        raise ValueError('complete bounded prefix source')
    head_stop = (H+1)//2-1
    candidates = programs(N, exponents, meter)
    meter.reserve(32*1024**2+4096*(D+1)+4096*H)
    mu = ordinary_mu(D, meter)
    endpoints = []
    for source_endpoint, ratio in zip(source['endpoints'], (Q(p, q), Q(1))):
        if source_endpoint['ratio'] != str(ratio) or len(source_endpoint['rows']) != H:
            raise ValueError('complete source endpoint rows')
        den = ratio.denominator
        M1 = rational(source_endpoint['step_first_moment'])
        floor_l1 = rational(source_endpoint['floor_l1'])
        blocks, start = [], 1
        while start <= head_stop:
            stop = min(2*start-1, head_stop)
            total = [0]*(D//start)
            row_sums, direct, kernel_l1 = [], [], Q(0)
            max_kernel = Q(0)
            for row in source_endpoint['rows'][start-1:stop]:
                j = row['j']
                values = [0]*(D//j)
                for seg in row['segments']:
                    coefficient = rational(seg['coefficient'])
                    scaled = coefficient*den
                    if scaled.denominator != 1:
                        raise ValueError('common exact source denominator')
                    max_kernel = max(max_kernel, abs(coefficient))
                    kernel_l1 += abs(coefficient)*(seg['hi']-seg['lo']+1)
                    for n in range(seg['lo'], seg['hi']+1):
                        values[n-1] = scaled.numerator*mu[n]
                        meter.charge(8)
                if max_kernel > 4:
                    raise ValueError('joined tail-source jump amplitude')
                row_sum = sum(values)
                if Q(row_sum, den)+Q(row['direct']) != Q(row['coefficient']):
                    raise ValueError('same source raw coefficient')
                row_sums.append(row_sum)
                direct.append(row['direct'])
                for h, value in enumerate(exact_correlations(values, meter)):
                    total[h] += value
                    meter.charge(4)
            diag, cross = Q(total[0], den*den), Q(2*sum(total[1:]), den*den)
            moment = Q(sum(a*a for a in row_sums), den*den)
            diagonal_upper, universal_diagonal = 4*kernel_l1, 4*M1/start
            if moment != diag+cross or not 0 <= diag <= diagonal_upper <= universal_diagonal:
                raise ValueError('diagonal/moment identity or uniform majorant')
            absolute_direct = sum(map(lambda x: abs(Q(x)), direct), Q(0))
            actual = sum((abs(Q(a, den)+Q(d)) for a, d in zip(row_sums, direct)), Q(0))
            count = stop-start+1
            trials = []
            prefix = [0]
            for v in total[1:]:
                prefix.append(prefix[-1]+v)
            for candidate in candidates:
                B = min(candidate['requested_cutoff'], len(total)-1)
                near = Q(2*prefix[B], den*den)
                far = cross-near
                paid = (4+8*B)*M1/start
                upper = paid+max(far, Q(0))
                if moment > upper:
                    raise ValueError('near-lag payment and signed-far transfer')
                trials.append({**candidate, 'used_cutoff': B,
                    'near_signed': str(near), 'far_signed': str(far),
                    'paid_moment_upper': str(paid), 'finite_moment_upper': str(upper),
                    'finite_head_upper': str(absolute_direct+sqrt_upper(count*upper)),
                    'paid_head_upper': str(sqrt_upper(count*paid)),
                    'unpaid_risk_upper': str(sqrt_upper(count*max(far, Q(0)))),
                    'far_nonpositive_observed': far <= 0,
                    'uniform_far_bound_proved': False})
            blocks.append({'start': start, 'stop': stop,
                'correlation_numerators': total, 'row_sums_scaled': row_sums,
                'direct_coefficients': direct, 'joined_kernel_l1': str(kernel_l1),
                'max_kernel': str(max_kernel), 'diagonal': str(diag),
                'signed_cross': str(cross), 'moment': str(moment),
                'diagonal_upper': str(diagonal_upper),
                'uniform_diagonal_upper': str(universal_diagonal),
                'actual_head_variation': str(actual),
                'cauchy_upper': str(absolute_direct+sqrt_upper(count*moment)),
                'candidates': trials})
            start *= 2
        endpoints.append({'ratio': str(ratio), 'denominator': den,
                          'step_first_moment': str(M1), 'floor_l1': str(floor_l1),
                          'blocks': blocks})
    if len(source['endpoints']) != 2:
        raise ValueError('both ratio endpoints')
    return {'schema': SCHEMA, 'N': N, 'y': y, 'H': H,
            'parameters': source['parameters'], 'head_stop': head_stop,
            'exponent_requests': exponents, 'rounding_denominator': ROUNDING_DENOMINATOR,
            'endpoints': endpoints, 'uniform_full_head_bound_proved': False,
            'RH_proved': False}


def summarize(certificate):
    """Every candidate remains visible; no empirical exponent is fitted."""
    result = []
    for endpoint in certificate['endpoints']:
        rows = []
        for index, exponent in enumerate([None]+certificate['exponent_requests']):
            parts = [block['candidates'][index] for block in endpoint['blocks']]
            direct = sum((abs(Q(v)) for block in endpoint['blocks'] for v in block['direct_coefficients']), Q(0))
            rows.append({'exponent': exponent,
                'paid_power': str((1+(Q(exponent) if exponent is not None else Q(0)))/2),
                'finite_head_upper': str(sum((Q(p['finite_head_upper']) for p in parts), Q(0))),
                'paid_head_upper': str(direct+sum((Q(p['paid_head_upper']) for p in parts), Q(0))),
                'unpaid_risk_upper': str(sum((Q(p['unpaid_risk_upper']) for p in parts), Q(0))),
                'positive_far_blocks': sum(Q(p['far_signed']) > 0 for p in parts),
                'total_blocks': len(parts), 'uniform_far_bound_proved': False})
        frontier = [a['exponent'] for a in rows if not any(
            Q(b['paid_power']) <= Q(a['paid_power']) and
            Q(b['unpaid_risk_upper']) <= Q(a['unpaid_risk_upper']) and
            (Q(b['paid_power']) < Q(a['paid_power']) or
             Q(b['unpaid_risk_upper']) < Q(a['unpaid_risk_upper']))
            for b in rows)]
        result.append({'ratio': endpoint['ratio'], 'candidates': rows,
            'finite_evidence_pareto_exponents': frontier,
            'pareto_scope': 'paid exponent versus observed remaining risk; no uniform far bound',
            'actual_head_variation': str(sum((Q(b['actual_head_variation']) for b in endpoint['blocks']), Q(0))),
            'moment_cauchy_upper': str(sum((Q(b['cauchy_upper']) for b in endpoint['blocks']), Q(0))),
            'diagonal_only_claim_counterexamples': [b['start'] for b in endpoint['blocks'] if Q(b['signed_cross']) > 0]})
    return result
