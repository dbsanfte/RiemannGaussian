"""Contract complete Mobius/floor sums before bounding the raw repair.

The exact source rewrite leaves signed Mertens windows. It supplies a
uniform absolute tail rule, while the arithmetic head remains unpaid.
"""
from fractions import Fraction as Q

from prime_transfer_algebra_058 import Meter
from mobius_prefix_completion_062 import ordinary_mu


def _export(value):
    value = Q(value)
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > 4096:
        raise OverflowError('sparse prefix rational capacity')
    return str(value)


def decompose(N, y, p, q, ratio, meter):
    """Six floors minus their complete tails; combine before taking norms."""
    floors, steps = {}, {}
    requests = 0
    for b, multiplier in ((p, Q(1)), (q, -ratio)):
        for v, a in ((4, 1), (2, -3), (1, 2)):
            Z, c = v*N//b, multiplier*a
            if not Z:
                continue
            floors[Z] = floors.get(Z, Q(0))+c
            end = Z//(y+1)
            requests += end
            i = 1
            while i <= end:
                T = Z//i
                last = min(end, Z//T)
                mass = c*(last-i+1)
                steps[T] = steps.get(T, Q(0))-mass
                steps[y] = steps.get(y, Q(0))+mass
                i = last+1
                meter.charge(48)
    return ({n: c for n, c in sorted(floors.items()) if c},
            {n: c for n, c in sorted(steps.items()) if c}, requests)


def window_kernel(steps, j, meter):
    """Coalesce the signed integer intervals, retaining all endpoints."""
    events = {}
    for T, c in steps.items():
        lo, hi = T//(j+1)+1, T//j
        meter.charge(24)
        if lo > hi:
            continue
        events[lo] = events.get(lo, Q(0))+c
        events[hi+1] = events.get(hi+1, Q(0))-c
    answer, value, previous = [], Q(0), None
    for at in sorted(events):
        if value and previous is not None and previous < at:
            if answer and answer[-1]['hi']+1 == previous and Q(answer[-1]['coefficient']) == value:
                answer[-1]['hi'] = at-1
            else:
                answer.append({'lo': previous, 'hi': at-1, 'coefficient': _export(value)})
        value += events[at]
        previous = at
        meter.charge(20)
    if value:
        raise ValueError('interval events must close')
    return answer


def construct(N, y, H, parameters, meter=None):
    meter = Meter() if meter is None else meter
    p, q = parameters['p'], parameters['q']
    if any(type(n) is not int for n in (N, y, H, p, q)) or not 2 <= N <= 65536 or not 2 <= p < q:
        raise ValueError('bounded integer source parameters')
    D = 4*N//p
    if not 1 <= y <= D or not 1 <= H <= min(D, 4096):
        raise ValueError('prefix and short horizon')
    meter.reserve(16*1024**2+512*(D+1)+2048*H)
    mu = ordinary_mu(D, meter)
    M = [0]*(D+1)
    for n in range(1, D+1):
        M[n] = M[n-1]+mu[n]
        meter.charge(4)
    endpoints = []
    for ratio in (Q(p, q), Q(1)):
        floors, steps, requests = decompose(N, y, p, q, ratio, meter)
        rows = []
        for j in range(1, H+1):
            direct = floors.get(j, Q(0))
            segments = window_kernel(steps, j, meter)
            actual, price = direct, abs(direct)
            for seg in segments:
                c = Q(seg['coefficient'])
                actual += c*(M[seg['hi']]-M[seg['lo']-1])
                price += abs(c)*(seg['hi']-seg['lo']+1)
                meter.charge(32)
            rows.append({'j': j, 'direct': _export(direct), 'segments': segments,
                         'coefficient': _export(actual), 'interval_l1': _export(price)})
        tails, joined, actual = [], Q(0), Q(0)
        floor_l1 = sum(map(abs, floors.values()), Q(0))
        M1 = sum((abs(c)*T for T, c in steps.items()), Q(0))
        for J in range(H, 0, -1):
            joined += Q(rows[J-1]['interval_l1'])
            actual += abs(Q(rows[J-1]['coefficient']))
            coarse = sum((abs(c) for Z, c in floors.items() if J <= Z <= H), Q(0))
            coarse += sum((abs(c)*(T//J-T//(H+1)) for T, c in steps.items()), Q(0))
            if not actual <= joined <= coarse <= floor_l1+M1/J:
                raise ValueError('complete tail bound chain')
            tails.append({'J': J, 'H': H, 'joined_interval_upper': _export(joined),
                          'coarse_upper': _export(coarse), 'actual_variation': _export(actual)})
            meter.charge(32*(len(floors)+len(steps)+1))
        endpoints.append({'ratio': str(ratio),
                          'floors': [{'horizon': Z, 'coefficient': _export(c)} for Z, c in floors.items()],
                          'steps': [{'horizon': T, 'coefficient': _export(c)} for T, c in steps.items()],
                          'rows': rows, 'step_first_moment': _export(M1), 'floor_l1': _export(floor_l1),
                          'coefficient_l1': _export(actual), 'tail_bounds': list(reversed(tails))})
    return {'schema': 'mobius-sparse-prefix-inverse-v1', 'parameters': parameters,
            'N': N, 'y': y, 'H': H, 'endpoints': endpoints}


def selected_cutoffs(H, fractions=None):
    """Every canonical rational fraction in(0,1] is a valid tail location."""
    fractions = ['1/8', '1/4', '1/2', '3/4', '1'] if fractions is None else fractions
    if type(fractions) not in (list, tuple) or len(fractions) > 256:
        raise ValueError('finite tail-location request count')
    locations = {1: ['full']}
    for text in fractions:
        if type(text) is not str or not 1 <= len(text) <= 2500:
            raise ValueError('canonical rational tail fraction')
        value = Q(text)
        if str(value) != text or not 0 < value <= 1 or max(value.numerator.bit_length(), value.denominator.bit_length()) > 4096:
            raise ValueError('bounded canonical rational tail fraction')
        at = (H*value.numerator+value.denominator-1)//value.denominator
        locations.setdefault(at, []).append(text)
    return [{'J': at, 'labels': labels} for at, labels in sorted(locations.items())]


def block_moments(certificate):
    """Diagnostic moments of the actual raw inverse, not uniform estimates."""
    H = certificate['H']
    result = []
    for endpoint in certificate['endpoints']:
        blocks, J = [], 1
        while J <= H:
            stop = min(2*J-1, H)
            values = [Q(row['coefficient']) for row in endpoint['rows'][J-1:stop]]
            blocks.append({'start': J, 'stop': stop, 'row_count': len(values),
                           'actual_variation': _export(sum(map(abs, values), Q(0))),
                           'actual_energy': _export(sum((v*v for v in values), Q(0))),
                           'joined_interval_upper': _export(sum((Q(row['interval_l1']) for row in endpoint['rows'][J-1:stop]), Q(0)))})
            J *= 2
        result.append({'ratio': endpoint['ratio'], 'blocks': blocks})
    return result
