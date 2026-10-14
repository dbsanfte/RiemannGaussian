"""Reversible arithmetic words with dyadic maps and retained pair mixing.

Exact evaluation supplies candidate evidence.  The recovery certificate proves
only a uniform inverse norm; the source-specific moment estimate remains open.
"""
from copy import deepcopy
from fractions import Fraction as Q

import reversible_divisor_circuits as V
from potential_candidate_language import Meter

MAX_HORIZON = V.MAX_HORIZON
SCHEMA = 'permuted-arithmetic-circuit-v1'
DOMAIN = 'closed_dyadic_horizon_weighted_l2_half_lt_sigma_le_one'
BOUND = '3^permutation_count*shear_factor*(1+1/epsilon)^recovery_power'
BINDING = 'same_fixed_source_and_block_branches_in_inverse'
root = V.root
rational = V.rational


def _phase_syntax(tree, meter):
    V.validate({'stages': [{'op': 'sign', 'phase': tree}]}, meter)


def _map_syntax(tree, meter):
    count = 0

    def walk(node, depth):
        nonlocal count
        meter.charge(); count += 1
        if count > 15 or depth > 3 or type(node) is not dict:
            raise ValueError('bounded dyadic map tree')
        kind = node.get('kind')
        if type(kind) is not str:
            raise ValueError('explicit map kind')
        if kind == 'polynomial' and set(node) == {'kind', 'coefficients'}:
            coefficients = node['coefficients']
            if type(coefficients) is not list or not 2 <= len(coefficients) <= 5:
                raise ValueError('polynomial degree one through four')
            for c in coefficients:
                meter.charge(); V._integer(c, -8, 8)
            if coefficients[1] % 2 != 1 or any(c % 2 for c in coefficients[2:]):
                raise ValueError('odd linear and even higher coefficients')
        elif kind == 'xor' and set(node) == {'kind', 'mask'}:
            if type(node['mask']) is not str or node['mask'] not in ('all', 'top', 'alternating'):
                raise ValueError('declared bit mask')
        elif kind == 'reverse_bits' and set(node) == {'kind'}:
            pass
        elif kind == 'rotate_bits' and set(node) == {'kind', 'shift'}:
            V._integer(node['shift'], -4, 4)
            if node['shift'] == 0:
                raise ValueError('nonzero fixed rotation')
        elif kind == 'compose' and set(node) == {'kind', 'maps'}:
            if type(node['maps']) is not list or not 2 <= len(node['maps']) <= 3:
                raise ValueError('two or three composed maps')
            for child in node['maps']:
                walk(child, depth + 1)
        elif kind == 'choose' and set(node) == {'kind', 'phase', 'positive', 'negative'}:
            _phase_syntax(node['phase'], meter)
            walk(node['positive'], depth + 1)
            walk(node['negative'], depth + 1)
        else:
            raise ValueError('exact dyadic map schema')

    walk(tree, 0)


def validate(program, meter):
    meter.charge()
    if type(program) is not dict or set(program) != {'stages'}:
        raise ValueError('exact stages-only program')
    stages = program['stages']
    if type(stages) is not list or len(stages) > 7:
        raise ValueError('at most seven circuit stages')
    counts = dict(convolve=0, sign=0, permute=0, shear=0)
    for stage in stages:
        meter.charge()
        if type(stage) is not dict or type(stage.get('op')) is not str:
            raise ValueError('explicit stage object')
        op = stage['op']
        if op in ('convolve', 'sign'):
            V.validate({'stages': [stage]}, meter)
        elif op == 'permute' and set(stage) == {'op', 'map', 'inverse'}:
            if type(stage['inverse']) is not bool:
                raise ValueError('strict permutation direction')
            _map_syntax(stage['map'], meter)
        elif op == 'shear' and set(stage) == {'op', 'coefficient', 'phase', 'direction'}:
            coefficient = rational(stage['coefficient'], meter)
            if not coefficient or abs(coefficient) > 2 or coefficient.denominator > 6:
                raise ValueError('nonzero bounded rational shear')
            if type(stage['direction']) is not str or stage['direction'] not in ('even_from_odd', 'odd_from_even'):
                raise ValueError('explicit retained pair direction')
            _phase_syntax(stage['phase'], meter)
        else:
            raise ValueError('exact circuit stage schema')
        counts[op] += 1
    if any(counts[op] > cap for op, cap in (('convolve', 3), ('sign', 3), ('permute', 3), ('shear', 2))):
        raise ValueError('bounded stage types')
    return True


def certificate(program, meter):
    validate(program, meter)
    order, factor = Q(0), Q(1)
    permutations = shears = 0
    for stage in program['stages']:
        meter.charge()
        if stage['op'] == 'convolve':
            order = meter.number(order + abs(rational(stage['alpha'], meter)))
        elif stage['op'] == 'permute':
            permutations += 1
        elif stage['op'] == 'shear':
            shears += 1
            factor = meter.number(factor * (1 + 2 * abs(rational(stage['coefficient'], meter))))
    return dict(schema=SCHEMA, program=deepcopy(program), fractional_order=str(order),
                recovery_power=(order.numerator + order.denominator - 1) // order.denominator,
                permutation_count=permutations, shear_count=shears, shear_factor=str(factor),
                domain=DOMAIN, bound=BOUND, coefficient_binding=BINDING)


def inverse(program, meter):
    validate(program, meter)
    result = deepcopy(program)
    result['stages'].reverse()
    for stage in result['stages']:
        meter.charge()
        if stage['op'] == 'convolve':
            stage['alpha'] = str(-rational(stage['alpha'], meter))
        elif stage['op'] == 'permute':
            stage['inverse'] = not stage['inverse']
        elif stage['op'] == 'shear':
            stage['coefficient'] = str(-rational(stage['coefficient'], meter))
    return result


def normalize(program, meter):
    """Proved word identities and explicitly dyadic terminal isometries."""
    validate(program, meter)
    stages, rewrites = deepcopy(program['stages']), []

    def replace(rule, position, count, after):
        meter.charge(count + len(after) + 1)
        rewrites.append(dict(rule=rule, position=position,
                             before=deepcopy(stages[position:position + count]),
                             after=deepcopy(after)))
        stages[position:position + count] = after

    while True:
        changed = False
        for index, stage in enumerate(stages):
            meter.charge()
            op = stage['op']
            if op == 'permute' and stage['map']['kind'] == 'polynomial':
                c = stage['map']['coefficients']
                if c[:2] == [0, 1] and all(x == 0 for x in c[2:]):
                    replace('identity_permutation', index, 1, [])
                    changed = True; break
            if index + 1 == len(stages):
                continue
            other = stages[index + 1]
            meter.charge()
            if op == other['op'] == 'permute' and stage['map'] == other['map'] and stage['inverse'] != other['inverse']:
                replace('inverse_permutations', index, 2, [])
                changed = True; break
            if op == other['op'] == 'sign' and stage['phase'] == other['phase']:
                replace('inverse_signs', index, 2, [])
                changed = True; break
            merge = None
            if op == other['op'] == 'convolve' and stage['prime_phase'] == other['prime_phase']:
                merge = ('alpha', 'merge_convolutions')
            elif op == other['op'] == 'shear' and stage['phase'] == other['phase'] and stage['direction'] == other['direction']:
                merge = ('coefficient', 'merge_shears')
            if merge:
                field, rule = merge
                total = meter.number(rational(stage[field], meter) + rational(other[field], meter))
                if abs(total) <= 2 and total.denominator <= 6:
                    after = []
                    if total:
                        merged = deepcopy(stage); merged[field] = str(total); after = [merged]
                    replace(rule, index, 2, after)
                    changed = True; break
        if changed:
            continue
        if stages and stages[-1]['op'] in ('sign', 'permute'):
            rule = 'terminal_sign' if stages[-1]['op'] == 'sign' else 'terminal_dyadic_permutation'
            replace(rule, len(stages) - 1, 1, [])
            continue
        break
    normalized = {'stages': stages}
    validate(normalized, meter)
    return dict(program=normalized, rewrites=rewrites, equivalence='dyadic_moments')


def _horizon(H, meter):
    meter.charge(); V._integer(H, 1, MAX_HORIZON)
    if (H + 1) & H:
        raise ValueError('complete closed dyadic horizon 2^K-1 required')


def source(name, H, meter):
    _horizon(H, meter)
    return V.source(name, H, meter)


def _values(values, meter):
    V._validate_source(values, meter)
    _horizon(len(values) - 1, meter)


def _resolve_map(tree, m, k, values, meter):
    """Resolve source choices once per block; no intermediate values are read."""
    meter.charge()
    kind = tree['kind']
    if kind == 'choose':
        branch = 'positive' if V._phase(tree['phase'], m, values, meter) > 0 else 'negative'
        return _resolve_map(tree[branch], m, k, values, meter)
    if kind == 'compose':
        return (kind, [_resolve_map(child, m, k, values, meter) for child in tree['maps']])
    if kind == 'polynomial':
        return kind, tree['coefficients']
    if kind == 'xor':
        mask = tree['mask']
        if mask == 'all':
            return kind, m - 1
        if mask == 'top':
            return kind, m // 2
        bits = 0
        for j in range(0, k, 2):
            meter.charge(); bits = meter.number(bits + (1 << j))
        return kind, bits
    if kind == 'rotate_bits':
        return kind, tree['shift'] % k if k else 0
    return kind, None


def _residue(resolved, r, m, k, meter):
    meter.charge()
    kind, argument = resolved
    if kind == 'polynomial':
        result = 0
        for coefficient in reversed(argument):
            meter.charge()
            result = meter.number(meter.number(result * r + coefficient) % m)
        return result
    if kind == 'xor':
        return meter.number(r ^ argument)
    if kind == 'reverse_bits':
        result = 0
        for j in range(k):
            meter.charge()
            result = meter.number((result << 1) | ((r >> j) & 1))
        return result
    if kind == 'rotate_bits':
        if not k or not argument:
            return r
        return meter.number(((r << argument) | (r >> (k - argument))) & (m - 1))
    if kind == 'compose':
        for child in argument:
            r = _residue(child, r, m, k, meter)
        return r
    raise ValueError('resolved index map')


def _permutation(stage, values, meter):
    H = len(values) - 1
    table = [0] * (H + 1); meter.charge(H + 1)
    m, k = 1, 0
    while m <= H:
        resolved = _resolve_map(stage['map'], m, k, values, meter)
        for r in range(m):
            meter.charge()
            target = m + _residue(resolved, r, m, k, meter)
            if stage['inverse']:
                table[target] = m + r
            else:
                table[m + r] = target
        m *= 2; k += 1
    return table


def _apply(program, values, data, absolute, meter):
    H = len(values) - 1
    meter.live(200000 + 20 * (H + 1))
    spf = V._spf(H, meter) if any(s['op'] == 'convolve' for s in program['stages']) else None
    for stage in program['stages']:
        meter.charge()
        op = stage['op']
        if op == 'sign':
            for n in range(1, H + 1):
                meter.charge()
                data[n] = V._small(data[n] * V._phase(stage['phase'], n, values, meter), meter)
        elif op == 'permute':
            table = _permutation(stage, values, meter)
            meter.charge(2 * (H + 1))
            data, absolute = [data[index] for index in table], [absolute[index] for index in table]
            del table
        elif op == 'shear':
            c = rational(stage['coefficient'], meter)
            for n in range(2, H, 2):
                meter.charge()
                phase = V._phase(stage['phase'], n, values, meter)
                target, other = (n, n + 1) if stage['direction'] == 'even_from_odd' else (n + 1, n)
                term = V._small(c * phase * data[other], meter)
                data[target] = V._small(data[target] + term, meter)
                absolute[target] = V._small(absolute[target] + V._small(abs(c) * absolute[other], meter), meter)
        else:
            kernel = V._kernel(stage, values, spf, meter)
            output, envelope = [0] * (H + 1), [0] * (H + 1)
            meter.charge(2 * (H + 1))
            for d in range(1, H + 1):
                meter.charge()
                coefficient = kernel[d]
                if not coefficient:
                    continue
                magnitude = abs(coefficient)
                for n in range(1, H // d + 1):
                    meter.charge()
                    j = d * n
                    output[j] = V._small(output[j] + V._small(coefficient * data[n], meter), meter)
                    envelope[j] = V._small(envelope[j] + V._small(magnitude * absolute[n], meter), meter)
            data, absolute = output, envelope
            del kernel
    return dict(signed=data, absolute=absolute)


def evaluate(program, values, meter):
    validate(program, meter); _values(values, meter)
    meter.live(200000 + 20 * len(values))
    data = [0]
    for value in values[1:]:
        meter.charge()
        data.append(V._small(data[-1] + value, meter))
    meter.charge(len(data))
    return _apply(program, values, data, [abs(value) for value in data], meter)


def apply_to_state(program, values, state, meter):
    validate(program, meter); _values(values, meter)
    if type(state) is not list or len(state) != len(values) or type(state[0]) not in (int, Q) or state[0] != 0:
        raise ValueError('complete exact state with zero endpoint')
    for value in state:
        meter.number(value)
    meter.live(200000 + 20 * len(values)); meter.charge(2 * len(state))
    return _apply(program, values, list(state), [abs(value) for value in state], meter)['signed']


def _state(state, meter):
    if type(state) is not dict or set(state) != {'signed', 'absolute'}:
        raise ValueError('complete signed and absolute state')
    signed, absolute = state['signed'], state['absolute']
    if type(signed) is not list or type(absolute) is not list or len(signed) != len(absolute):
        raise ValueError('equal complete state vectors')
    _horizon(len(signed) - 1, meter)
    for a, b in zip(signed, absolute):
        meter.number(a); meter.number(b); meter.charge()
        if b < abs(a):
            raise ValueError('path envelope dominates complete signed state')
    if signed[0] != 0 or absolute[0] != 0:
        raise ValueError('zero state endpoints')
    meter.live(200000 + 4 * len(signed))
    return signed, absolute


def moments(state, scales, meter):
    signed, absolute = _state(state, meter)
    if type(scales) is not list or len(scales) > len(signed):
        raise ValueError('bounded scale list')
    seen, result = [], []
    for X in scales:
        meter.charge(len(seen) + 1); V._integer(X, 1, MAX_HORIZON)
        if X in seen or 2 * X > len(signed):
            raise ValueError('distinct complete moment blocks')
        seen.append(X)
        total = magnitude = 0
        for n in range(X, 2 * X):
            meter.charge()
            total = V._small(total + V._small(signed[n] * signed[n], meter), meter)
            magnitude = V._small(magnitude + V._small(absolute[n] * absolute[n], meter), meter)
        result.append(dict(X=X, energy=str(meter.number(Q(total, X * X))),
                           absolute_energy=str(meter.number(Q(magnitude, X * X)))))
    return result


def initial_cost(state, meter):
    signed, _ = _state(state, meter)
    if len(signed) < 32:
        raise ValueError('complete initial interval 1..31')
    total = Q(0)
    for n in range(1, 32):
        total = meter.number(total + Q(meter.number(signed[n] * signed[n]), n * n))
    return str(total)


def decomposition(program, values, state, scales, meter):
    """Retain the complete fresh block, lower block, and signed cross energies."""
    validate(program, meter); _values(values, meter)
    signed, _ = _state(state, meter)
    if len(signed) != len(values) or type(scales) is not list:
        raise ValueError('same complete source/output and explicit scales')
    seen = []
    for X in scales:
        meter.charge(len(seen) + 1); V._integer(X, 1, MAX_HORIZON)
        if X & (X - 1) or X in seen or 2 * X > len(signed):
            raise ValueError('distinct complete dyadic decomposition blocks')
        seen.append(X)
    diagonal_word = {'stages': [deepcopy(s) for s in program['stages'] if s['op'] != 'convolve']}
    meter.charge(len(program['stages']))
    diagonal = evaluate(diagonal_word, values, meter)['signed']
    # The already retained full output and source are additional live vectors.
    meter.live(200000 + 24 * len(values))
    result = []
    for X in scales:
        fresh = lower = mixed = total = 0
        for n in range(X, 2 * X):
            meter.charge()
            a = diagonal[n]
            b = V._small(signed[n] - a, meter)
            fresh = V._small(fresh + V._small(a * a, meter), meter)
            lower = V._small(lower + V._small(b * b, meter), meter)
            mixed = V._small(mixed + V._small(2 * a * b, meter), meter)
            total = V._small(total + V._small(signed[n] * signed[n], meter), meter)
        if meter.number(fresh + lower + mixed) != total:
            raise ArithmeticError('complete block energy identity')
        result.append(dict(X=X, diagonal_energy=str(meter.number(Q(fresh, X * X))),
                           lower_energy=str(meter.number(Q(lower, X * X))),
                           mixed_energy=str(meter.number(Q(mixed, X * X))),
                           total_energy=str(meter.number(Q(total, X * X)))))
    return result
