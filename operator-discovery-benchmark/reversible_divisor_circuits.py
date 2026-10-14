"""Exact, uniformly reversible arithmetic circuits; no moment bound is assumed."""
from copy import deepcopy
from fractions import Fraction as Q
from math import gcd

from potential_candidate_language import Meter, mobius

MAX_HORIZON = 131071
SCHEMA = 'reversible-divisor-circuit-v1'


def rational(value, meter):
    meter.charge()
    if type(value) is not str or not value or len(value) > 2500:
        raise ValueError('bounded canonical rational string')
    parts = value.split('/')
    if len(parts) > 2 or any(not p or not p.lstrip('-').isdigit() for p in parts):
        raise ValueError('rational syntax')
    if any(len(p.lstrip('-')) > 1234 for p in parts):
        raise OverflowError('rational input bit cap')
    integers = [meter.number(int(p)) for p in parts]
    if len(integers) == 2 and integers[1] <= 0:
        raise ValueError('positive denominator')
    result = meter.number(Q(*integers))
    if str(result) != value:
        raise ValueError('reduced canonical rational')
    return result


def _integer(value, lo, hi):
    if type(value) is not int or not lo <= value <= hi:
        raise ValueError('strict bounded integer')


def validate(program, meter):
    meter.charge()
    if type(program) is not dict or set(program) != {'stages'}:
        raise ValueError('stages-only program')
    stages = program['stages']
    if type(stages) is not list or len(stages) > 5:
        raise ValueError('at most five circuit stages')

    def phase(tree):
        nodes = 0

        def walk(node, kind, depth=0):
            nonlocal nodes
            meter.charge(); nodes += 1
            if nodes > 31 or depth > 6:
                raise ValueError('phase node/depth bound')
            if type(node) is not list or not node or type(node[0]) is not str:
                raise ValueError('phase/index syntax')
            op = node[0]
            if kind == 'index':
                if op == 'n' and len(node) == 1:
                    return
                if op in ('root', 'subtract_root') and len(node) == 3:
                    a, b = node[1:]
                    _integer(a, 1, 6); _integer(b, 1, 6)
                    if a > b or gcd(a, b) != 1:
                        raise ValueError('reduced root exponent in (0,1]')
                    return
                if op in ('quotient', 'remainder') and len(node) == 2:
                    _integer(node[1], 2, 16); return
            elif op == 'constant' and len(node) == 2:
                _integer(node[1], -1, 1)
                if not node[1]:
                    raise ValueError('unit sign required')
                return
            elif op in ('parity', 'source_sign') and len(node) == 2:
                walk(node[1], 'index', depth + 1); return
            elif op == 'multiply' and len(node) == 3:
                walk(node[1], 'phase', depth + 1)
                walk(node[2], 'phase', depth + 1); return
            elif op == 'residue_sign' and len(node) == 4:
                walk(node[1], 'index', depth + 1)
                _integer(node[2], 2, 16)
                residues = node[3]
                if type(residues) is not list or len(residues) > node[2]:
                    raise ValueError('bounded residue list')
                for r in residues:
                    meter.charge(); _integer(r, 0, node[2] - 1)
                if residues != sorted(set(residues)):
                    raise ValueError('strict ordered residues')
                return
            raise ValueError('declared typed phase production')

        walk(tree, 'phase')

    convolutions = signs = 0
    orders = []
    for stage in stages:
        meter.charge()
        if type(stage) is not dict:
            raise ValueError('stage object')
        if stage.get('op') == 'convolve' and set(stage) == {'op', 'alpha', 'prime_phase'}:
            alpha = rational(stage['alpha'], meter)
            if not alpha or abs(alpha) > 2 or alpha.denominator > 6:
                raise ValueError('nonzero bounded fractional convolution order')
            phase(stage['prime_phase']); convolutions += 1
            orders.append((abs(alpha.numerator) + alpha.denominator - 1) // alpha.denominator)
        elif stage.get('op') == 'sign' and set(stage) == {'op', 'phase'}:
            phase(stage['phase']); signs += 1
        else:
            raise ValueError('exact convolution/sign stage schema')
    if convolutions > 3 or signs > 2:
        raise ValueError('at most three convolutions and two signs')
    return orders


def certificate(program, meter):
    orders = validate(program, meter)
    return dict(schema=SCHEMA, program=deepcopy(program), convolution_orders=orders,
                recovery_power=sum(orders), domain='discrete_weighted_l2_sigma_gt_half',
                bound='(1+1/epsilon)^recovery_power',
                coefficient_binding='same_fixed_source_in_all_stages_and_inverse')


def inverse(program, meter):
    validate(program, meter)
    result = deepcopy(program)
    result['stages'].reverse()
    for stage in result['stages']:
        if stage['op'] == 'convolve':
            stage['alpha'] = str(-rational(stage['alpha'], meter))
    return result


def root(n, a, b, meter):
    """Exact floor n**(a/b); also used for the cofinal test exponents."""
    if type(n) is not int or n < 0 or type(a) is not int or a < 1 or type(b) is not int or b < 1:
        raise ValueError('integer root domain')
    target = meter.number(n ** a)
    lo, hi = 0, 1 << ((target.bit_length() + b - 1) // b)
    while lo + 1 < hi:
        meter.charge()
        mid = (lo + hi) // 2
        if meter.number(mid ** b) <= target:
            lo = mid
        else:
            hi = mid
    return hi if meter.number(hi ** b) <= target else lo


def _index(tree, n, meter):
    meter.charge()
    op = tree[0]
    if op == 'n':
        return n
    if op in ('root', 'subtract_root'):
        r = root(n, tree[1], tree[2], meter)
        return r if op == 'root' else n - r
    if op == 'quotient':
        return n // tree[1]
    if op == 'remainder':
        return n % tree[1]
    raise ValueError('index operation')


def _phase(tree, n, values, meter):
    meter.charge()
    op = tree[0]
    if op == 'constant':
        return tree[1]
    if op == 'multiply':
        return _phase(tree[1], n, values, meter) * _phase(tree[2], n, values, meter)
    index = _index(tree[1], n, meter)
    if not 0 <= index <= n < len(values):
        raise ValueError('complete fixed-source phase domain')
    if op == 'parity':
        return -1 if index % 2 else 1
    if op == 'source_sign':
        return -1 if values[index] < 0 else 1
    if op == 'residue_sign':
        return -1 if index % tree[2] in tree[3] else 1
    raise ValueError('phase operation')


def source(name, H, meter):
    _integer(H, 1, MAX_HORIZON)
    if name not in ('mu', 'one', 'partial_prime_13'):
        raise ValueError('declared source')
    if name == 'one':
        meter.charge(H + 1); meter.live(2 * (H + 1))
        return [0] + [1] * H
    values = mobius(H, meter)
    if name == 'mu':
        return values
    result = [0] * (H + 1)
    meter.charge(H + 1); meter.live(3 * (H + 1))
    for n in range(1, H + 1):
        meter.charge()
        if values[n]:
            sign = 1
            for p in (2, 3, 5, 7, 11, 13):
                meter.charge()
                if n % p == 0:
                    sign = -sign
            result[n] = sign
    return result


def _small(value, meter):
    value = meter.number(value)
    return value.numerator if type(value) is Q and value.denominator == 1 else value


def _spf(H, meter):
    table = [0] * (H + 1)
    meter.charge(H + 1)
    for p in range(2, H + 1):
        meter.charge()
        if table[p]:
            continue
        table[p] = p
        for n in range(p * p, H + 1, p):
            meter.charge()
            if not table[n]:
                table[n] = p
    return table


def _kernel(stage, values, spf, meter):
    H = len(values) - 1
    alpha = rational(stage['alpha'], meter)
    rising = [1]
    for k in range(1, H.bit_length() + 1):
        rising.append(_small(rising[-1] * (alpha + k - 1) / k, meter))
    kernel = [0] * (H + 1); kernel[1] = 1
    signs = [0] * (H + 1)
    meter.charge(2 * (H + 1))
    for n in range(2, H + 1):
        meter.charge()
        p = spf[n]
        if not signs[p]:
            signs[p] = _phase(stage['prime_phase'], p, values, meter)
        t, k = n, 0
        while t % p == 0:
            meter.charge(); t //= p; k += 1
        local = rising[k] * (-1 if signs[p] == -1 and k % 2 else 1)
        kernel[n] = _small(kernel[t] * local, meter)
    return kernel


def _apply(program, values, data, meter):
    H = len(values) - 1
    spf = _spf(H, meter) if any(s['op'] == 'convolve' for s in program['stages']) else None
    for stage in program['stages']:
        meter.charge()
        if stage['op'] == 'sign':
            data = [_small(data[n] * _phase(stage['phase'], n, values, meter), meter)
                    if n else 0 for n in range(H + 1)]
            meter.charge(H + 1)
            continue
        kernel = _kernel(stage, values, spf, meter)
        output = [0] * (H + 1); meter.charge(H + 1)
        for d in range(1, H + 1):
            meter.charge()
            coefficient = kernel[d]
            if not coefficient:
                continue
            for k in range(1, H // d + 1):
                meter.charge()
                term = _small(coefficient * data[k], meter)
                output[d * k] = _small(output[d * k] + term, meter)
        data = output
    return data


def _validate_source(values, meter):
    if type(values) is not list or not 2 <= len(values) <= MAX_HORIZON + 1:
        raise ValueError('complete bounded positive-horizon source')
    if type(values[0]) is not int or values[0] != 0:
        raise ValueError('source zero endpoint')
    for value in values[1:]:
        meter.charge()
        if type(value) is not int or value not in (-1, 0, 1):
            raise ValueError('bounded signed source')


def evaluate(program, values, meter):
    validate(program, meter); _validate_source(values, meter)
    # Includes metadata, source, prefix, SPF, local kernels, sign tables and both
    # input/output vectors. Arithmetic scalar bit lengths are checked separately.
    meter.live(200000 + 12 * len(values))
    data = [0]
    for value in values[1:]:
        data.append(_small(data[-1] + value, meter))
    return _apply(program, values, data, meter)


def apply_to_state(program, values, data, meter):
    """Synthetic inverse verification, with exactly the same frozen source phases."""
    validate(program, meter); _validate_source(values, meter)
    if type(data) is not list or len(data) != len(values) or data[0] != 0:
        raise ValueError('full zero-padded state')
    for value in data:
        meter.number(value)
    meter.live(200000 + 12 * len(values))
    return _apply(program, values, list(data), meter)


def moments(output, scales, meter):
    if type(scales) is not list or len(scales) != len(set(scales)):
        raise ValueError('distinct scale list')
    if type(output) is not list or len(output) < 2 or output[0] != 0:
        raise ValueError('complete state')
    result = []
    for X in scales:
        _integer(X, 1, MAX_HORIZON)
        if 2 * X > len(output):
            raise ValueError('full moment interval required')
        total = 0
        for value in output[X:2 * X]:
            meter.charge()
            total = _small(total + _small(value * value, meter), meter)
        energy = _small(Q(total, X * X), meter)
        result.append(dict(X=X, energy=str(energy)))
    return result


def initial_cost(output, meter, threshold=32):
    if len(output) < threshold:
        raise ValueError('complete initial interval')
    total = Q(0)
    for n in range(1, threshold):
        total = _small(total + Q(_small(output[n] * output[n], meter), n * n), meter)
    return str(total)
