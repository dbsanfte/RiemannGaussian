"""Independent exact divisor-circuit evaluation and recovery admission.

Kernels are reconstructed from prime factorizations, and each convolution
enumerates divisors of its output index. No producer arithmetic is imported.
Recovery admission certifies the restricted uniform inverse norm theorem,
not a source-specific transformed-moment estimate.
"""
from fractions import Fraction as Q
from math import gcd, isqrt

from potential_candidate_language import Meter


MAX_HORIZON = 131071
SCHEMA = 'reversible-divisor-circuit-v1'
DOMAIN = 'discrete_weighted_l2_sigma_gt_half'
BOUND = '(1+1/epsilon)^recovery_power'
BINDING = 'same_fixed_source_in_all_stages_and_inverse'


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _alpha(text, meter):
    meter.charge()
    _require(type(text) is str and 0 < len(text) <= 16
             and all(c in '-0123456789/' for c in text), 'canonical bounded alpha')
    parts = text.split('/')
    _require(len(parts) <= 2 and all(p and p != '-' for p in parts), 'alpha integer components')
    try:
        integers = [int(p) for p in parts]
    except ValueError as error:
        raise ValueError('alpha integer syntax') from error
    _require(len(integers) == 1 or integers[1] > 0, 'positive alpha denominator')
    for integer in integers:
        meter.number(integer)
    value = meter.number(Q(*integers))
    _require(str(value) == text and value != 0 and abs(value) <= 2 and value.denominator <= 6,
             'nonzero canonical alpha within circuit policy')
    return value


def _phase_syntax(phase, meter):
    nodes = 0

    def node(tree, depth, index=False):
        nonlocal nodes
        meter.charge()
        nodes += 1
        _require(nodes <= 31 and depth <= 6, 'bounded phase/index syntax')
        _require(type(tree) is list and tree and type(tree[0]) is str, 'explicit phase/index node')
        op = tree[0]
        if index:
            if op == 'n':
                _require(len(tree) == 1, 'n index arity')
            elif op in ('root', 'subtract_root'):
                _require(len(tree) == 3 and type(tree[1]) is int and type(tree[2]) is int
                         and 1 <= tree[1] <= tree[2] <= 6 and gcd(tree[1], tree[2]) == 1,
                         'reduced positive root exponent at most one')
                meter.number(tree[1]); meter.number(tree[2])
            elif op in ('quotient', 'remainder'):
                _require(len(tree) == 2 and type(tree[1]) is int and 2 <= tree[1] <= 16,
                         'bounded index modulus')
                meter.number(tree[1])
            else:
                raise ValueError('unsupported source index')
        elif op == 'constant':
            _require(len(tree) == 2 and type(tree[1]) is int and tree[1] in (-1, 1),
                     'strict unit phase')
            meter.number(tree[1])
        elif op in ('parity', 'source_sign'):
            _require(len(tree) == 2, 'unary phase arity')
            node(tree[1], depth + 1, True)
        elif op == 'residue_sign':
            _require(len(tree) == 4 and type(tree[2]) is int and 2 <= tree[2] <= 16
                     and type(tree[3]) is list and len(tree[3]) <= tree[2], 'residue phase schema')
            node(tree[1], depth + 1, True)
            meter.number(tree[2])
            previous = -1
            for residue in tree[3]:
                meter.charge()
                _require(type(residue) is int and previous < residue < tree[2],
                         'strictly increasing valid residues')
                meter.number(residue)
                previous = residue
        elif op == 'multiply':
            _require(len(tree) == 3, 'binary phase arity')
            node(tree[1], depth + 1); node(tree[2], depth + 1)
        else:
            raise ValueError('unsupported unit phase')

    node(phase, 0)
    return nodes


def _program(program, meter):
    meter.charge()
    _require(type(program) is dict and set(program) == {'stages'}
             and type(program['stages']) is list and len(program['stages']) <= 5,
             'explicit bounded circuit stages')
    parsed = []
    convolutions = signs = 0
    for stage in program['stages']:
        meter.charge()
        _require(type(stage) is dict and type(stage.get('op')) is str, 'explicit stage object')
        if stage.get('op') == 'convolve':
            _require(set(stage) == {'op', 'alpha', 'prime_phase'}, 'convolution exact keys')
            alpha = _alpha(stage['alpha'], meter)
            _phase_syntax(stage['prime_phase'], meter)
            convolutions += 1
            parsed.append(('convolve', alpha, stage['prime_phase']))
        elif stage.get('op') == 'sign':
            _require(set(stage) == {'op', 'phase'}, 'sign exact keys')
            _phase_syntax(stage['phase'], meter)
            signs += 1
            parsed.append(('sign', None, stage['phase']))
        else:
            raise ValueError('supported circuit stage')
    _require(convolutions <= 3 and signs <= 2, 'bounded stage types')
    meter.live(16384)
    return parsed


def validate(program, meter):
    _program(program, meter)
    return True


def verify(certificate, meter=None):
    meter = Meter(2000000) if meter is None else meter
    meter.charge()
    _require(type(certificate) is dict and set(certificate) == {
        'schema', 'program', 'convolution_orders', 'recovery_power', 'domain',
        'bound', 'coefficient_binding'}, 'recovery certificate exact keys')
    parsed = _program(certificate['program'], meter)
    orders = [(abs(alpha.numerator) + alpha.denominator - 1) // alpha.denominator
              for op, alpha, _ in parsed if op == 'convolve']
    recorded = certificate['convolution_orders']
    _require(type(recorded) is list and len(recorded) == len(orders)
             and all(type(a) is int and a == b for a, b in zip(recorded, orders)),
             'full convolution recovery orders')
    _require(type(certificate['recovery_power']) is int
             and certificate['recovery_power'] == sum(orders), 'summed unsquared recovery power')
    _require(all(type(certificate[key]) is str for key in ('schema', 'domain', 'bound', 'coefficient_binding'))
             and certificate['schema'] == SCHEMA and certificate['domain'] == DOMAIN
             and certificate['bound'] == BOUND and certificate['coefficient_binding'] == BINDING,
             'uniform recovery theorem and fixed source binding')
    meter.charge(len(orders) + 8)
    return True


def _horizon(horizon, meter):
    meter.charge()
    _require(type(horizon) is int and 1 <= horizon <= MAX_HORIZON, 'bounded positive source horizon')
    meter.number(horizon)


def _spf(horizon, meter, resident):
    """Independent Eratosthenes smallest-prime table, not divisor inversion."""
    meter.charge(horizon + 1)
    meter.live(resident + horizon + 1)
    table = [0] * (horizon + 1)
    for n in range(2, horizon + 1):
        meter.charge()
        if table[n]:
            continue
        table[n] = n
        if n <= isqrt(horizon):
            for multiple in range(n * n, horizon + 1, n):
                meter.charge()
                if not table[multiple]:
                    table[multiple] = n
    return table


def _factor(n, table, meter):
    answer = []
    while n > 1:
        meter.charge(2)
        prime = table[n]
        exponent = 0
        while True:
            meter.charge()
            if n % prime:
                break
            meter.charge(2)
            n //= prime
            exponent += 1
        answer.append((prime, exponent))
        meter.charge()
    return answer


def source(name, horizon, meter):
    _horizon(horizon, meter)
    _require(type(name) is str and name in ('mu', 'one', 'partial_prime_13'), 'declared source name')
    meter.charge(horizon + 1)
    meter.live(2 * (horizon + 1) + 128)
    values = [0] * (horizon + 1)
    if name == 'one':
        meter.charge(horizon)
        values[1:] = [1] * horizon
        return values
    table = _spf(horizon, meter, horizon + 1)
    for n in range(1, horizon + 1):
        factors = _factor(n, table, meter)
        meter.charge(len(factors) + 1)
        if any(exponent >= 2 for _, exponent in factors):
            value = 0
        elif name == 'mu':
            value = -1 if len(factors) % 2 else 1
        else:
            value = -1 if sum(prime <= 13 for prime, _ in factors) % 2 else 1
        values[n] = value
    return values


def _values(values, meter):
    _require(type(values) is list and 2 <= len(values) <= MAX_HORIZON + 1, 'complete positive source vector')
    meter.charge(len(values))
    _require(type(values[0]) is int and values[0] == 0
             and all(type(value) is int and value in (-1, 0, 1) for value in values),
             'fixed integer source coefficients with index zero')
    meter.number(len(values) - 1)
    meter.live(len(values) + 16384)
    return len(values) - 1


def _power(n, exponent, meter):
    if n in (0, 1) or exponent == 1:
        meter.charge()
        return meter.number(n)
    work = exponent * n.bit_length()
    if work > meter.max_bits:
        raise OverflowError('root temporary bit preflight')
    meter.charge(work)
    return meter.number(n ** exponent)


class _RootMaps:
    """Lazy monotone maps shared by root/subtract-root in ALL circuit stages."""
    def __init__(self, horizon, meter, resident):
        self.horizon = horizon
        self.meter = meter
        self.resident = resident
        self.maps = {}
        self.cells = 0

    def live(self, extra=0):
        self.meter.live(self.resident + self.cells + 128 * len(self.maps) + extra)

    def root(self, n, a, b):
        self.meter.charge()
        _require(0 <= n <= self.horizon, 'root map within complete source horizon')
        key = (a, b)
        if key not in self.maps:
            self.meter.charge()
            self.maps[key] = [[0], 1]
            self.cells += 1
            self.live(256)
        roots, threshold = self.maps[key]
        needed = max(0, n + 1 - len(roots))
        if not needed:
            return roots[n]
        # Reserve the complete requested extension before target/threshold work.
        self.meter.charge(needed)
        self.cells += needed
        self.live(256)
        current = roots[-1]
        for value in range(len(roots), n + 1):
            target = _power(value, a, self.meter)
            self.meter.charge()
            # theta<=1 makes floor(value^theta) increase by at mostone. The
            # exact threshold loop also guards that fact without approximation.
            while target >= threshold:
                self.meter.charge(2)
                current += 1
                threshold = _power(current + 1, b, self.meter)
                self.meter.charge()
            roots.append(current)
        self.maps[key][1] = threshold
        return roots[n]


def _index(index, n, meter, roots):
    meter.charge()
    op = index[0]
    if op == 'n':
        value = n
    elif op in ('quotient', 'remainder'):
        value = n // index[1] if op == 'quotient' else n % index[1]
    else:
        a, b = index[1:]
        if a == b:
            root = n
        else:
            root = roots.root(n, a, b)
        value = root if op == 'root' else n - root
    _require(0 <= value <= n, 'source index in its exact phase domain')
    return meter.number(value)


def _phase(phase, n, values, meter, roots):
    meter.charge()
    op = phase[0]
    if op == 'constant':
        return phase[1]
    if op == 'multiply':
        return _phase(phase[1], n, values, meter, roots) * _phase(phase[2], n, values, meter, roots)
    index = _index(phase[1], n, meter, roots)
    if op == 'parity':
        return -1 if index % 2 else 1
    if op == 'source_sign':
        return -1 if values[index] < 0 else 1
    return -1 if index % phase[2] in phase[3] else 1


def _kernel(alpha, phase, horizon, values, table, meter, resident, roots):
    meter.charge(horizon + 1)
    roots.live(2 * (horizon + 1) + 256)
    kernel = [Q(0)] * (horizon + 1)
    kernel[1] = Q(1)
    rising = [Q(1)]
    for exponent in range(1, horizon.bit_length()):
        meter.charge(2)
        value = meter.number(rising[-1] * meter.number(alpha + exponent - 1))
        rising.append(meter.number(value / exponent))
    prime_signs = {}
    for n in range(2, horizon + 1):
        value = Q(1)
        factors = _factor(n, table, meter)
        for prime, exponent in factors:
            if prime not in prime_signs:
                prime_signs[prime] = _phase(phase, prime, values, meter, roots)
                meter.charge()
            meter.charge(2)
            sign = prime_signs[prime] if exponent % 2 else 1
            value = meter.number(value * rising[exponent] * sign)
        kernel[n] = value
    return kernel


def _divisors(n, table, meter):
    result = [1]
    for prime, exponent in _factor(n, table, meter):
        old = result
        meter.charge(len(old) * (exponent + 1))
        result = []
        power = 1
        for power_index in range(exponent + 1):
            for divisor in old:
                result.append(meter.number(divisor * power))
            if power_index < exponent:
                power = meter.number(power * prime)
    return result


def evaluate(program, values, meter):
    horizon = _values(values, meter)
    parsed = _program(program, meter)
    meter.charge(horizon + 1)
    current = [Q(0)]
    for value in values[1:]:
        current.append(meter.number(current[-1] + value))
    resident = 8 * (horizon + 1) + 16384
    meter.live(resident)
    roots = _RootMaps(horizon, meter, resident)
    table = _spf(horizon, meter, 3 * (horizon + 1) + 16384) if parsed else None
    for op, alpha, phase in parsed:
        if op == 'sign':
            for n in range(1, horizon + 1):
                current[n] = meter.number(current[n] * _phase(phase, n, values, meter, roots))
        else:
            kernel = _kernel(alpha, phase, horizon, values, table, meter, resident, roots)
            meter.charge(horizon + 1)
            output = [Q(0)] * (horizon + 1)
            for n in range(1, horizon + 1):
                divisors = _divisors(n, table, meter)
                roots.live(2 * len(divisors) + 256)
                total = Q(0)
                for divisor in divisors:
                    meter.charge(2)
                    term = meter.number(kernel[divisor] * current[n // divisor])
                    total = meter.number(total + term)
                output[n] = total
            current = output
            # Do not retain the previous kernel while constructing the next
            # stage; the resident base then covers simultaneous stage vectors.
            del kernel
    return current


def moments(output, scales, meter):
    _require(type(output) is list and 2 <= len(output) <= MAX_HORIZON + 1, 'complete output vector')
    _require(type(scales) is list and len(scales) <= len(output) - 1, 'bounded scale list')
    meter.charge(len(output) + len(scales))
    _require(type(output[0]) in (int, Q) and output[0] == 0
             and all(type(value) in (int, Q) for value in output), 'exact output with zero index')
    for value in output:
        meter.number(value)
    seen = set()
    for X in scales:
        _require(type(X) is int and X >= 1, 'positive strict block scale')
        meter.number(X)
        _require(X not in seen and 2 * X - 1 < len(output), 'distinct complete moment blocks')
        seen.add(X)
    meter.live(2 * len(output) + 8 * len(scales) + 16384)
    result = []
    for X in scales:
        total = Q(0)
        for n in range(X, 2 * X):
            meter.charge(2)
            square = meter.number(output[n] * output[n])
            total = meter.number(total + square)
        denominator = meter.number(X * X)
        result.append(dict(X=X, energy=str(meter.number(total / denominator))))
    return result
