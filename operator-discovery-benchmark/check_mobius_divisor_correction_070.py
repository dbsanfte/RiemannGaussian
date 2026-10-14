"""Independent exact checker for finite local divisor polynomial corrections.

No optimizer, producer, historical checker, floating proof arithmetic, or supplied
Mobius values are used.  The last evaluator independently sieves ordinary mu.
"""
from fractions import Fraction
import math
import time

SCHEMA = 'mobius-divisor-correction-v1'
GRID = 1 << 20
MAX_TERMS = 2_000_000
MAX_BYTES = 2 * 1024 ** 3
MAX_POWER_BITS = 100_000


class Meter:
    def __init__(self, limit=300_000_000_000, seconds=7200):
        self.limit = limit
        self.seconds = seconds
        self.operations = 0
        self.started = time.monotonic()

    def charge(self, count=1):
        if type(count) is not int or count < 0:
            raise ValueError('invalid work charge')
        self.operations += count
        if self.operations > self.limit:
            raise ValueError('checker work limit exceeded')
        if time.monotonic() - self.started > self.seconds:
            raise ValueError('checker time limit exceeded')

    add = charge


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _keys(obj, names, label):
    _require(type(obj) is dict and set(obj) == set(names.split()), label + ' keys')


def _integer(x, lo=None, hi=None, bits=4096):
    _require(type(x) is int, 'integer required')
    _require(x.bit_length() <= bits, 'integer bit limit')
    _require(lo is None or x >= lo, 'integer below range')
    _require(hi is None or x <= hi, 'integer above range')
    return x


def _decimal(value):
    if value.bit_length() < 12_000:
        return str(value)
    sign = '-' if value < 0 else ''
    value = abs(value)
    chunks = []
    while value:
        value, chunk = divmod(value, 1_000_000_000)
        chunks.append(chunk)
    return sign + str(chunks[-1]) + ''.join(f'{c:09d}' for c in reversed(chunks[:-1]))


def rational_text(value):
    value = Fraction(value)
    return _decimal(value.numerator) if value.denominator == 1 else _decimal(value.numerator) + '/' + _decimal(value.denominator)


def _rational(value):
    _require(type(value) is str and 0 < len(value) <= 61_000, 'rational string required')
    parts = value.split('/')
    _require(len(parts) <= 2 and all(p and (p.isascii()) for p in parts), 'rational syntax')
    _require(all(p.lstrip('-').isdigit() for p in parts), 'rational syntax')
    # Avoid Python decimal parsing limits without changing process-wide settings.
    def parse(p):
        sign = -1 if p.startswith('-') else 1
        p = p.lstrip('-')
        _require(len(p) <= 30_104, 'rational integer capacity')
        n = 0
        for start in range(0, len(p), 9):
            part = p[start:start + 9]
            n = n * 10 ** len(part) + int(part)
        _require(n.bit_length() <= MAX_POWER_BITS, 'rational integer bit limit')
        return sign * n
    a = parse(parts[0])
    b = parse(parts[1]) if len(parts) == 2 else 1
    _require(b > 0, 'positive rational denominator required')
    result = Fraction(a, b)
    _require(value == rational_text(result), 'noncanonical rational')
    return result


def _monomial(indices, degree, radius):
    _require(type(indices) is list and len(indices) <= degree, 'monomial list/degree')
    result = tuple(_integer(s, 2, radius) for s in indices)
    _require(tuple(sorted(result)) == result, 'monomial not sorted')
    return result


def _capacity(count, bits=4096, term_limit=True):
    _require(not term_limit or count <= MAX_TERMS, 'term capacity exceeded')
    # Conservatively includes Python dict/list/tuple/int objects and temporaries.
    _require(count * (1024 + (bits + 7) // 8) <= MAX_BYTES, 'checker memory capacity exceeded')


def _polynomial(entries, degree, radius, meter, bits=4096):
    _require(type(entries) is list, 'polynomial list required')
    _capacity(len(entries), bits)
    result = {}
    previous = None
    for entry in entries:
        meter.charge(10 + degree)
        _keys(entry, 'indices numerator', 'polynomial term')
        key = _monomial(entry['indices'], degree, radius)
        coefficient = _integer(entry['numerator'], bits=bits)
        _require(coefficient != 0, 'zero sparse coefficient')
        _require(previous is None or previous < key, 'polynomial ordering or duplicate')
        previous = key
        result[key] = coefficient
    return result


def _metadata(value, meter, depth=0, state=None):
    if state is None:
        state = [0, 0]
    state[0] += 1
    meter.charge()
    _require(depth <= 16 and state[0] <= 10_000, 'metadata complexity')
    if type(value) is dict:
        for key, item in value.items():
            _require(type(key) is str, 'metadata key type')
            state[1] += len(key)
            meter.charge(len(key))
            _metadata(item, meter, depth + 1, state)
    elif type(value) is list:
        for item in value:
            _metadata(item, meter, depth + 1, state)
    elif type(value) is str:
        state[1] += len(value)
        meter.charge(len(value))
    elif type(value) is int:
        _integer(value)
    elif type(value) is float:
        _require(math.isfinite(value), 'metadata nonfinite float')
    else:
        _require(value is None or type(value) is bool, 'metadata not JSON')
    _require(state[1] <= 100_000, 'metadata text capacity')


def _constraint(n, multiplier, meter):
    # Enumerating divisors independently avoids trusting producer supports.
    divisors = []
    for d in range(1, math.isqrt(n) + 1):
        meter.charge(2)
        if n % d == 0:
            divisors.append(d)
            if d * d != n:
                divisors.append(n // d)
    result = {}
    def add(indices, c):
        key = tuple(sorted(multiplier + indices))
        result[key] = result.get(key, 0) + c
    if n % 2:
        add((), 1)
    for d in divisors:
        if d >= 2:
            add((d,), 1)
        if d >= 3:
            add((d - 1,), -1)
        meter.charge(4 + len(multiplier))
    return {key: value for key, value in result.items() if value}


def _weight(key):
    return math.prod(key)


def _upper(poly, denominator, meter):
    total = 0
    for key, c in poly.items():
        meter.charge(5 + len(key) + c.bit_length())
        total += abs(c) * _weight(key)
    return Fraction(total, GRID * denominator)


def _power(base, exponent, meter):
    if exponent == 0 or base <= 1:
        meter.charge()
        return 1 if exponent == 0 else base
    estimate = base.bit_length() * exponent
    _require(estimate <= MAX_POWER_BITS, 'integer power intermediary capacity')
    meter.charge(estimate * max(1, exponent.bit_length()))
    return pow(base, exponent)


def _ceil_weight(weight, sigma, meter):
    if weight == 1 or sigma == 0:
        return GRID
    if sigma == 1:
        return weight * GRID
    a, b = sigma.numerator, sigma.denominator
    # No floats: ceil((weight**sigma)*GRID) is an integer b-th root.
    estimate = weight.bit_length() * a + GRID.bit_length() * b
    _require(estimate <= MAX_POWER_BITS, 'price integer power intermediary capacity')
    target = _power(weight, a, meter) * _power(GRID, b, meter)
    _require(target.bit_length() <= MAX_POWER_BITS, 'price power bit limit')
    lo, hi = GRID, weight * GRID
    while lo < hi:
        middle = (lo + hi) // 2
        # For large candidates whose powers exceed the exact bit budget,
        # comparison can be settled by bit lower bounds, without constructing.
        if (middle.bit_length() - 1) * b >= target.bit_length():
            hi = middle
            meter.charge(2)
        elif _power(middle, b, meter) >= target:
            hi = middle
        else:
            lo = middle + 1
    return lo


def _prices(poly, exponents, degree, denominator, meter):
    rows = []
    for text, sigma in exponents:
        coefficients = [0] * (degree + 1)
        for indices, numerator in poly.items():
            meter.charge(5 + len(indices) + numerator.bit_length())
            coefficients[len(indices)] += abs(numerator) * _ceil_weight(_weight(indices), sigma, meter)
        rows.append({'sigma': text, 'coefficients': [rational_text(Fraction(c, GRID * GRID * denominator)) for c in coefficients]})
    return rows


def _prefixes(radius, meter):
    # Linear sieve; ordinary Mobius is introduced only in this final evaluator.
    smallest = [0] * (radius + 1)
    mu = [0] * (radius + 1)
    primes = []
    mu[1] = 1
    for n in range(2, radius + 1):
        meter.charge(3)
        if not smallest[n]:
            smallest[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            meter.charge(5)
            product = n * p
            if product > radius:
                break
            smallest[product] = p
            if n % p == 0:
                mu[product] = 0
                break
            mu[product] = -mu[n]
    prefix = [0] * (radius + 1)
    for n in range(1, radius + 1):
        meter.charge()
        prefix[n] = prefix[n - 1] + mu[n]
    return prefix


def _evaluate(poly, prefix, denominator, meter):
    result = 0
    for key, numerator in poly.items():
        product = numerator
        for index in key:
            meter.charge(2 + product.bit_length())
            product *= prefix[index]
        result += product
        meter.charge(2 + product.bit_length())
    return Fraction(result, denominator)


def verify_correction(cert, meter=None):
    meter = Meter() if meter is None else meter
    meter.charge()
    _keys(cert, 'schema input constraint_radius coefficient_grid price_exponents options baseline_unconditional_bound rounds selected_round selected_polynomial selected_conditional_prices used_constraints full_divisor_system_used constant_only_selected scalar_fake conditional_prefix_bounds_paid uniform_head_bound_proved RH_proved learner_mobius_signs_accessed', 'certificate')
    _require(cert['schema'] == SCHEMA, 'schema mismatch')
    _require(type(cert['coefficient_grid']) is int and cert['coefficient_grid'] == GRID, 'coefficient grid mismatch')
    for flag in ('conditional_prefix_bounds_paid', 'uniform_head_bound_proved', 'RH_proved', 'learner_mobius_signs_accessed'):
        _require(cert[flag] is False, 'unsupported proof/access flag')
    source = cert['input']
    _keys(source, 'degree U denominator polynomial', 'input')
    degree = _integer(source['degree'], 2, 8)
    radius = _integer(source['U'], 1, 131_072)
    denominator = _integer(source['denominator'], 1, 1_000_000)
    constraint_radius = _integer(cert['constraint_radius'], radius, 131_072)
    polynomial = _polynomial(source['polynomial'], degree, radius, meter)
    _require(type(cert['options']) is dict, 'options dictionary required')
    _metadata(cert['options'], meter)
    exponent_rows = cert['price_exponents']
    _require(type(exponent_rows) is list and len(exponent_rows) <= 32, 'exponent count')
    exponents = [(text, _rational(text)) for text in exponent_rows]
    _require(len(set(exponent_rows)) == len(exponent_rows), 'duplicate exponent')
    _require(all(0 <= sigma <= 1 for _, sigma in exponents), 'exponent range')
    baseline = {key: GRID * coefficient for key, coefficient in polynomial.items()}
    baseline_upper = _upper(baseline, denominator, meter)
    _require(_rational(cert['baseline_unconditional_bound']) == baseline_upper, 'baseline bound mismatch')
    rounds = cert['rounds']
    _require(type(rounds) is list and len(rounds) <= 8, 'round count')
    total_sparse_terms = len(source['polynomial'])
    for row in rounds:
        _require(type(row) is dict, 'round dictionary required')
        for name in ('residual', 'dual'):
            _require(type(row.get(name)) is list, 'round sparse list required')
            _require(len(row[name]) <= MAX_TERMS, 'round term limit')
            total_sparse_terms += len(row[name])
    _require(type(cert['selected_polynomial']) is list, 'selected polynomial list required')
    total_sparse_terms += len(cert['selected_polynomial'])
    _capacity(total_sparse_terms * 2 + len(polynomial) * 2, 4132, term_limit=False)
    candidates = [(baseline_upper, 0, -1, baseline, [])]
    for number, row in enumerate(rounds):
        _keys(row, 'columns lambda_numerators residual dual box primal_upper boxed_lower gap solver search', 'round')
        box = _integer(row['box'], 1)
        _metadata(row['solver'], meter)
        _metadata(row['search'], meter)
        columns = row['columns']
        lambdas = row['lambda_numerators']
        _require(type(columns) is list and len(columns) <= 256, 'column count')
        _require(type(lambdas) is list and len(lambdas) == len(columns), 'lambda alignment')
        accumulated = dict(baseline)
        union = set(polynomial)
        seen = set()
        expanded = []
        used = []
        # Account for simultaneous source, residual, union, dual and expansions.
        _capacity(len(polynomial) * 5, 4116, term_limit=False)
        for column, numerator in zip(columns, lambdas):
            _keys(column, 'n multiplier_indices', 'column')
            n = _integer(column['n'], 2, constraint_radius)
            multiplier = _monomial(column['multiplier_indices'], degree - 1, constraint_radius)
            _require((n, multiplier) not in seen, 'duplicate column')
            seen.add((n, multiplier))
            numerator = _integer(numerator, -box * GRID, box * GRID, bits=4116)
            support = _constraint(n, multiplier, meter)
            expanded.append(support)
            union.update(support)
            _require(len(union) <= MAX_TERMS, 'union term limit')
            _capacity(total_sparse_terms * 2 + len(polynomial) * 2 + len(union) * 3 + sum(len(item) for item in expanded), 4132, term_limit=False)
            if numerator:
                used.append(n)
                for key, value in support.items():
                    meter.charge(5 + numerator.bit_length())
                    accumulated[key] = accumulated.get(key, 0) + numerator * value
        accumulated = {key: value for key, value in accumulated.items() if value}
        residual = _polynomial(row['residual'], degree, constraint_radius, meter, bits=4132)
        _require(residual == accumulated, 'residual coefficient identity mismatch')
        dual = _polynomial(row['dual'], degree, constraint_radius, meter, bits=4096)
        _require(set(dual) <= union, 'dual monomial outside full support union')
        for key, z in dual.items():
            meter.charge(5 + len(key))
            _require(abs(z) <= GRID * _weight(key), 'dual feasibility bound')
        upper = _upper(residual, denominator, meter)
        pairing = sum(dual.get(key, 0) * coefficient for key, coefficient in polynomial.items())
        meter.charge(len(polynomial) * 5)
        penalty = 0
        for support in expanded:
            penalty += abs(sum(dual.get(key, 0) * coefficient for key, coefficient in support.items()))
            meter.charge(5 * len(support))
        lower = Fraction(pairing - box * penalty, GRID * denominator)
        _require(_rational(row['primal_upper']) == upper, 'primal upper mismatch')
        _require(_rational(row['boxed_lower']) == lower, 'boxed lower mismatch')
        _require(_rational(row['gap']) == upper - lower and lower <= upper, 'duality gap mismatch')
        candidates.append((upper, sum(n != 0 for n in lambdas), number, residual, sorted(set(used))))
    best = min(candidates, key=lambda item: item[:3])
    upper, _, selected_index, selected, used = best
    _require(_integer(cert['selected_round'], -1, len(rounds) - 1) == selected_index, 'selected round mismatch')
    supplied_selected = _polynomial(cert['selected_polynomial'], degree, constraint_radius, meter, bits=4132)
    _require(supplied_selected == selected, 'selected polynomial mismatch')
    _require(cert['selected_conditional_prices'] == _prices(selected, exponents, degree, denominator, meter), 'conditional prices mismatch')
    _require(type(cert['used_constraints']) is list and all(type(n) is int for n in cert['used_constraints']) and cert['used_constraints'] == used, 'used constraints mismatch')
    _require(type(cert['full_divisor_system_used']) is bool and cert['full_divisor_system_used'] == (used == list(range(2, constraint_radius + 1))), 'full divisor-system flag mismatch')
    _require(type(cert['constant_only_selected']) is bool and cert['constant_only_selected'] == all(not key for key in selected), 'constant-only flag mismatch')
    fake = cert['scalar_fake']
    _keys(fake, 'source_value corrected_value violated_used_constraints actual_mobius_assignment', 'scalar fake')
    _require(_rational(fake['source_value']) == Fraction(polynomial.get((), 0), denominator), 'fake source mismatch')
    _require(_rational(fake['corrected_value']) == Fraction(selected.get((), 0), GRID * denominator), 'fake correction mismatch')
    _require(type(fake['violated_used_constraints']) is list and all(type(n) is int for n in fake['violated_used_constraints']) and fake['violated_used_constraints'] == [n for n in used if n % 2], 'fake violations mismatch')
    _require(fake['actual_mobius_assignment'] is False, 'fake global Mobius claim')
    prefix = _prefixes(constraint_radius, meter)
    actual = _evaluate(polynomial, prefix, denominator, meter)
    corrected = _evaluate(selected, prefix, GRID * denominator, meter)
    _require(actual == corrected, 'actual polynomial identity failed')
    _require(abs(actual) <= upper, 'unconditional price failed actual evaluation')
    premises = []
    for exponent_number, (_, sigma) in enumerate(exponents):
        holds = True
        for s in range(1, constraint_radius + 1):
            if _power(abs(prefix[s]), sigma.denominator, meter) > _power(s, sigma.numerator, meter):
                holds = False
                break
        premises.append(holds)
        if holds:
            value = sum(_rational(c) for c in cert['selected_conditional_prices'][exponent_number]['coefficients'])
            _require(abs(actual) <= value, 'conditional price fails satisfied finite premise')
    return {'verified': True, 'source_actual_value': rational_text(actual), 'selected_actual_value': rational_text(corrected), 'selected_upper': rational_text(upper), 'finite_C1_prefix_premises': premises, 'conditional_prefix_bounds_paid': False, 'original_source_binding_proved': False, 'uniform_head_bound_proved': False, 'RH_proved': False, 'work': meter.operations}
