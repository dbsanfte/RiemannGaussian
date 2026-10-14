"""Independent exact local prime-adjunction tensor and support-bound audit.

These are component identities conditional on coprime/distinct index domains.
No whole signed moment estimate or independently varying source signs follows.
"""
from fractions import Fraction

MAX_TERMS = 256
SOURCES = ('B', 'au', 'av')


def validate(program):
    if type(program) is not dict or set(program) != {'binding', 'terms'}:
        raise ValueError('exact binding/terms program')
    binding = program['binding']
    if type(binding) is not str or binding not in ('same_prime', 'distinct_primes'):
        raise ValueError('reviewed prime binding required')
    dimensions = 1 if binding == 'same_prime' else 2
    terms = program['terms']
    if type(terms) is not list or not 1 <= len(terms) <= MAX_TERMS:
        raise ValueError('bounded nonempty term list')
    for term in terms:
        if type(term) is not dict or set(term) != {'coefficient', 'left', 'right'}:
            raise ValueError('exact term schema')
        c = term['coefficient']
        if type(c) is not int or c == 0 or abs(c) > 2:
            raise ValueError('nonzero bounded integer coefficient')
        for side in ('left', 'right'):
            vector = term[side]
            if type(vector) is not list or len(vector) != dimensions or any(type(e) is not int or not 0 <= e <= 6 for e in vector):
                raise ValueError('one exponent per free prime, integers0..6')
        if sum(term['left']) + sum(term['right']) > 6:
            raise ValueError('total adjunction exponent<=6')
    return binding, dimensions, terms


def _add(target, source, scalar, meter):
    for exponent, coefficient in source.items():
        meter.charge(3)
        value = target.get(exponent, 0) + scalar * coefficient
        if value: target[exponent] = value
        elif exponent in target: del target[exponent]
    return target


def _multiply(left, right, meter):
    result = {}
    for a, c in left.items():
        for b, d in right.items():
            meter.charge(len(a) + 3)
            exponent = tuple(x + y for x, y in zip(a, b))
            value = result.get(exponent, 0) + c * d
            if value: result[exponent] = value
            elif exponent in result: del result[exponent]
    return result


def _atom(label, exponent, axis, dimensions, meter):
    zero = (0,) * dimensions
    if exponent == 0: meter.charge(); return {zero: 1}
    if label in (1, 2):
        degree = exponent if label == 1 else 2 * exponent
        previous = exponent - 1 if label == 1 else 2 * exponent - 2
        top = list(zero); bottom = list(zero); top[axis] = degree; bottom[axis] = previous
        meter.charge(2 * dimensions + 2)
        return {tuple(top): 1, tuple(bottom): -1}
    # Literal prime-power convolution, rather than powers of the prime row.
    result = {}
    for j in range(exponent + 1):
        _add(result, _multiply(_atom(1, j, axis, dimensions, meter),
                               _atom(2, exponent - j, axis, dimensions, meter), meter), 1, meter)
    return result


def expand(program, meter):
    _, dimensions, terms = validate(program)
    meter.live(65536 + 16 * len(terms))
    components = [{} for _ in range(9)]
    cache = {}
    for term in terms:
        for i in range(3):
            for j in range(3):
                value = {(0,) * dimensions: 1}
                for axis in range(dimensions):
                    for label, exponent in ((i, term['left'][axis]), (j, term['right'][axis])):
                        key = (label, exponent, axis)
                        if key not in cache: cache[key] = _atom(label, exponent, axis, dimensions, meter)
                        value = _multiply(value, cache[key], meter)
                _add(components[3 * i + j], value, term['coefficient'], meter)
    result = []
    for component in components:
        meter.charge(len(component))
        result.append([[list(exponent), coefficient] for exponent, coefficient in sorted(component.items())])
    return result


def facts(program, meter):
    binding, dimensions, _ = validate(program)
    multipliers = expand(program, meter)
    valuations = []; norms = []
    for component in multipliers:
        meter.charge((dimensions + 1) * len(component))
        valuations.append([min(exponent[axis] for exponent, _ in component) for axis in range(dimensions)] if component else None)
        norms.append(sum(abs(coefficient) for _, coefficient in component))
    nonzero = [v for v in valuations if v is not None]
    common = [min(v[axis] for v in nonzero) for axis in range(dimensions)] if nonzero else None
    meter.charge(dimensions * len(nonzero))
    return dict(multipliers=multipliers, component_valuations=valuations,
                component_l1=norms, common_valuations=common,
                free_prime_count=dimensions, binding=binding,
                whole_signed_bound_proved=False)


def _rational(text):
    if type(text) is not str or len(text) > 32:
        raise ValueError('bounded canonical rational string')
    try: value = Fraction(text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational text') from error
    if str(value) != text: raise ValueError('canonical rational text')
    return value


def support_bound(binding, weights, theta_text, meter):
    """Conditional absolute support-count exponent, with all log costs retained.

Weights refer to independent FREE prime indices, never the number of tensor
factors or to squaring a single prime bank. Component l1/constants and every
outside/smooth/child sector must still be included in a full estimate.
"""
    if binding not in ('same_prime', 'distinct_primes') or type(binding) is not str:
        raise ValueError('reviewed prime binding')
    dimensions = 1 if binding == 'same_prime' else 2
    if type(weights) is not list or len(weights) != dimensions:
        raise ValueError('exactly one weight per independent free prime')
    values = [_rational(w) for w in weights]; theta = _rational(theta_text)
    if any(w <= 0 for w in values) or not Fraction(1, 2) <= theta < 1:
        raise ValueError('strictly positive weights and theta in[1/2,1)')
    meter.charge(4 * dimensions + 4)
    return dict(binding=binding, free_prime_count=dimensions,
                weights=[str(w) for w in values], theta=str(theta),
                energy_upper_power=str(1 - theta * sum(values, Fraction(0))),
                prime_count=dimensions, independent_labels=['q'] if dimensions == 1 else ['q', 'r'],
                geometry='smooth_bank' if dimensions == 1 else 'bank_bank',
                index_support='h<=n,k<=n/q' if dimensions == 1 else 'h<=n/q,k<=n/r',
                logs_retained=True,
                logarithmic_factors_retained=True,
                distinct_and_coprime_domain_required=True,
                whole_signed_bound_proved=False)
