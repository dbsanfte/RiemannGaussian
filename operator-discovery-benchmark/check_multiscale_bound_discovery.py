"""Independent admission of section closure and arbitrary-prefix certificates.

The source definition is trusted input; finite observations supply no proof.
Only exact rational arithmetic is used, without importing the searcher.
"""
from fractions import Fraction
import re


MAX_BITS = 4096
MAX_INTERNAL_BITS = 65536


class Meter:
    def __init__(self):
        self.operations = 0

    def charge(self, n=1):
        self.operations += n


def _require(test, message):
    if not test:
        raise ValueError(message)


def _meter(meter):
    return Meter() if meter is None else meter


def _checked(value, meter):
    meter.charge()
    _require(max(abs(value.numerator).bit_length(), value.denominator.bit_length())
             <= MAX_INTERNAL_BITS, 'intermediate rational size limit')
    return value


def _rational(text, meter):
    meter.charge()
    _require(type(text) is str and 1 <= len(text) <= 2500,
             'bounded rational string required')
    _require(re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', text) is not None,
             'integer or integer-ratio syntax required')
    try:
        value = Fraction(text)
    except (ValueError, ZeroDivisionError):
        raise ValueError('invalid rational') from None
    _require(str(value) == text, 'canonical rational required')
    _require(max(abs(value.numerator).bit_length(), value.denominator.bit_length())
             <= MAX_BITS, 'rational representation size limit')
    return value


def _vector(data, n, meter):
    _require(type(data) is list and len(data) == n, 'vector dimension')
    return [_rational(x, meter) for x in data]


def _matrix(data, rows, cols, meter):
    _require(type(data) is list and len(data) == rows, 'matrix row dimension')
    return [_vector(row, cols, meter) for row in data]


def _identity(n):
    return [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]


def _transpose(a):
    return [list(row) for row in zip(*a)]


def _mul(a, b, meter):
    _require(bool(a) and bool(b) and len(a[0]) == len(b), 'matrix product dimension')
    columns = _transpose(b)
    result = []
    for row in a:
        result.append([_checked(sum((_checked(x * y, meter)
                                    for x, y in zip(row, col)), Fraction(0)), meter)
                       for col in columns])
    return result


def _matvec(a, v, meter):
    return [row[0] for row in _mul(a, [[x] for x in v], meter)]


def _rowmul(v, a, meter):
    return _mul([v], a, meter)[0]


def _dot(v, w, meter):
    return _checked(sum((_checked(x * y, meter) for x, y in zip(v, w)), Fraction(0)), meter)


def _power(a, k, meter):
    result = _identity(len(a))
    factor = a
    while k:
        if k % 2:
            result = _mul(result, factor, meter)
        k //= 2
        if k:
            factor = _mul(factor, factor, meter)
    return result


def _psd(a, strict, meter):
    """Exact symmetric Schur elimination, including the zero-pivot condition."""
    n = len(a)
    _require(a == _transpose(a), 'quadratic form must be symmetric')
    work = [row[:] for row in a]
    for i in range(n):
        pivot = work[i][i]
        _require(pivot > 0 if strict else pivot >= 0,
                 'positive definite metric required' if strict else 'invariant residual is not PSD')
        if pivot == 0:
            _require(all(work[i][j] == 0 for j in range(i + 1, n)),
                     'zero PSD pivot has nonzero cross terms')
            continue
        for j in range(i + 1, n):
            for k in range(j, n):
                value = _checked(work[j][k] - work[i][j] * work[i][k] / pivot, meter)
                work[j][k] = work[k][j] = value


def _inverse(a, meter):
    n = len(a)
    work = [row[:] + ident for row, ident in zip(a, _identity(n))]
    for i in range(n):
        pivot_row = next((j for j in range(i, n) if work[j][i]), None)
        _require(pivot_row is not None, 'singular metric')
        work[i], work[pivot_row] = work[pivot_row], work[i]
        pivot = work[i][i]
        work[i] = [_checked(x / pivot, meter) for x in work[i]]
        for j in range(n):
            if j != i and work[j][i]:
                multiple = work[j][i]
                work[j] = [_checked(x - multiple * y, meter)
                           for x, y in zip(work[j], work[i])]
    return [row[n:] for row in work]


def _source(model, meter):
    _require(type(model) is dict and set(model) == {'base', 'matrices', 'initial', 'output'},
             'complete recursive source definition required')
    base = model['base']
    _require(type(base) is int and 2 <= base <= 8, 'source base2..8')
    _require(type(model['initial']) is list and 1 <= len(model['initial']) <= 32,
             'source dimension1..32')
    n = len(model['initial'])
    initial = _vector(model['initial'], n, meter)
    output = _vector(model['output'], n, meter)
    _require(type(model['matrices']) is list and len(model['matrices']) == base,
             'every residue matrix required')
    matrices = [_matrix(a, n, n, meter) for a in model['matrices']]
    _require(all(sum(map(abs, row)) <= 1 for a in matrices for row in a),
             'source row contraction required')
    _require(_matvec(matrices[0], initial, meter) == initial,
             'source unit/leading-zero consistency required')
    bound = _checked(sum(map(abs, output)) * max(map(abs, initial)), meter)
    return base, matrices, initial, output, bound


def _sections(base, output, matrices, states, meter):
    _require(type(states) is list and 1 <= len(states) <= 10, 'state dimension1..10')
    _require(states[0] == [1, 0], 'target state must be first')
    rows, seen = [], set()
    for state in states:
        _require(type(state) is list and len(state) == 2 and
                 all(type(x) is int for x in state), 'integer section pair required')
        scale, offset = state
        _require(1 <= scale <= base ** 8 and 0 <= offset < scale,
                 'bounded section scale/offset')
        rest, depth = scale, 0
        while rest > 1 and rest % base == 0:
            rest //= base
            depth += 1
        _require(rest == 1, 'section scale must be a power of source base')
        _require((scale, offset) not in seen, 'duplicate section')
        seen.add((scale, offset))
        row, digits = output[:], offset
        for _ in range(depth):
            row = _rowmul(row, matrices[digits % base], meter)
            digits //= base
        rows.append(row)
    return rows


def _reachable(matrices, initial, meter):
    """Span closure with actual integer-index witnesses, not sample fitting."""
    echelon, basis = [], []

    def insert(vector, index):
        remainder = vector[:]
        for pivot, row in echelon:
            multiple = remainder[pivot]
            if multiple:
                remainder = [_checked(x - multiple * y, meter)
                             for x, y in zip(remainder, row)]
        pivot = next((j for j, x in enumerate(remainder) if x), None)
        if pivot is None:
            return
        value = remainder[pivot]
        normalized = [_checked(x / value, meter) for x in remainder]
        # Insertion order need not have increasing pivots. Existing reduced
        # vectors vanish at every earlier pivot, which suffices for reduction.
        echelon.append((pivot, normalized))
        basis.append((vector, index))

    insert(initial, 0)
    cursor = 0
    while cursor < len(basis):
        vector, index = basis[cursor]
        for residue, matrix in enumerate(matrices):
            insert(_matvec(matrix, vector, meter), len(matrices) * index + residue)
        cursor += 1
    return basis


def _closure(model, states, transitions, meter):
    base, matrices, initial, output, source_bound = _source(model, meter)
    section_rows = _sections(base, output, matrices, states, meter)
    d = len(states)
    _require(type(transitions) is list and len(transitions) == base,
             'all closure residues required')
    parsed = [_matrix(a, d, d, meter) for a in transitions]
    reachable = _reachable(matrices, initial, meter)
    for residue in range(base):
        for i, section in enumerate(section_rows):
            left = _rowmul(section, matrices[residue], meter)
            right = _rowmul(parsed[residue][i], section_rows, meter)
            difference = [_checked(x - y, meter) for x, y in zip(left, right)]
            for vector, index in reachable:
                if _dot(difference, vector, meter):
                    witness = dict(state=i, residue=residue, n=index,
                                   left=str(_dot(left, vector, meter)),
                                   right=str(_dot(right, vector, meter)))
                    return dict(verified=False, valid=False, counterexample=witness,
                                reachable_dimension=len(reachable)), None
    admission = dict(verified=True, valid=True, counterexample=None,
                     reachable_dimension=len(reachable), source_bound=str(source_bound))
    return admission, (base, parsed, source_bound)


def verify_closure(model, states, transitions, meter=None):
    """Return a universal admission or an actual-index counterexample.

    Malformed definitions raise ValueError. A well-formed false identity returns
    valid=False; its witness is a reachable source value, not an arbitrary vector.
    """
    return _closure(model, states, transitions, _meter(meter))[0]


def verify(model, certificate, meter=None):
    """Admit an all-N prefix bound from a complete exact certificate."""
    meter = _meter(meter)
    _require(type(model) is dict, 'recursive source dictionary required')
    _require(type(certificate) is dict and set(certificate) ==
             {'base', 'states', 'transitions', 'bound'}, 'complete certificate required')
    _require(type(certificate['base']) is int and certificate['base'] == model.get('base'),
             'certificate/source base binding')
    closure, data = _closure(model, certificate['states'], certificate['transitions'], meter)
    _require(closure['valid'], 'false global section closure: ' + str(closure['counterexample']))
    base, transitions, source_bound = data
    d = len(certificate['states'])
    bound = certificate['bound']
    _require(type(bound) is dict and set(bound) ==
             {'alpha', 'Q', 'projection', 'block_transition'}, 'complete projected bound required')
    alpha = _rational(bound['alpha'], meter)
    _require(0 <= alpha <= 1 and alpha.denominator <= 24, 'alpha in[0,1], denominator<=24')
    _require(type(bound['projection']) is list and 1 <= len(bound['projection']) <= d,
             'observable bound dimension1..state dimension')
    h = len(bound['projection'])
    projection = _matrix(bound['projection'], h, d, meter)
    _require(projection[0] == [Fraction(int(j == 0)) for j in range(d)],
             'projection must recover the target exactly')
    reduced = _matrix(bound['block_transition'], h, h, meter)
    metric = _matrix(bound['Q'], h, h, meter)
    block = [[sum((a[i][j] for a in transitions), Fraction(0))
              for j in range(d)] for i in range(d)]
    _require(_mul(projection, block, meter) == _mul(reduced, projection, meter),
             'exact observable block quotient required')
    _psd(metric, True, meter)
    p, q = alpha.numerator, alpha.denominator
    step = _power(reduced, q, meter)
    transported = _mul(_mul(_transpose(step), metric, meter), step, meter)
    growth = base ** (2 * p)
    slack = [[_checked(growth * metric[i][j] - transported[i][j], meter)
              for j in range(h)] for i in range(h)]
    _psd(slack, False, meter)
    inverse = _inverse(metric, meter)
    phase, phase_costs = _identity(h)[0], []
    for _ in range(q):
        phase_costs.append(_dot(_rowmul(phase, inverse, meter), phase, meter))
        phase = _rowmul(phase, reduced, meter)
    phase_max = max(phase_costs)
    full_form = _mul(_mul(_transpose(projection), metric, meter), projection, meter)
    state_energy = _checked(source_bound ** 2 * sum((abs(x) for row in full_form for x in row),
                                                   Fraction(0)), meter)
    common = _checked(state_energy * phase_max, meter)
    if alpha:
        constant = _checked(common * base ** 4 / alpha ** 2, meter)
        expression = 'N^(2*alpha)'
        log_degree = 0
    else:
        constant = _checked(common * (base - 1) ** 2, meter)
        expression = '(1+floor(log_base(N)))^2'
        log_degree = 2
    return dict(verified=True, closure_verified=True, bound_proved=True,
                base=base, reachable_dimension=closure['reachable_dimension'],
                state_dimension=d, bound_dimension=h, alpha=str(alpha),
                source_bound=str(source_bound), state_energy_bound=str(state_energy),
                phase_costs=list(map(str, phase_costs)), phase_max=str(phase_max),
                squared_bound=dict(constant=str(constant), N_power=str(2 * alpha),
                                   log_degree=log_degree, expression=expression,
                                   domain='every integer N>=1; sum over 0<=n<N'),
                whole_signed_bound_proved=False, RH_proved=False)


def check_core_closure(*args, **kwargs):
    """Finite core observations are not a recursive all-index definition."""
    meter = kwargs.get('meter')
    if meter is not None:
        meter.charge()
    return dict(verified=False, valid=False, status='unknown',
                reason='no admitted all-index core closure prover', counterexample=None,
                bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)
