"""Exact independent source-law and rough-frontier certificate admission.

No producer, search solver, source observations or fitted constants are used.
Local rational series prove every prime valuation. Frontier bounds concern
only the declared prime-only rough prefix, never the joined original prefix.
"""
from fractions import Fraction as F
import re

from flint import arb, ctx


class Meter:
    def __init__(self):
        self.operations = 0

    def charge(self, n=1):
        self.operations += n


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _same(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return set(a) == set(b) and all(_same(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(_same(x, y) for x, y in zip(a, b))
    return a == b


def _meter(meter):
    return Meter() if meter is None else meter


def _q(text, meter):
    meter.charge()
    _require(type(text) is str and len(text) <= 2500 and
             re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', text) is not None,
             'bounded canonical rational syntax')
    value = F(text)
    _require(str(value) == text and
             max(abs(value.numerator).bit_length(), value.denominator.bit_length()) <= 4096,
             'canonical rational within4096 bits')
    return value


def _checked(value, meter):
    meter.charge()
    _require(max(abs(value.numerator).bit_length(), value.denominator.bit_length()) <= 65536,
             'intermediate rational size limit')
    return value


def _add(a, b, meter):
    result = a.copy()
    for key, coefficient in b.items():
        result[key] = _checked(result.get(key, F(0)) + coefficient, meter)
        if not result[key]:
            del result[key]
    return result


def _scale(a, coefficient, meter):
    if not coefficient:
        return {}
    return {key: _checked(value * coefficient, meter) for key, value in a.items()}


def _multiply(a, b, meter):
    result = {}
    for (i, j), x in a.items():
        for (k, l), y in b.items():
            key = (i + k, j + l)
            result[key] = _checked(result.get(key, F(0)) + x * y, meter)
    return {key: value for key, value in result.items() if value}


def _poly(data, meter):
    _require(type(data) is list and len(data) <= 4096, 'bounded polynomial term list')
    result, previous = {}, None
    for term in data:
        _require(type(term) is list and len(term) == 3 and
                 all(type(x) is int and 0 <= x <= 4096 for x in term[:2]),
                 'nonnegative integer polynomial degrees')
        key = tuple(term[:2])
        _require(previous is None or previous < key, 'sorted unique polynomial monomials')
        previous = key
        coefficient = _q(term[2], meter)
        _require(coefficient != 0, 'zero polynomial term forbidden')
        result[key] = coefficient
    return result


def _function(data, meter):
    _require(type(data) is dict and set(data) == {'numerator', 'denominator'},
             'complete rational-function representation')
    numerator, denominator = _poly(data['numerator'], meter), _poly(data['denominator'], meter)
    _require(bool(denominator), 'nonzero rational-function denominator')
    initial = {i: c for (i, j), c in denominator.items() if j == 0}
    _require(set(initial) == {0} and initial[0] != 0,
             'constant nonzero formal-series denominator at valuation zero')
    return numerator, denominator


def _fadd(a, b, meter):
    return (_add(_multiply(a[0], b[1], meter), _multiply(b[0], a[1], meter), meter),
            _multiply(a[1], b[1], meter))


def _fscale(a, coefficient, meter):
    return _scale(a[0], coefficient, meter), a[1]


def _fequal(a, b, meter):
    return _multiply(a[0], b[1], meter) == _multiply(b[0], a[1], meter)


ONE = {(0, 0): F(1)}
ZERO_FUNCTION = ({}, ONE)


def _source(source, meter):
    _require(type(source) is dict and set(source) == {'lattice', 'channels'},
             'complete arithmetic source definition')
    _require(type(source['lattice']) is int and source['lattice'] == 6,
             'sixth-root lattice required')
    channels = source['channels']
    _require(type(channels) is list and 1 <= len(channels) <= 12, 'source channel count1..12')
    factors, weights, atoms = [], [], []
    for channel in channels:
        _require(type(channel) is dict and set(channel) == {'atoms', 'weight'},
                 'source channel atoms and complete affine weight')
        _require(type(channel['atoms']) is list and 1 <= len(channel['atoms']) <= 8,
                 'one to eight source atoms per channel')
        _require(type(channel['weight']) is list and len(channel['weight']) == 2,
                 'constant and R source weights required')
        weights.append(tuple(_q(x, meter) for x in channel['weight']))
        numerator, denominator = ONE, ONE
        parsed = []
        for atom in channel['atoms']:
            _require(type(atom) is dict and set(atom) == {'kind', 'shift'} and
                     atom['kind'] in ('mu', 'power') and type(atom['shift']) is int and
                     0 <= atom['shift'] <= 24, 'licensed local Euler atom')
            kind, shift = atom['kind'], atom['shift']
            parsed.append((kind, shift))
            local = {(0, 0): F(1), (shift, 1): F(-1)}
            if kind == 'mu':
                numerator = _multiply(numerator, local, meter)
            else:
                denominator = _multiply(denominator, local, meter)
        factors.append((numerator, denominator))
        atoms.append(parsed)
    return factors, weights, atoms


def _valuation(atoms, valuation, meter):
    """Independent finite coefficient convolution of source atom series."""
    out = [ONE] + [{} for _ in range(valuation)]
    for kind, shift in atoms:
        local = ([ONE, {(shift, 0): F(-1)}] + [{} for _ in range(max(0, valuation - 1))]
                 if kind == 'mu' else [{(shift * e, 0): F(1)} for e in range(valuation + 1)])
        local = local[:valuation + 1]
        new = []
        for e in range(valuation + 1):
            value = {}
            for j in range(e + 1):
                value = _add(value, _multiply(out[j], local[e - j], meter), meter)
            new.append(value)
        out = new
    return out[valuation]


def _rank(rows, meter):
    work = [row[:] for row in rows]
    cursor = 0
    for column in range(len(rows[0])):
        pivot_row = next((i for i in range(cursor, len(work)) if work[i][column]), None)
        if pivot_row is None:
            continue
        work[cursor], work[pivot_row] = work[pivot_row], work[cursor]
        pivot = work[cursor][column]
        work[cursor] = [_checked(x / pivot, meter) for x in work[cursor]]
        for i in range(cursor + 1, len(work)):
            multiple = work[i][column]
            if multiple:
                work[i] = [_checked(x - multiple * y, meter)
                           for x, y in zip(work[i], work[cursor])]
        cursor += 1
        if cursor == len(work):
            break
    return cursor


def _states(source, states, meter):
    factors, weights, atoms = _source(source, meter)
    n = len(factors)
    _require(type(states) is list and 1 <= len(states) <= n, 'independent state count1..channel count')
    rows, valuations = [], {}
    for i, state in enumerate(states):
        _require(type(state) is dict and set(state) == {'row', 'program'}, 'state row and provenance')
        _require(type(state['row']) is list and len(state['row']) == n, 'source-bound state row dimension')
        row = [_q(x, meter) for x in state['row']]
        program = state['program']
        if i == 0:
            _require(_same(program, {'op': 'source'}) and row == [F(1)] * n,
                     'first state must be the complete signed source')
        else:
            _require(type(program) is dict and set(program) ==
                     {'op', 'parent', 'valuation', 'degree', 'scale'} and program['op'] == 'jet',
                     'complete prime-jet program')
            parent, e, degree = program['parent'], program['valuation'], program['degree']
            _require(type(parent) is int and 0 <= parent < i, 'acyclic earlier state parent')
            _require(type(e) is int and 0 <= e <= 24 and type(degree) is int and
                     0 <= degree <= 4096, 'bounded nonnegative valuation/jet degree')
            scale = _q(program['scale'], meter)
            if e not in valuations:
                valuations[e] = [_valuation(channel, e, meter) for channel in atoms]
            expected = [_checked(scale * rows[parent][j] * valuations[e][j].get((degree, 0), F(0)), meter)
                        for j in range(n)]
            _require(row == expected, 'exact jet derivation from parent source row')
            _require(next((x for x in row if x), None) == 1, 'canonical normalized jet row')
        rows.append(row)
        _require(_rank(rows, meter) == len(rows), 'every proposed state must be independent')
    return factors, weights, atoms, rows


def _actual_R(meter):
    """License the fixed source constant domain by an independent Arb enclosure."""
    meter.charge(1000)
    previous = ctx.prec
    try:
        ctx.prec = 256
        z2 = (arb(2) / 3).zeta()
        z4 = (arb(4) / 3).zeta()
        residue = (arb(9) / 2) * (z4 / (z2 * z2) - 1 / z2)
        _require(residue.is_finite() and residue > 1 and residue < 5,
                 'fixed R_u must be independently certified inside[1,5]')
        return str(residue)
    finally:
        ctx.prec = previous


def _affine_range(pair):
    a, b = pair
    return min(a + b, a + 5 * b), max(a + b, a + 5 * b)


def _ceiling(pair):
    return max(map(abs, _affine_range(pair)))


def _prime_polynomial(row, atoms, weights, meter):
    result = {}
    for multiplier, channel, weight in zip(row, atoms, weights):
        local = _valuation(channel, 1, meter)
        for (degree, zero), coefficient in local.items():
            old = result.get(degree, (F(0), F(0)))
            result[degree] = tuple(_checked(x + multiplier * coefficient * y, meter)
                                   for x, y in zip(old, weight))
    return {d: pair for d, pair in result.items() if any(pair)}


def _frontier(index, row, atoms, weights, meter):
    polynomial = _prime_polynomial(row, atoms, weights, meter)
    unit = tuple(_checked(sum((row[j] * weights[j][i] for j in range(len(row))), F(0)), meter)
                 for i in range(2))
    unit_ceiling = _ceiling(unit)
    return _from_prime(index, polynomial, unit_ceiling)


def _from_prime(index, polynomial, unit_ceiling):
    entries = [[d, str(a), str(b)] for d, (a, b) in sorted(polynomial.items())]
    expected = dict(state=index, prime_polynomial=entries, unit_ceiling=str(unit_ceiling),
                    scope='raw_rough_prefix_shared_cutoff_ceil_sqrt_2X',
                    all_integer_blocks=True, whole_signed_bound_proved=False)
    if not entries:
        expected.update(status='zero_prime_polynomial', lead_degree=None, sign=0,
                        coefficient_floor='0', remainder_ceiling='0', q_threshold='1/2',
                        coefficient_ceiling='0', r=None, energy_upper_exponent='-1',
                        energy_lower_exponent=None, upper_constant=str(unit_ceiling ** 2),
                        upper_log_power=0, refutes_separate_subpower_payment=False)
        return expected
    degree = entries[0][0]
    low, high = _affine_range(polynomial[degree])
    sign = 1 if low > 0 else -1 if high < 0 else 0
    floor = min(abs(low), abs(high)) if sign else F(0)
    tail = sum((_ceiling(pair) for d, pair in polynomial.items() if d > degree), F(0))
    ceiling = _ceiling(polynomial[degree]) + tail
    threshold = min(F(1, 2), floor / (2 * tail)) if tail and sign else F(1, 2)
    r = F(degree, 6)
    if r < 1:
        upper_power, log_power = 1 - 2 * r, 0
        constant = (unit_ceiling + 2 * ceiling / (1 - r)) ** 2
    elif r == 1:
        upper_power, log_power = F(-1), 2
        constant = (unit_ceiling + 2 * ceiling) ** 2
    else:
        upper_power, log_power = F(-1), 0
        constant = (unit_ceiling + ceiling * (1 + 1 / (r - 1))) ** 2
    lower = 1 - 2 * r if sign and r < 1 else None
    expected.update(status='two_sided_power_bound' if lower is not None else
                    'unresolved_leading_coefficient' if sign == 0 else 'upper_bound_only',
                    lead_degree=degree, sign=sign, coefficient_floor=str(floor),
                    remainder_ceiling=str(tail), q_threshold=str(threshold),
                    coefficient_ceiling=str(ceiling), r=str(r),
                    energy_upper_exponent=str(upper_power),
                    energy_lower_exponent=str(lower) if lower is not None else None,
                    upper_constant=str(constant), upper_log_power=log_power,
                    refutes_separate_subpower_payment=lower is not None and lower > 0)
    return expected


def _theorem_scope(bounds):
    descriptions = []
    for bound in bounds:
        lower = None
        if bound['energy_lower_exponent'] is not None:
            threshold = F(bound['q_threshold']) ** -6
            ceiling = (threshold.numerator + threshold.denominator - 1) // threshold.denominator
            lower = dict(c='log(2)/8', log_power=-2, energy_power=bound['energy_lower_exponent'],
                         constant='c^2*A^2/(64*2^(2*r))',
                         A=bound['coefficient_floor'], r=bound['r'],
                         head_requirements=['X>=16', 'y=ceil(sqrt(2*X))',
                                            'y>='+str(ceiling), 'y<=c*X/(2*log(X))',
                                            'J<=c*A*X^(1-r)/(8*2^r*log(X))'],
                         J=bound['unit_ceiling'], quantifier='all integer X beyond one finite uniform head',
                         prime_count_provider='elementary central-binomial bound; no PNT or RH')
        descriptions.append(dict(state=bound['state'],
            support='one shared y=ceil(sqrt(2*X)); unit and primes only for X<=n<2X',
            upper_domain='every integer X>=1', upper_factor='(1+log(X))^'+str(bound['upper_log_power']),
            lower=lower, complete_source_lower_bound=False))
    return descriptions


def _frontiers(atoms, weights, rows, bounds, meter):
    _require(type(bounds) is list and len(bounds) == len(rows), 'complete state frontier coverage')
    expected = [_frontier(i, row, atoms, weights, meter) for i, row in enumerate(rows)]
    _require(_same(bounds, expected), 'all source-bound frontier coefficients, signs, constants, powers and scopes')
    return expected


def verify_frontier(source, states, bounds, meter=None):
    meter = _meter(meter)
    _, weights, atoms, rows = _states(source, states, meter)
    residue = _actual_R(meter)
    expected = _frontiers(atoms, weights, rows, bounds, meter)
    return dict(verified=True, frontier_bounds=expected, R_enclosure=residue,
                theorem_scope=_theorem_scope(expected),
                scope='raw rough component only', whole_signed_bound_proved=False, RH_proved=False)


def verify(source, certificate, meter=None):
    """Verify all-prime/all-valuation laws, units and typed rough bounds."""
    meter = _meter(meter)
    _require(type(certificate) is dict and set(certificate) ==
             {'source', 'states', 'basis', 'transfer', 'unit', 'target_row', 'domain', 'frontier_bounds'},
             'complete certificate with no forged global-bound fields')
    _require(_same(certificate['source'], source), 'immutable complete source binding')
    factors, weights, atoms, rows = _states(source, certificate['states'], meter)
    n, h = len(factors), len(rows)
    _require(_same(certificate['basis'], [[str(x) for x in row] for row in rows]),
             'basis must consist of the proven state rows')
    _require(type(certificate['domain']) is dict and set(certificate['domain']) ==
             {'prime', 'cofactor_coprime', 'all_valuations'} and
             all(value is True for value in certificate['domain'].values()),
             'exact prime, coprime-cofactor and all-valuation domain required')
    data = certificate['transfer']
    _require(type(data) is list and len(data) == h and
             all(type(row) is list and len(row) == h for row in data), 'full transfer matrix dimension')
    transfer = [[_function(value, meter) for value in row] for row in data]
    for i in range(h):
        for j in range(n):
            lhs = ZERO_FUNCTION
            for k in range(h):
                lhs = _fadd(lhs, _fscale(transfer[i][k], rows[k][j], meter), meter)
            rhs = _fscale(factors[j], rows[i][j], meter)
            _require(_fequal(lhs, rhs, meter), 'full rational transfer identity including infinite valuation tail')
    expected_unit = [dict(constant=str(sum((row[j] * weights[j][0] for j in range(n)), F(0))),
                          R=str(sum((row[j] * weights[j][1] for j in range(n)), F(0))))
                     for row in rows]
    _require(_same(certificate['unit'], expected_unit), 'every signed unit/head source coefficient required')
    _require(type(certificate['target_row']) is list and len(certificate['target_row']) == h,
             'target recovery row dimension')
    target = [_q(x, meter) for x in certificate['target_row']]
    recovery = [sum((target[i] * rows[i][j] for i in range(h)), F(0)) for j in range(n)]
    _require(recovery == [F(1)] * n, 'complete original-source row recovery')
    residue = _actual_R(meter)
    bounds = _frontiers(atoms, weights, rows, certificate['frontier_bounds'], meter)
    return dict(verified=True, all_prime_coefficient_closure_proved=True,
                all_valuations_retained=True, target_recovery_proved=True,
                state_count=h, source_channel_count=n, R_enclosure=residue,
                residue_domain=['1', '5'], unit=expected_unit,
                frontier_bounds=bounds, frontier_bound_scope='raw rough shared-cutoff component only',
                theorem_scope=_theorem_scope(bounds),
                whole_prefix_bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)


def _psd2(a, b, c):
    if a < 0:
        return False
    if a == 0:
        return b == 0 and c >= 0
    return c - b * b / a >= 0


def verify_joined_forms(frontier_bound, certificate, meter=None, *, source=None, states=None):
    """Replay the finite storage dictionary and independently bind its premise."""
    meter = _meter(meter)
    _require(source is not None and states is not None, 'source and state binding required')
    _, weights, atoms, rows = _states(source, states, meter)
    _actual_R(meter)
    _require(type(frontier_bound) is dict, 'verified frontier premise required')
    state = frontier_bound.get('state')
    _require(type(state) is int and 0 <= state < len(rows), 'source-bound frontier state index')
    _require(_same(frontier_bound, _frontier(state, rows[state], atoms, weights, meter)),
             'complete source-bound frontier must be replayed before joined-form use')
    lower = frontier_bound['energy_lower_exponent']
    _require(lower is not None and _q(lower, meter) > 0 and
             frontier_bound['refutes_separate_subpower_payment'] is True,
             'proved positive rough lower exponent required')
    _require(type(certificate) is dict and set(certificate) ==
             {'status', 'dictionary', 'rows', 'scope', 'source_lower_state', 'source_lower_exponent',
              'counts', 'proof_rule', 'broader_multiscale_grammar_refuted', 'operations',
              'whole_signed_bound_proved', 'RH_proved'}, 'complete scoped joined-form certificate')
    diagonal = ['1/2', '1', '2', '3', '4']
    cross = ['-4', '-3', '-2', '-1', '-1/2', '0', '1/2', '1', '2', '3', '4']
    _require(_same(certificate['dictionary'], dict(diagonal=diagonal, cross=cross)),
             'complete frozen joined-storage dictionary')
    _require(type(certificate['rows']) is list and len(certificate['rows']) == 275,
             'every joined-form candidate required')
    coverage = {(a, b, c) for a in diagonal for b in cross for c in diagonal}
    counts = dict(target_not_dominated=0, refuted_by_rough_lower_bound=0, endpoint_restatement=0)
    for row in certificate['rows']:
        _require(type(row) is dict and set(row) ==
                 {'diagonal_left', 'cross', 'diagonal_right', 'schur_complement', 'endpoint_multiple',
                  'classification'}, 'complete candidate classification')
        key = row['diagonal_left'], row['cross'], row['diagonal_right']
        _require(key in coverage, 'missing, duplicate or outside-dictionary joined form')
        coverage.remove(key)
        a, b, c = (_q(x, meter) for x in key)
        expected = dict(diagonal_left=key[0], cross=key[1], diagonal_right=key[2],
                        schur_complement=None, endpoint_multiple=None)
        if not _psd2(a - 1, b - 1, c - 1):
            expected['classification'] = 'target_not_dominated'
        else:
            _require(_psd2(a, b, c) and c >= 1, 'target domination implies PSD and priced complement')
            schur = _checked(a - b * b / c, meter)
            expected['schur_complement'] = str(schur)
            if schur > 0:
                expected['classification'] = 'refuted_by_rough_lower_bound'
            else:
                _require(schur == 0 and a == b == c and a >= 1,
                         'zero-Schur dominated form must be a target multiple')
                expected['classification'] = 'endpoint_restatement'
                expected['endpoint_multiple'] = str(a)
        _require(_same(row, expected), 'exact target-domination, Schur and endpoint classification')
        counts[expected['classification']] += 1
    _require(not coverage, 'exhaustive joined-form coverage')
    metadata = dict(status='instantaneous_joined_storage_grammar_exhausted',
        scope='constant quadratic form in the two same-cutoff raw prefixes A,B',
        source_lower_state=state, source_lower_exponent=lower, counts=counts,
        proof_rule='Q-J PSD; Schur(Q) A^2 <= (A,B)Q(A,B)^t; singular survivor=kJ',
        broader_multiscale_grammar_refuted=False, operations=8250,
        whole_signed_bound_proved=False, RH_proved=False)
    _require(all(_same(certificate[key], value) for key, value in metadata.items()),
             'joined search accounting, source premise and finite-grammar scope')
    return dict(verified=True, counts=counts, source_lower_state=state,
                scope=metadata['scope'], source_frontier_binding_required=True,
                broader_multiscale_grammar_refuted=False,
                whole_signed_bound_proved=False, RH_proved=False)
