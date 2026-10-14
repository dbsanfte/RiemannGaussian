"""Independent meromorphic source normalization replay.

The initial Euler identity is used only in its absolute convergence domain.
No coefficient-series convergence at an interior pole is asserted.
"""
from collections import defaultdict
from fractions import Fraction as Q
import re

from flint import arb, ctx


class Meter:
    def __init__(self):
        self.operations = 0

    def charge(self, n=1):
        self.operations += n


def _require(value, message):
    if not value:
        raise ValueError(message)


def _q(value, meter):
    meter.charge()
    _require(type(value) is str and 1 <= len(value) <= 2500 and
             re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', value),
             'canonical bounded rational text')
    result = Q(value)
    _require(str(result) == value and
             max(abs(result.numerator).bit_length(), result.denominator.bit_length()) <= 4096,
             'canonical4096bit rational')
    return result


def _integer(value, meter, positive=False):
    meter.charge()
    _require(type(value) is int and abs(value).bit_length() <= 4096 and
             (not positive or value > 0), 'strict bounded integer')
    return value


def _checked(value, meter):
    meter.charge()
    _require(max(abs(value.numerator).bit_length(), value.denominator.bit_length()) <= 65536,
             'intermediate rational size cap')
    return value


def _same(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return set(a) == set(b) and all(_same(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(_same(x, y) for x, y in zip(a, b))
    return a == b


def _put(poly, key, coefficient, meter):
    coefficient = _checked(poly.get(key, Q(0)) + coefficient, meter)
    if coefficient:
        poly[key] = coefficient
    else:
        poly.pop(key, None)


def _encode(poly):
    return [{'coefficient': str(c), 'powers': [[a, e] for a, e in key]}
            for key, c in sorted(poly.items())]


def _parse_terms(data, meter):
    _require(type(data) is list and len(data) <= 4096, 'bounded Laurent polynomial')
    result, previous = {}, None
    for term in data:
        _require(type(term) is dict and set(term) == {'coefficient', 'powers'},
                 'exact Laurent term fields')
        coefficient = _q(term['coefficient'], meter)
        _require(coefficient != 0, 'nonzero Laurent coefficient')
        _require(type(term['powers']) is list and len(term['powers']) <= 64,
                 'bounded Laurent monomial')
        key, last = [], None
        for power in term['powers']:
            _require(type(power) is list and len(power) == 2, 'argument/exponent pair')
            argument = _q(power[0], meter)
            exponent = _integer(power[1], meter)
            _require(argument > 0 and argument != 1 and exponent != 0 and abs(exponent) <= 4096,
                     'regular positive zeta argument and nonzero bounded exponent')
            _require(last is None or last < power[0], 'lexically sorted distinct named constants')
            last = power[0]
            key.append((power[0], exponent))
        key = tuple(key)
        _require(previous is None or previous < key, 'sorted distinct Laurent terms')
        previous = key
        result[key] = coefficient
    return result


def _product(a, b, meter):
    result = {}
    for key, coefficient in a.items():
        for other, value in b.items():
            powers = dict(key)
            for argument, exponent in other:
                powers[argument] = powers.get(argument, 0) + exponent
            combined = tuple(sorted((s, e) for s, e in powers.items() if e))
            _put(result, combined, coefficient * value, meter)
    _require(len(result) <= 4096, 'Laurent product term cap')
    return result


def _sum(a, b, meter):
    result = a.copy()
    for key, coefficient in b.items():
        _put(result, key, coefficient, meter)
    return result


def _derive(source, meter):
    _require(type(source) is dict and set(source) == {'lattice', 'channels'}, 'exact source fields')
    lattice = _integer(source['lattice'], meter, positive=True)
    _require(type(source['channels']) is list and 1 <= len(source['channels']) <= 64,
             'bounded nonempty source channels')
    channels, points, shifts = [], set(), []
    for channel in source['channels']:
        _require(type(channel) is dict and set(channel) == {'atoms', 'weight'}, 'exact channel fields')
        _require(type(channel['weight']) is list and len(channel['weight']) == 2, 'affine scalar weight')
        for c in channel['weight']:
            _q(c, meter)
        _require(type(channel['atoms']) is list and len(channel['atoms']) <= 32, 'bounded atom list')
        exponents = defaultdict(int)
        for atom in channel['atoms']:
            _require(type(atom) is dict and set(atom) == {'kind', 'shift'} and
                     type(atom['kind']) is str and atom['kind'] in ('mu', 'power'), 'typed source atom')
            shift = Q(_integer(atom['shift'], meter), lattice)
            shifts.append(shift)
            exponents[shift] += 1 if atom['kind'] == 'power' else -1
        exponents = {s: e for s, e in exponents.items() if e}
        points.update(1 - s for s, e in exponents.items() if e > 0 and s < 1)
        channels.append({'weight': channel['weight'][:],
                         'factors': [[str(s), e] for s, e in sorted(exponents.items())]})
    poles = []
    for point in sorted(points):
        orders = [dict((Q(s), e) for s, e in c['factors']).get(1 - point, 0) for c in channels]
        row = {'point': str(point), 'channel_orders': orders}
        if max(orders) > 1:
            row['status'] = 'higher_order_unsupported'
        elif any(point + Q(s) <= 0 for c in channels for s, e in c['factors'] if Q(s) != 1 - point):
            row['status'] = 'nonpositive_regular_argument_unsupported'
        else:
            A, B = {}, {}
            for c, order in zip(channels, orders):
                if order != 1:
                    continue
                key = tuple(sorted((str(point + Q(s)), e) for s, e in c['factors'] if Q(s) != 1 - point))
                _put(A, key, _q(c['weight'][0], meter), meter)
                _put(B, key, _q(c['weight'][1], meter), meter)
            negative = {key: -c for key, c in A.items()}
            solution = None
            if len(B) == 1:
                (denkey, denominator), = B.items()
                inverse = {tuple((s, -e) for s, e in denkey): 1 / denominator}
                solution = _encode(_product(negative, inverse, meter))
            row.update(status='simple_affine_residue', residue={'constant': _encode(A), 'R': _encode(B)},
                       cancellation={'numerator': _encode(negative), 'denominator': _encode(B),
                                     'laurent_solution': solution})
        poles.append(row)
    return {'schema': 'source-pole-normalization-v1', 'source_binding': source,
            'initial_abscissa': str(max([Q(1)] + [1 - s for s in shifts])),
            'channels': channels, 'positive_poles': poles,
            'scope': {'reciprocal_zeta_zero_poles_enumerated': False, 'source_values_observed': False,
                      'uniform_bound_proved': False, 'RH_proved': False}}


def _evaluate(poly, values, meter):
    result = arb(0)
    for key, c in poly.items():
        value = arb(c.numerator) / c.denominator
        for argument, exponent in key:
            meter.charge(1 + abs(exponent))
            value *= values[argument] ** exponent
        result += value
    _require(result.is_finite(), 'finite rigorous Laurent evaluation')
    return result


def verify(source, proposal, actual_R=None, formal_R='2', target_sigma='1/2', meter=None):
    """Replay the AST; exact scalar definition is optional, interval binding is not.

    ``actual_R`` is an exact Laurent polynomial supplied by the source premise.
    Its provenance is the caller's independently admitted source definition.
    An interval for R cannot replace that definition.
    """
    meter = Meter() if meter is None else meter
    expected = _derive(source, meter)
    _require(_same(proposal, expected), 'complete source-generated normalization certificate')
    sigma, family_R = _q(target_sigma, meter), _q(formal_R, meter)
    _require(sigma == Q(1, 2), 'subpower block-energy holomorphy boundary is exactly1/2')
    binding = None if actual_R is None else _parse_terms(actual_R, meter)
    old_precision = ctx.prec
    checks = []
    try:
        ctx.prec = 256
        for row in expected['positive_poles']:
            if row['status'] != 'simple_affine_residue':
                checks.append({'point': row['point'], 'status': row['status'], 'normalization_admitted': False})
                continue
            A = _parse_terms(row['residue']['constant'], meter)
            B = _parse_terms(row['residue']['R'], meter)
            arguments = set(a for poly in (A, B, binding or {}) for key in poly for a, e in key)
            # All regular inverse factors must be nonzero even if their signed
            # residue cancels before numeric evaluation.
            point = Q(row['point'])
            arguments.update(str(point + Q(s)) for c in expected['channels'] for s, e in c['factors']
                             if Q(s) != 1 - point)
            values, gates = {}, []
            for argument in sorted(arguments):
                a = Q(argument)
                meter.charge(100)
                value = (arb(a.numerator) / a.denominator).zeta()
                _require(value.is_finite() and not value.contains(0), 'strict nonzero regular zeta gate')
                values[argument] = value
                gates.append({'argument': argument, 'interval': str(value), 'nonzero': True})
            formal = _sum(A, {key: c * family_R for key, c in B.items()}, meter)
            formal_value = _evaluate(formal, values, meter)
            formal_nonzero = bool(not formal_value.contains(0))
            substituted = None if binding is None else _sum(A, _product(B, binding, meter), meter)
            exact_zero = substituted == {} if binding is not None else False
            actual_value = None if substituted is None else _evaluate(substituted, values, meter)
            actual_nonzero = bool(actual_value is not None and not actual_value.contains(0))
            above = point > sigma
            checks.append({'point': row['point'], 'status': 'simple_affine_residue',
                           'regular_zeta_gates': gates,
                           'exact_binding_present': binding is not None,
                           'substituted_residue': None if substituted is None else _encode(substituted),
                           'exact_cancellation_proved': exact_zero,
                           'binding_residue_interval': None if actual_value is None else str(actual_value),
                           'binding_residue_nonzero': actual_nonzero,
                           'formal_R': str(family_R), 'formal_residue': _encode(formal),
                           'formal_residue_interval': str(formal_value),
                           'formal_family_pole_proved': formal_nonzero,
                           'family_subpower_energy_excluded': bool(formal_nonzero and above),
                           'supplied_binding_subpower_energy_excluded': bool(actual_nonzero and above),
                           'normalization_admitted': exact_zero})
    finally:
        ctx.prec = old_precision
    return {'verified': True, 'pole_checks': checks, 'target_sigma': str(sigma),
            'initial_identity_domain': 'Re(s)>' + expected['initial_abscissa'],
            'interior_interpretation': 'meromorphic_continuation_only',
            'ordinary_series_convergence_at_poles_asserted': False,
            'holomorphy_implication': {
                'premise': 'whole block energy O_epsilon(X^epsilon) for EVERY epsilon>0 and all sufficiently large X',
                'conclusion': 'Dirichlet source holomorphic on Re(s)>1/2',
                'proof': 'Abel integral and dyadic Cauchy-Schwarz; choose epsilon<2*Re(s)-1',
                'finite_initial_blocks_retained': True},
            'scope': {'fixed_scalar_provenance_required': True,
                      'interval_only_scalar_binding_admitted': False,
                      'reciprocal_zeta_zero_poles_enumerated': False,
                      'pole_cancellation_sufficient_for_bound': False,
                      'source_values_observed': False,
                      'actual_source_bound_refuted': False,
                      'uniform_bound_proved': False, 'RH_proved': False}}
