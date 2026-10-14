"""Independent exact factor certificates and scoped prime-edge bound audit.

Divisibility is checked by rational substitution, not polynomial division.
Recomposition retains every original tensor component; a local factorization
or conditional directed-edge bound is never a full signed recovery theorem.
"""
from fractions import Fraction as Q
from math import comb, gcd
import re

MAX_ROWS = 512
MAX_EXPONENT = 24
MAX_BITS = 4096


def linear_forms():
    result = []
    for a in range(-2, 3):
        for b in range(-2, 3):
            for c in range(-2, 3):
                if (a, b) == (0, 0) or gcd(gcd(abs(a), abs(b)), abs(c)) != 1: continue
                if (a if a else b) <= 0: continue
                result.append([a, b, c])
    return sorted(result)


def _number(value, meter):
    meter.charge()
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_BITS:
        raise OverflowError('exact rational bit cap')
    return value


def _rational(text):
    if type(text) is not str or not 1 <= len(text) <= 128 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
        raise ValueError('bounded canonical rational string')
    try: value = Q(text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational text') from error
    if str(value) != text: raise ValueError('canonical rational string')
    return value


def _poly(poly, meter, kind=None):
    if type(poly) is not list or len(poly) > MAX_ROWS:
        raise ValueError('bounded canonical sparse polynomial')
    result = {}; previous = None
    for row in poly:
        if type(row) is not list or len(row) != 2:
            raise ValueError('exponent/coefficient row')
        exponent, coefficient = row
        if type(exponent) is not list or len(exponent) != 2 or any(type(e) is not int or not 0 <= e <= MAX_EXPONENT for e in exponent):
            raise ValueError('bounded bivariate integer exponents')
        key = tuple(exponent)
        if previous is not None and key <= previous: raise ValueError('strict lexicographic sparse support')
        previous = key
        if kind == 'integer' and type(coefficient) is not int: raise ValueError('original integer coefficient')
        if kind == 'rational' and type(coefficient) is not str: raise ValueError('quotient canonical rational string')
        if type(coefficient) is int: value = Q(coefficient)
        elif type(coefficient) is str: value = _rational(coefficient)
        else: raise ValueError('exact integer or rational string coefficient')
        if not value: raise ValueError('zero sparse coefficients must be omitted')
        result[key] = _number(value, meter)
    return result


def _form(form):
    if type(form) is not list or len(form) != 3 or any(type(x) is not int for x in form) or form not in linear_forms():
        raise ValueError('normalized searched primitive linear form')
    return form


def _substitutes_zero(poly, form, meter):
    a, b, c = form; result = {}
    for (i, j), coefficient in poly.items():
        if a:
            scalar = _number(coefficient * Q(-1, a) ** i, meter)
            for k in range(i + 1):
                meter.charge(4 + i)
                value = _number(scalar * comb(i, k) * b ** k * c ** (i - k), meter)
                degree = k + j
                result[degree] = _number(result.get(degree, Q(0)) + value, meter)
        else:
            meter.charge(2 + j)
            value = _number(coefficient * Q(-c, b) ** j, meter)
            result[i] = _number(result.get(i, Q(0)) + value, meter)
    return all(not coefficient for coefficient in result.values())


def divisible(poly, form, meter):
    _form(form); meter.live(65536)
    return _substitutes_zero(_poly(poly, meter), form, meter)


def _multiply(left, right, meter):
    result = {}
    for (i, j), coefficient in left.items():
        for (k, l), other in right.items():
            meter.charge(3)
            exponent = (i + k, j + l)
            value = _number(result.get(exponent, Q(0)) + _number(coefficient * other, meter), meter)
            if value: result[exponent] = value
            elif exponent in result: del result[exponent]
    if len(result) > MAX_ROWS: raise OverflowError('recomposition sparse-row cap')
    return result


def verify(original, factors, quotients, meter):
    if type(original) is not list or type(quotients) is not list or len(original) != 9 or len(quotients) != 9:
        raise ValueError('all nine row-major tensor components required')
    meter.live(131072)
    source = [_poly(poly, meter, 'integer') for poly in original]
    residual = [_poly(poly, meter, 'rational') for poly in quotients]
    if not any(source): raise ValueError('all-zero original tensor has no maximal factorization')
    if type(factors) is not list or len(factors) > MAX_EXPONENT:
        raise ValueError('bounded factor list')
    product = {(0, 0): Q(1)}; previous = None; total = 0
    for factor in factors:
        if type(factor) is not dict or set(factor) != {'coefficients', 'multiplicity'}:
            raise ValueError('exact factor schema')
        form = _form(factor['coefficients']); key = tuple(form)
        multiplicity = factor['multiplicity']
        if type(multiplicity) is not int or not 1 <= multiplicity <= MAX_EXPONENT:
            raise ValueError('positive bounded factor multiplicity')
        if previous is not None and key <= previous: raise ValueError('ordered distinct factors required')
        previous = key; total += multiplicity
        if total > MAX_EXPONENT: raise ValueError('bounded total factor degree')
        linear = {exponent: Q(c) for exponent, c in zip(((1, 0), (0, 1), (0, 0)), form) if c}
        for _ in range(multiplicity): product = _multiply(product, linear, meter)
    for before, after in zip(source, residual):
        if _multiply(product, after, meter) != before:
            raise ValueError('complete exact polynomial recomposition failed')
    nonzero = [p for p in residual if p]
    if not nonzero: raise ValueError('nonzero original requires nonzero residual')
    for form in linear_forms():
        if all(_substitutes_zero(poly, form, meter) for poly in nonzero):
            raise ValueError('residual has an omitted searched common linear factor')
    return dict(original=original, factors=factors, quotients=quotients,
                residual_maximal=True, searched_linear_form_count=len(linear_forms()),
                scope='all nine local tensor components on original distinct/coprime prime domain',
                whole_signed_bound_proved=False, full_domain_recovery='OPEN')


def edge_bound(theta_text, weight_text, degree_text, meter):
    theta = _rational(theta_text); weight = _rational(weight_text); degree = _rational(degree_text)
    if not Q(1, 2) <= theta < 1 or weight <= 0 or degree <= 0:
        raise ValueError('theta in[1/2,1), positive weight and outgoing degree')
    exponent = _number(1 - theta * (1 + weight), meter)
    constant_exponent = _number(max(2 - theta * (1 + weight), Q(0)), meter)
    multiplier = _number(2 * degree * (2 + weight) / (1 + weight), meter)
    return dict(theta=str(theta), weight=str(weight), degree=str(degree),
                geometry='directed_prime_edges', orientation='r<q',
                cutoff='r>n^theta and q>n^theta',
                outgoing_degree_scope='at most degree outgoing q per fixed r, uniformly in n and r',
                growing_degree_graphs_admitted=False,
                coefficient_hypothesis='absolute pair coefficient <= C*d2(H)*d2(K)*r^(-weight)',
                both_orientation_supports_retained=True,
                energy_upper_power=str(exponent), logdegree=2,
                constant_multiplier=str(multiplier), constant_power_of_two=str(constant_exponent),
                cofinal=exponent <= 0, conditional_primitive=True,
                symmetric_component='OPEN', core_component='OPEN',
                full_domain_recovery='OPEN', whole_signed_bound_proved=False)
