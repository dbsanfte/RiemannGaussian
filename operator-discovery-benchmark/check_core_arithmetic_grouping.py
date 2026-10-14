"""Independent complete ordered-pair audit of arithmetic grouping.

Q_rs sums every signed coefficient pair with labels(r,s), BEFORE absolute
values. The target is W_eta(2X)-rho*W_eta(X), identity filter only. Units,
old heads, both orientations, diagonals and all coefficients through4X-1
remain present. Grouping identities and finite envelopes prove no bound.

Return schema: group_labels (sorted observed integer labels); group_matrix
(row-major Arb Q_rs); signed_total; sum_abs; positive_sum (nonnegative
part); negative_sum (SIGNED nonpositive part); diagonal_coefficient_sum
(the original h=k diagonal, not the group-matrix diagonal); scalar_total
(independent full-prefix work); identity_residual; identity_verified; and
false all-scale/whole-bound/RH flags. Thus signed_total=positive_sum+
negative_sum and sum_abs=positive_sum-negative_sum, up to ball arithmetic.
"""
from fractions import Fraction as Q
import re
from flint import arb, ctx

MAX_INDICES = 524287
POWER_WORK = 64
SPECIAL_WORK = 256


class Meter:
    """Standalone shared-work meter; supplied study meters remain authoritative."""
    def __init__(self, cap=1500000000, max_cells=48000000):
        if type(cap) is not int or cap < 0 or type(max_cells) is not int or max_cells < 0:
            raise ValueError('nonnegative strict budget integers')
        self.cap = cap; self.max_cells = max_cells; self.operations = 0; self.peak_cells = 0
    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('strict nonnegative work')
        self.operations += n
        if self.operations > self.cap: raise RuntimeError('shared arithmetic work cap')
    def live(self, cells):
        if type(cells) is not int or cells < 0: raise ValueError('strict nonnegative resident cells')
        self.peak_cells = max(self.peak_cells, cells)
        if cells > self.max_cells: raise RuntimeError('resident cell cap')
    def counts(self): return dict(operations=self.operations, peak_cells=self.peak_cells)


def _rational(text):
    if type(text) is not str or not 1 <= len(text) <= 128 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
        raise ValueError('bounded canonical rational string')
    try: result = Q(text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational string') from error
    if str(result) != text: raise ValueError('canonical rational string')
    return result


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite(): raise ArithmeticError('finite Arb arithmetic')
    return value


def _real(value, meter):
    meter.charge(2)
    return _finite(arb(value.numerator) / value.denominator, meter)


def grouped_literal(coefficients, labels, X, eta='1', rho='1/2', meter=None):
    """Audit complete pair groups independently of any grouping producer.

This numerical identity accepts irregular X as well as dyadic probes; only
X>=1024 dyadic observations belong to the downstream theorem's domain.
No cache crosses calls or meters. Integral weights use exact Ei endpoints.
"""
    if meter is None: meter = Meter()
    if ctx.prec != 192: raise ValueError('independent Arb precision192')
    if type(X) is not int or X < 1 or 4 * X - 1 > MAX_INDICES: raise ValueError('bounded positive integerX')
    N = 4 * X - 1
    if type(coefficients) is not list or len(coefficients) != N + 1 or type(labels) is not list or len(labels) != N + 1:
        raise ValueError('exact complete4X coefficient and label lists')
    if any(type(label) is not int for label in labels): raise ValueError('strict integer labels, including dummy0')
    for coefficient in coefficients: _finite(coefficient, meter)
    if not coefficients[0].is_zero(): raise ValueError('zero dummy coefficient')
    eta_q = _rational(eta); rho_q = _rational(rho)
    if not -2 <= eta_q <= 2 or not 0 <= rho_q <= 1: raise ValueError('eta[-2,2],rho[0,1]')
    eta_a = _real(eta_q, meter); rho_a = _real(rho_q, meter)
    group_labels = sorted(set(labels[1:])); group_count = len(group_labels); meter.charge(2 * N)
    # Includes retained input, label maps, full matrix, transient scalar pairs,
    # log/Ei/endpoints, max kernels and the independent two prefix vectors.
    meter.live(2 * group_count * group_count + 20 * (N + 1) + 4096)
    index = {label: i for i, label in enumerate(group_labels)}
    group_index = [0] + [index[label] for label in labels[1:]]; meter.charge(N)
    matrix = [[arb(0) for _ in group_labels] for _ in group_labels]
    logarithms = [arb(0)] * (N + 2); ei = [arb(0)] * (N + 2)
    for n in range(2, N + 2):
        meter.charge(POWER_WORK + SPECIAL_WORK)
        logarithms[n] = _finite(arb(n).log(), meter)
        ei[n] = _finite((-logarithms[n]).ei(), meter)

    def d(Y, M):
        if M >= 2 * Y: return Q(0)
        return Q(1, max(Y, M)) - Q(1, 2 * Y)

    def ell(Y, M):
        if M >= 2 * Y: return arb(0)
        lower = max(Y, M)
        if lower == 1:
            # Only the (h,k)=(1,1) parent cell uses this placeholder; its
            # logarithmic multiplier is exactly0, and its true log work0.
            return arb(0)
        return _finite(ei[2 * Y] - ei[lower], meter)

    constant_kernel = [arb(0)] * (N + 1)
    log_kernel = [arb(0)] * (N + 1)
    for M in range(1, N + 1):
        dc = d(2 * X, M) - rho_q * d(X, M); meter.charge(6)
        constant_kernel[M] = _real((1 - eta_q) * dc, meter)
        difference = _finite(ell(2 * X, M) - _finite(rho_a * ell(X, M), meter), meter)
        log_kernel[M] = _finite(_finite(eta_a * difference, meter) / 2, meter)
    diagonal = arb(0)
    for h in range(1, N + 1):
        row = matrix[group_index[h]]; coefficient = coefficients[h]; log_h = logarithms[h]
        for k in range(1, N + 1):
            M = max(h, k)
            kernel = _finite(constant_kernel[M] + _finite(log_kernel[M] * _finite(log_h + logarithms[k], meter), meter), meter)
            pair = _finite(_finite(coefficient * coefficients[k], meter) * kernel, meter)
            j = group_index[k]; row[j] = _finite(row[j] + pair, meter)
            meter.charge(3)
            if h == k: diagonal = _finite(diagonal + pair, meter)
    signed = absolute = positive = negative = arb(0)
    for row in matrix:
        for value in row:
            magnitude = _finite(abs(value), meter)
            signed = _finite(signed + value, meter)
            absolute = _finite(absolute + magnitude, meter)
            positive = _finite(positive + _finite((value + magnitude) / 2, meter), meter)
            negative = _finite(negative + _finite((value - magnitude) / 2, meter), meter)
            meter.charge(4)
    # Independent scalar route: whole prefixes followed by exact unit-cell
    # integration. It does not reconstruct work from the pair/group matrix.
    F = [arb(0)] * (N + 1); B = [arb(0)] * (N + 1)
    for n in range(1, N + 1):
        F[n] = _finite(F[n - 1] + coefficients[n], meter)
        B[n] = _finite(B[n - 1] + _finite(coefficients[n] * logarithms[n], meter), meter)
    def shell(Y):
        critical = prime = arb(0)
        for n in range(Y, 2 * Y):
            square = _finite(F[n] * F[n], meter)
            critical = _finite(critical + _finite(square / (n * (n + 1)), meter), meter); meter.charge(2)
            if n == 1:
                if not B[n].is_zero(): raise ValueError('unit log prefix must be exactlyzero')
            else:
                cell = _finite(ei[n + 1] - ei[n], meter)
                prime = _finite(prime + _finite(_finite(F[n] * B[n], meter) * cell, meter), meter)
        return _finite(_finite((1 - eta_a) * critical, meter) + _finite(eta_a * prime, meter), meter)
    scalar = _finite(shell(2 * X) - _finite(rho_a * shell(X), meter), meter)
    residual = _finite(signed - scalar, meter)
    if not residual.contains(0): raise ValueError('complete ordered grouping fails scalar signed-work identity')
    return dict(group_labels=group_labels, group_matrix=matrix, signed_total=signed, sum_abs=absolute,
                positive_sum=positive, negative_sum=negative, diagonal_coefficient_sum=diagonal,
                scalar_total=scalar, identity_residual=residual, identity_verified=True,
                dyadic_domain=(X >= 1024 and X & (X - 1) == 0),
                all_scale_group_bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)


def _integer_root(n, exponent, meter):
    """Exact floor(n^(1/exponent)) by bounded integer bisection."""
    if type(n) is not int or n < 0 or type(exponent) is not int or exponent < 1:
        raise ValueError('nonnegative integer root arguments')
    if n < 2 or exponent == 1: meter.charge(); return n
    lower = 0; upper = 1 << ((n.bit_length() + exponent - 1) // exponent)
    while lower + 1 < upper:
        middle = (lower + upper) // 2; meter.charge(exponent + 3)
        if middle ** exponent <= n: lower = middle
        else: upper = middle
    # The upper bracket may itself be the exact root when n is a power2.
    meter.charge(exponent + 1)
    return upper if upper ** exponent <= n else lower


def _factor(n, meter):
    factors = []; p = 2
    while p * p <= n:
        meter.charge(2); exponent = 0
        while n % p == 0:
            n //= p; exponent += 1; meter.charge(3)
        if exponent: factors.append((p, exponent))
        p = 3 if p == 2 else p + 2; meter.charge()
    if n > 1: factors.append((n, 1)); meter.charge()
    return factors


def evaluate_labels(program, X, meter=None):
    """Independent exact arithmetic-key interpretation, no source coefficients.

Strip small prime valuations modulo1 or2, then apply the complete declared
post map. Factorization is by trial division, not the producer's sieve.
"""
    if meter is None: meter = Meter()
    if type(X) is not int or X < 1 or 4 * X - 1 > MAX_INDICES: raise ValueError('bounded positive integerX')
    if type(program) is not dict or set(program) != {'base', 'post'}: raise ValueError('exact base/post arithmetic AST')
    base = program['base']; post = program['post']
    if type(base) is not dict or set(base) != {'op', 'cutoff', 'valuation_step'} or base['op'] != 'strip_small_prime_powers':
        raise ValueError('exact stripping base')
    step = base['valuation_step']
    if type(step) is not int or step not in (1, 2): raise ValueError('valuation step1or2')
    cutoff = base['cutoff']
    if type(cutoff) is not dict or set(cutoff) != {'kind', 'value'}: raise ValueError('exact cutoff AST')
    value = _rational(cutoff['value']); kind = cutoff['kind']
    if kind == 'none':
        if value != 0: raise ValueError('none cutoff value0')
        cutoff_value = 0
    elif kind == 'fixed':
        if value not in (2, 3): raise ValueError('fixed cutoff2or3')
        cutoff_value = int(value)
    elif kind == 'power':
        if value not in (Q(1, 6), Q(1, 3), Q(1, 2), Q(2, 3), Q(1)): raise ValueError('declared power cutoff')
        cutoff_value = _integer_root(X ** value.numerator, value.denominator, meter); meter.charge(value.numerator)
    elif kind == 'log2':
        if value != 1: raise ValueError('log2 cutoff value1')
        cutoff_value = X.bit_length() - 1; meter.charge()
    else: raise ValueError('known cutoff kind')
    if type(post) is not dict or set(post) != {'op', 'value'}: raise ValueError('exact post AST')
    op = post['op']; post_value = _rational(post['value'])
    if op in ('identity', 'remove_largest_once', 'remove_smallest_once', 'remove_largest_all'):
        if post_value != 0: raise ValueError('identity/removal post value0')
    elif op == 'root':
        if post_value not in (2, 3, 6): raise ValueError('root post degree2,3or6')
    elif op == 'quotient':
        if post_value not in (Q(1, 3), Q(1, 2)): raise ValueError('quotient exponent1/3or1/2')
    elif op == 'residue':
        if post_value not in (2, 3, 6): raise ValueError('residue modulus2,3or6')
    else: raise ValueError('known post operation')
    denominator = 1
    if op == 'quotient':
        denominator = max(1, _integer_root(X ** post_value.numerator, post_value.denominator, meter))
        meter.charge(post_value.numerator)
    N = 4 * X - 1; meter.live(6 * (N + 1) + 4096)
    result = [0] * (N + 1)
    for n in range(1, N + 1):
        factors = _factor(n, meter); r = 1; retained = []
        for p, exponent in factors:
            if p <= cutoff_value: exponent %= step; meter.charge()
            if exponent:
                r *= p ** exponent; retained.append((p, exponent)); meter.charge(exponent + 2)
        if op == 'identity': label = r
        elif op == 'remove_largest_once': label = r // retained[-1][0] if retained else 1
        elif op == 'remove_smallest_once': label = r // retained[0][0] if retained else 1
        elif op == 'remove_largest_all': label = r // retained[-1][0] ** retained[-1][1] if retained else 1
        elif op == 'root': label = _integer_root(r, int(post_value), meter)
        elif op == 'quotient': label = r // denominator
        else: label = r % int(post_value)
        result[n] = label; meter.charge(3)
    return result
