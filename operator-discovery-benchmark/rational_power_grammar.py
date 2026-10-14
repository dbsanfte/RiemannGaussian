"""Rational powers with explicit real signs, complex branches and recovery.

This extends, rather than changes, the frozen exact coefficient language.
There is no semantic denominator ceiling. Search protocols impose their own
finite resource limits. Dirichlet powers and pointwise powers are distinct.
"""
from fractions import Fraction as Q
import flint

from exact_arithmetic import normalized_power
from signed_control_grammar import integer_residual, lattice

VERSION = "rational-powers-and-absolute-moments-v1"
MODES = ("real", "signed", "absolute", "principal_complex")


class PowerDomainError(ValueError):
    pass


def rational(exponent):
    if isinstance(exponent, float):
        raise ValueError("Use an exact rational exponent, not a float")
    return Q(exponent)


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def exact_nth_root(n, d):
    """Return the exact nonnegative integer root, or None."""
    if n < 0 or d < 1:
        raise ValueError("Nonnegative radicand and positive root order required")
    if n < 2 or d == 1:
        return n
    low, high = 0, 1 << ((n.bit_length() + d - 1) // d)
    while high-low > 1:
        middle = (low+high)//2
        if middle**d <= n:
            low = middle
        else:
            high = middle
    return low if low**d == n else None


def positive_power(x, exponent):
    """Exact rational when possible, otherwise a certified real ball."""
    x, a = Q(x), rational(exponent)
    if x < 0 or (x == 0 and a <= 0):
        raise PowerDomainError("Nonnegative real power has a singular or negative input")
    if x == 0:
        return Q(0)
    numerator = exact_nth_root(x.numerator, a.denominator)
    denominator = exact_nth_root(x.denominator, a.denominator)
    if numerator is not None and denominator is not None:
        return Q(numerator, denominator)**a.numerator
    result = real(x).root(a.denominator)**a.numerator
    if not result.is_finite():
        raise ArithmeticError("Native root evaluation did not produce a finite enclosure")
    return result


def real_power(x, exponent, mode="real"):
    """Real algebraic, sign-preserving, or absolute power of Q or a real ball.

    signed(x,a)=sgn(x)|x|^a is a separate production; it is not called an
    ordinary even root of a negative number. Ambiguous domains reject rather
    than silently selecting a complex branch. Real-ball crossing zero is
    handled by monotonic endpoint enclosures, not native pow across zero.
    """
    a = rational(exponent)
    if mode not in MODES[:3]:
        raise ValueError("Unknown real power mode")
    if isinstance(x, flint.arb):
        if not x.is_finite():
            raise PowerDomainError("Nonfinite real input")
        lo, hi = Q(str(x.lower().fmpq())), Q(str(x.upper().fmpq()))
        if lo <= 0 <= hi and a <= 0:
            raise PowerDomainError("Nonpositive exponent across zero")
        if mode == "real" and a.denominator % 2 == 0 and lo < 0:
            raise PowerDomainError("An even-denominator real power requires a nonnegative input")
        left, right = real_power(lo, a, mode), real_power(hi, a, mode)
        ball = (left if isinstance(left, flint.arb) else real(left)).union(
            right if isinstance(right, flint.arb) else real(right))
        if lo <= 0 <= hi:
            ball = ball.union(0)
        return ball
    x = Q(x)
    if x < 0 and mode == "real" and a.denominator % 2 == 0:
        raise PowerDomainError("An even-denominator real power requires a nonnegative input")
    magnitude = positive_power(abs(x), a)
    negative = x < 0 and (mode == "signed" or (mode == "real" and a.numerator % 2))
    return -magnitude if negative else magnitude


def complex_power(z, exponent):
    """Principal power, certified analytic only off the declared branch cut."""
    a = rational(exponent)
    z = flint.acb(z)
    if not z.is_finite():
        raise PowerDomainError("Nonfinite complex input")
    if a.denominator == 1:
        if a <= 0 and z.contains(0):
            raise PowerDomainError("Integer nonpositive power at a possibly singular input")
        return z**a.numerator
    if z.contains(0) or (z.imag.contains(0) and not z.real > 0):
        raise PowerDomainError("Principal fractional power intersects (-infinity,0]")
    result = (z.log()*real(a)).exp()
    if not result.is_finite():
        raise ArithmeticError("Native principal power was not finite")
    return result


def infer(term):
    """Typed extension for pointwise, composed and Dirichlet rational powers.

    Inputs are declared real rational sequences. A complex literal is
    explicit. Scalar arithmetic broadcasts onto sequences. Root subtrees can
    be composed with signed sums, products, divisions and other roots.
    """
    if not isinstance(term, list) or not term:
        raise ValueError("Malformed rational-power AST")
    op = term[0]
    if op == "input" and len(term) == 2 and type(term[1]) is int and term[1] in (0, 1):
        return "real_sequence"
    if op == "q" and len(term) == 2:
        rational(term[1]); return "real_scalar"
    if op == "complex" and len(term) == 3:
        rational(term[1]); rational(term[2]); return "complex_scalar"
    if op in ("add", "mul", "div") and len(term) == 3:
        left, right = infer(term[1]), infer(term[2])
        return ("complex" if "complex" in left+right else "real") + (
            "_sequence" if "sequence" in left+right else "_scalar")
    if op in ("abs", "sign") and len(term) == 2:
        child = infer(term[1])
        if op == "sign" and "complex" in child:
            raise ValueError("Sign requires a real value")
        return child.replace("complex", "real")
    if op == "rpow" and len(term) == 4:
        child, exponent, mode = infer(term[1]), rational(term[2]), term[3]
        if mode not in MODES:
            raise ValueError("Unknown power mode")
        if "complex" in child and mode != "principal_complex":
            raise ValueError("Complex powers require a declared branch")
        return child.replace("real", "complex") if mode == "principal_complex" else child
    if op == "dpow" and len(term) == 3:
        if infer(term[1]) != "real_sequence":
            raise ValueError("Dirichlet power requires an exact normalized rational sequence")
        rational(term[2]); return "real_sequence"
    raise ValueError("Unknown production or invalid arity")


def evaluate(term, inputs):
    infer(term)
    def map_one(value, function):
        return [function(v) for v in value] if isinstance(value, list) else function(value)
    def map_two(left, right, function):
        if isinstance(left, list) and isinstance(right, list):
            if len(left) != len(right): raise ValueError("Sequence cutoffs differ")
            return [function(x, y) for x, y in zip(left, right)]
        if isinstance(left, list): return [function(x, right) for x in left]
        if isinstance(right, list): return [function(left, y) for y in right]
        return function(left, right)
    def go(t):
        op = t[0]
        if op == "input": return [Q(v) for v in inputs[t[1]]]
        if op == "q": return rational(t[1])
        if op == "complex": return flint.acb(real(t[1]), real(t[2]))
        if op in ("add", "mul", "div"):
            def arithmetic(x, y):
                if isinstance(x, (flint.arb, flint.acb)) and isinstance(y, Q): y = real(y)
                if isinstance(y, (flint.arb, flint.acb)) and isinstance(x, Q): x = real(x)
                if op == "div" and (y == 0 or (hasattr(y, "contains") and y.contains(0))):
                    raise PowerDomainError("Division includes a singular input")
                return x+y if op == "add" else (x*y if op == "mul" else x/y)
            return map_two(go(t[1]), go(t[2]), arithmetic)
        if op == "abs": return map_one(go(t[1]), abs)
        if op == "sign":
            def sign(x):
                if x > 0: return Q(1)
                if x < 0: return Q(-1)
                if x == 0: return Q(0)
                raise PowerDomainError("Unresolved sign")
            return map_one(go(t[1]), sign)
        if op == "rpow":
            fun = complex_power if t[3] == "principal_complex" else lambda x, a: real_power(x, a, t[3])
            return map_one(go(t[1]), lambda x: fun(x, t[2]))
        if op == "dpow":
            values = go(t[1])
            if not all(isinstance(v, Q) for v in values):
                raise PowerDomainError("Exact Dirichlet production received an irrational coefficient")
            return normalized_power([Q(0)] + values, rational(t[2]))[1:]
        raise AssertionError("Unreachable after typing")
    return go(term)


def power_certificate(exponent, mode):
    a = rational(exponent)
    if mode not in MODES:
        raise ValueError("Unknown power mode")
    return {"exponent": str(a), "mode": mode,
            "domain": ("complex plane minus (-infinity,0] for a noninteger exponent" if mode == "principal_complex" else
                       "real inputs; ordinary even-denominator powers require nonnegative values; nonpositive exponents exclude zero"),
            "signed_information_preserved_invertibly": bool(mode == "signed" and a > 0),
            "signed_inverse_exponent": str(1/a) if mode == "signed" and a > 0 else None,
            "absolute_moment_recovery": "|S_a(R)|^k=|R|^(a*k), for a,k>0",
            "complex_zero_monodromy": "exp(2*pi*i*a*m) around a zero of multiplicity m; only integral a*m gives a single-valued local power",
            "ordinary_zero_exclusion_proved": False,
            "uniform_signed_arithmetic_control_proved": False}


def unit_absolute_moment(left, right, order):
    """Certified integral of |(1-u)*left+u*right|^q on 0<=u<=1."""
    left, right, q = Q(left), Q(right), rational(order)
    if q <= 0:
        raise ValueError("A positive moment order is required")
    if left == right:
        result = positive_power(abs(left), q)
    else:
        def primitive(x):
            value = positive_power(abs(x), q+1)
            return -value if x < 0 else value
        u, v = primitive(left), primitive(right)
        if isinstance(u, flint.arb) or isinstance(v, flint.arb):
            u = u if isinstance(u, flint.arb) else real(u)
            v = v if isinstance(v, flint.arb) else real(v)
            result = (v-u)/real((q+1)*(right-left))
        else:
            result = (v-u)/((q+1)*(right-left))
    return result if isinstance(result, flint.arb) else real(result)


def complete_absolute_moments(mu, cumulative, rows, scales, orders):
    """Every unit interval is integrated; no quadrature or sampled cells.

    Cache algebraic antiderivative values at the integer residual lattice.
    Native balls enclose exact algebraic sums; fractional moments are not
    misreported as exact rational numbers.
    """
    orders = [rational(q) for q in orders]
    if any(q <= 0 for q in orders): raise ValueError("Moment orders must be positive")
    D, prepared_rows = lattice(rows)
    prepared = D, prepared_rows
    endpoints = {v for X in scales for v in (X, 2*X)}
    total = {q: flint.arb(0) for q in orders}
    caches = {q: {} for q in orders}
    flat = {q: {} for q in orders}
    normalization = {q: real(D).root(q.denominator)**q.numerator for q in orders}
    snapshots = {}
    previous = integer_residual(mu, cumulative, prepared, 0)
    def power_ball(n, exponent, cache):
        if n not in cache:
            # Zero is explicit because native general root(0,d) may be nan.
            cache[n] = flint.arb(0) if n == 0 else flint.arb(n).root(exponent.denominator)**exponent.numerator
        return cache[n]
    for n in range(max(endpoints)+1):
        if n:
            current = integer_residual(mu, cumulative, prepared, n)
            for q in orders:
                if current == previous:
                    piece = power_ball(abs(current), q, flat[q])
                else:
                    u = power_ball(abs(previous), q+1, caches[q])
                    v = power_ball(abs(current), q+1, caches[q])
                    if previous < 0: u = -u
                    if current < 0: v = -v
                    piece = (v-u)/real((q+1)*(current-previous))
                total[q] += piece
            previous = current
        if n in endpoints: snapshots[n] = total.copy()
    result = {X: {q: (snapshots[2*X][q]-snapshots[X][q])/normalization[q] for q in orders} for X in scales}
    if any(not v.is_finite() for row in result.values() for v in row.values()):
        raise ArithmeticError("A complete moment was not finite")
    return result


def transfer_certificate(order, beta, constant, lipschitz):
    q, beta, C, L = map(rational, (order, beta, constant, lipschitz))
    if q <= 0 or beta < 0 or C <= 0 or L <= 0:
        raise ValueError("Positive order, constant and Lipschitz bound are required")
    if q >= 1:
        eta = (beta-1)/q
        method = "Holder-Mellin, including the L1 endpoint"
        bound_C = real(C).root(q.numerator)**q.denominator
    else:
        # Lipschitz peaks give sup|R| <= K X^(beta/(q+1)), and
        # integral|R| <= sup|R|^(1-q) * integral|R|^q.
        eta = 2*beta/(q+1)-1
        method = "Lipschitz peak bound followed by an L1-Mellin transfer; Holder is not applied below one"
        K = (real(2)**real(q+2)*real(L*C))**real(1/(q+1))
        bound_C = real(C)*K**real(1-q)
    return {"order": str(q), "beta": str(beta), "constant": str(C), "lipschitz": str(L),
            "mellin_exponent": str(eta), "method": method,
            "mellin_bound_coefficient_ball": bound_C.str(45),
            "premise": "For every dyadic X>=1, integral_X^(2X)|R(t)|^q dt <= C X^beta; |R(t)|<=L*t and Lipschitz constant<=L",
            "RH_sufficient_if_uniform_and_all_height_multiplier_nonzero": bool(eta <= Q(1,2)),
            "contradicted_if_critical_zero_multiplier_nonzero": bool(eta < Q(1,2)),
            "uniform_signed_moment_premise_proved": False, "RH_proved": False}
