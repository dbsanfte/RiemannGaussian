"""Coefficient-local arithmetic grammar with exact rational semantics.

Arrays have an unused zero entry. ``UNIT`` is delta_1, not the constant-one
sequence. These operators act on rational arithmetic functions; this module
does not assert analytic convergence of their Dirichlet series.
"""

from __future__ import annotations

from fractions import Fraction as Q
from functools import lru_cache
from math import gcd


def sequence(values):
    return [Q(0)] + [Q(value) for value in values]


def unit(size):
    return sequence([1] + [0] * (size - 1))


def require_same_size(left, right):
    if len(left) != len(right):
        raise ValueError("Arithmetic functions must have the same cutoff")


def convolve(left, right):
    require_same_size(left, right)
    size = len(left) - 1
    result = [Q(0)] * (size + 1)
    for i in range(1, size + 1):
        if left[i]:
            for j in range(1, size // i + 1):
                result[i * j] += left[i] * right[j]
    return result


def integer_power(values, exponent):
    if exponent < 0:
        raise ValueError("This production accepts only nonnegative integers")
    result = unit(len(values) - 1)
    factor = values
    while exponent:
        if exponent % 2:
            result = convolve(result, factor)
        exponent //= 2
        if exponent:
            factor = convolve(factor, factor)
    return result


def normalized_power(values, exponent):
    """Finite-at-each-index binomial series (delta_1+h)**exponent.

    If h(1)=0, h**k(n)=0 whenever 2**k>n. This structural termination
    bound holds on ALL inputs of the declared type, not just examples.
    """
    exponent = Q(exponent)
    if values[1] != 1:
        raise ValueError("Rational powers require f(1)=1")
    size = len(values) - 1
    residual = list(values)
    residual[1] -= 1
    term = unit(size)
    result = list(term)
    coefficient = Q(1)
    for k in range(1, size.bit_length()):
        term = convolve(term, residual)
        coefficient *= (exponent - k + 1) / k
        for n in range(1, size + 1):
            result[n] += coefficient * term[n]
    return result


def recursive_square_root(values):
    """Independent triangular implementation, with r(1)=1."""
    if values[1] != 1:
        raise ValueError("The normalized square root requires f(1)=1")
    size = len(values) - 1
    result = unit(size)
    for n in range(2, size + 1):
        middle = sum((result[d] * result[n // d]
                      for d in range(2, n) if n % d == 0), Q(0))
        result[n] = (values[n] - middle) / 2
    return result


def formal_log(values):
    if values[1] != 1:
        raise ValueError("Formal logarithms require f(1)=1")
    size = len(values) - 1
    residual = list(values)
    residual[1] -= 1
    term = unit(size)
    result = [Q(0)] * (size + 1)
    for k in range(1, size.bit_length()):
        term = convolve(term, residual)
        coefficient = Q((-1) ** (k + 1), k)
        for n in range(1, size + 1):
            result[n] += coefficient * term[n]
    return result


def formal_exp(values):
    if values[1] != 0:
        raise ValueError("Formal exponentials require h(1)=0")
    size = len(values) - 1
    term = unit(size)
    result = list(term)
    coefficient = Q(1)
    for k in range(1, size.bit_length()):
        term = convolve(term, values)
        coefficient /= k
        for n in range(1, size + 1):
            result[n] += coefficient * term[n]
    return result


def pointwise(left, right):
    require_same_size(left, right)
    return [a * b for a, b in zip(left, right)]


def add(left, right):
    require_same_size(left, right)
    return [a + b for a, b in zip(left, right)]


def scale(values, factor):
    return [Q(factor) * value for value in values]


def derivative(values, degree=1):
    """Euler degree on prime multiplicity: Omega(n)**degree times f(n).

    The logarithmic derivative in s is different. Omega is included as an
    explicit arithmetic feature; it is not silently learned from zeta.
    """
    return [Q(0)] + [value * sum(factorization(n).values()) ** degree
                    for n, value in enumerate(values[1:], 1)]


def factorization(n):
    if n < 1:
        raise ValueError("Factorization has positive-integer domain")
    result = {}
    divisor = 2
    while divisor * divisor <= n:
        while n % divisor == 0:
            result[divisor] = result.get(divisor, 0) + 1
            n //= divisor
        divisor += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


@lru_cache(maxsize=None)
def require_prime(prime):
    if prime < 2 or factorization(prime) != {prime: 1}:
        raise ValueError("A prime base is required for a prime valuation")


def valuation(integer, prime):
    require_prime(prime)
    if integer == 0:
        raise ValueError("The valuation of zero is outside this finite type")
    integer = abs(integer)
    result = 0
    while integer % prime == 0:
        integer //= prime
        result += 1
    return result


def digit_sum(integer, base):
    if integer < 0 or base < 2:
        raise ValueError("Digit sums require n>=0 and base>=2")
    result = 0
    while integer:
        integer, remainder = divmod(integer, base)
        result += remainder
    return result


def factorial_valuation(integer, prime):
    require_prime(prime)
    if integer < 0:
        raise ValueError("Factorial valuations require a nonnegative integer")
    result = 0
    while integer:
        integer //= prime
        result += integer
    return result


def exponent_map(values, multiplier):
    """Pull back f(n**multiplier); requires explicitly declared lookahead."""
    if multiplier < 1:
        raise ValueError("Positive exponent required")
    size = len(values) - 1
    result = [Q(0)]
    n = 1
    while n ** multiplier <= size:
        result.append(values[n ** multiplier])
        n += 1
    return result


def weighted_convolution(left, right, weight):
    require_same_size(left, right)
    size = len(left) - 1
    result = [Q(0)] * (size + 1)
    for i in range(1, size + 1):
        for j in range(1, size // i + 1):
            result[i * j] += Q(weight(i, j)) * left[i] * right[j]
    return result


def unitary_convolution(left, right):
    return weighted_convolution(left, right, lambda i, j: int(gcd(i, j) == 1))


def index_value(ast, environment):
    """Deeper typed index expressions; all return integers.

    Quotient and remainder by zero are rejected, not silently assigned zero.
    All iteration bounds must be supplied separately by the caller.
    """
    if isinstance(ast, int):
        return ast
    if isinstance(ast, str):
        return environment[ast]
    operation, *args = ast
    evaluated = [index_value(arg, environment) for arg in args]
    if operation == "add":
        return evaluated[0] + evaluated[1]
    if operation == "sub":
        return evaluated[0] - evaluated[1]
    if operation == "mul":
        return evaluated[0] * evaluated[1]
    if operation == "div":
        return evaluated[0] // evaluated[1]
    if operation == "mod":
        return evaluated[0] % evaluated[1]
    if operation == "gcd":
        return gcd(*evaluated)
    if operation == "min":
        return min(evaluated)
    if operation == "max":
        return max(evaluated)
    if operation == "digits":
        return digit_sum(*evaluated)
    if operation == "factval":
        return factorial_valuation(*evaluated)
    if operation == "eq":
        return int(evaluated[0] == evaluated[1])
    if operation == "le":
        return int(evaluated[0] <= evaluated[1])
    raise ValueError(f"Unknown index production: {operation}")


def program_value(program, inputs):
    if program["kind"] == "estimate_feedback_program":
        from cancellation_rewrite_grammar import program_value as feedback_value
        return feedback_value(program, inputs)
    if program["kind"] == "estimate_program":
        from estimate_grammar import program_value as estimate_value
        return estimate_value(program, inputs)
    if program["kind"] == "shift_ratio_program":
        from shift_ratio_grammar import program_value as shift_ratio_value
        return shift_ratio_value(program, inputs)
    if program["kind"] == "fractional_prime_program":
        # This explicit sort extends the rational core with rigorous real or
        # complex balls; its coefficient laws do not assert global RH bounds.
        from fractional_prime_grammar import program_value as fractional_value
        return fractional_value(program, inputs)
    if program["kind"] == "family_moment_program":
        from global_moment_grammar import program_value as moment_value
        return moment_value(program, inputs)
    kind = program["kind"]
    if kind == "residue_program":
        # Typed extension: its explicit finite-prime domain keeps numerical
        # residue semantics separate from exact rational Dirichlet identities.
        from creative_grammar import Term, evaluate
        return evaluate(Term.read(program["term"]), program["prime"], inputs)
    if kind == "input":
        return inputs[program["name"]]
    if kind == "power":
        return normalized_power(program_value(program["arg"], inputs),
                                Q(program["exponent"]))
    if kind == "root":
        if program["order"] < 2:
            raise ValueError("Root order must be at least two")
        return normalized_power(program_value(program["arg"], inputs),
                                Q(1, program["order"]))
    if kind == "log":
        return formal_log(program_value(program["arg"], inputs))
    if kind == "exp":
        return formal_exp(program_value(program["arg"], inputs))
    if kind in ("convolve", "pointwise", "add", "unitary"):
        evaluator = {"convolve": convolve, "pointwise": pointwise, "add": add,
                     "unitary": unitary_convolution}[kind]
        return evaluator(program_value(program["left"], inputs),
                         program_value(program["right"], inputs))
    if kind == "scale":
        return scale(program_value(program["arg"], inputs), Q(program["factor"]))
    raise ValueError(f"Unknown arithmetic production: {kind}")
