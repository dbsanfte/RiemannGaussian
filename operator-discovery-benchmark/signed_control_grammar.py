"""Signed scale recurrences and moments of cumulative arithmetic cancellation.

The operators preserve a quantified ordinary-zeta obstruction. Historical
priority is not an acceptance condition. Finite moment observations are not
uniform cancellation estimates.
"""
from fractions import Fraction as Q
from math import gcd
import flint


def real(value):
    value = Q(value)
    return flint.arb(value.numerator) / value.denominator


def atoms(rows):
    if not isinstance(rows, (list, tuple)):
        raise ValueError("Scale coefficients must be a list")
    merged = {}
    for d, a in rows:
        if type(d) is not int or d < 2:
            raise ValueError("Every scale divisor must be an integer >=2")
        merged[d] = merged.get(d, Q(0)) + Q(a)
    return tuple((d, a) for d, a in sorted(merged.items()) if a)


def critical_cost(rows):
    return sum((real(abs(a)) / flint.arb(d).sqrt() for d, a in atoms(rows)), flint.arb(0))


def lipschitz_cost(rows):
    return 1 + sum((abs(a) / d for d, a in atoms(rows)), Q(0))


def prefix(values):
    result = [0] * len(values)
    for n in range(1, len(values)):
        result[n] = result[n-1] + values[n]
    return result


def interpolation(mu, M, t):
    t = Q(t)
    n = t.numerator // t.denominator
    if t < 0 or n + bool(t.denominator != 1) >= len(M):
        raise ValueError("Interpolation exceeds the complete prefix")
    return Q(M[n]) if t.denominator == 1 else Q(M[n]) + (t-n) * mu[n+1]


def residual(mu, M, rows, t):
    return interpolation(mu, M, t) - sum((a * interpolation(mu, M, Q(t)/d) for d, a in atoms(rows)), Q(0))


def lattice(rows):
    rows = atoms(rows)
    D = 1
    for d, a in rows:
        denominator = (a/d).denominator
        D = D * denominator // gcd(D, denominator)
    return D, tuple((d, int(D*a/d)) for d, a in rows)


def integer_residual(mu, M, prepared, n):
    D, rows = prepared
    return D*M[n] - sum(b*(d*M[n//d] + mu[n//d+1]*(n % d)) for d, b in rows)


def unit_moment_numerator(left, right, order):
    if type(order) is not int or order < 2 or order % 2:
        raise ValueError("An even integer moment order >=2 is required")
    difference = right-left
    if not difference:
        return (order+1)*left**order
    numerator = right**(order+1)-left**(order+1)
    assert numerator % difference == 0
    return numerator // difference


def sampled_moments(mu, M, rows, scales, orders, cells):
    D, prepared_rows = lattice(rows)
    prepared = D, prepared_rows
    output = {}
    for X in scales:
        sums = {q: 0 for q in orders}
        selected = cells[str(X)]
        for n in selected:
            left = integer_residual(mu, M, prepared, n)
            right = integer_residual(mu, M, prepared, n+1)
            for q in orders:
                sums[q] += unit_moment_numerator(left, right, q)
        output[X] = {q: Q(X*sums[q], len(selected)*(q+1)*D**q) for q in orders}
    return output


def complete_window_moments(mu, M, rows, scales, orders):
    """Exact integrals on every unit interval, with no quadrature sampling."""
    endpoints = {x for X in scales for x in (X, 2*X)}
    D, prepared_rows = lattice(rows)
    prepared = D, prepared_rows
    cumulative = {q: 0 for q in orders}
    values = {}
    previous = integer_residual(mu, M, prepared, 0)
    for n in range(max(endpoints)+1):
        if n:
            current = integer_residual(mu, M, prepared, n)
            for q in orders:
                cumulative[q] += unit_moment_numerator(previous, current, q)
            previous = current
        if n in endpoints:
            values[n] = cumulative.copy()
    return {X: {q: Q(values[2*X][q]-values[X][q], (q+1)*D**q) for q in orders} for X in scales}


def positive_control_moment(rows, X, order, offset=0):
    rows = atoms(rows)
    slope = 1-sum((a/d for d, a in rows), Q(0))
    intercept = Q(offset)*(1-sum((a for d, a in rows), Q(0)))
    if slope == 0:
        return X*intercept**order
    return ((2*X*slope+intercept)**(order+1)-(X*slope+intercept)**(order+1))/(slope*(order+1))


def operator_certificate(rows):
    rows = atoms(rows)
    cost = critical_cost(rows)
    L = lipschitz_cost(rows)
    return {"operator": "R_a(t)=M_tilde(t)-sum a_d M_tilde(t/d)",
            "atoms": [[d, str(a)] for d, a in rows], "coefficient_domain": "actual Mobius, produced by Dirichlet inversion",
            "interpolation": "linear between integer cumulative sums; M_tilde(0)=0",
            "lipschitz_constant": str(L), "critical_inverse_cost_ball": cost.str(35),
            "nonvanishing_multiplier_Re_s_ge_half_certified": bool(cost < 1),
            "multiplier": "F_a(s)=1-sum a_d*d^(-s)",
            "ordinary_zeta_bridge": "Mellin(R_a)(s)=F_a(s)/(s*zeta(s))+H_a(s), H_a holomorphic for Re(s)>0",
            "inverse_cost": "1/(1-sum |a_d| d^(-theta)), when the denominator is positive",
            "global_signed_cancellation_estimate_proved": False,
            "historical_priority_is_acceptance_gate": False}


def moment_transfer_certificate(rows, order, beta):
    rows = atoms(rows)
    if type(order) is not int or order < 2 or order % 2:
        raise ValueError("An even integer moment order >=2 is required")
    beta = Q(beta)
    theta = beta/(order+1)
    cost = sum((real(abs(a))*real(d)**real(-theta) for d, a in rows), flint.arb(0))
    return {"order": order, "moment_exponent": str(beta), "pointwise_exponent": str(theta),
            "premise": "For every dyadic X>=1, integral_X^(2X) |R_a(t)|^q dt <= C X^beta",
            "residual_pointwise_constant": "(2^(q+2)*L*C)^(1/(q+1))",
            "inverse_cost_at_pointwise_exponent_ball": cost.str(35),
            "inverse_at_this_exponent_certified": bool(0 < theta <= 1 and cost < 1),
            "conclusion": "With the stated uniform premise, M(X)=O(X^theta), excluding ordinary zeta zeros Re(s)>theta",
            "uniform_moment_premise_proved": False,
            "RH_family_obligation": "Certify a sequence of uniform moment bounds with beta_q/(q+1)->1/2; every finite moment order is insufficient for that limit"}
