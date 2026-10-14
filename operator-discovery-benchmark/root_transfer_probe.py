#!/usr/bin/env python3
"""Discover and certify the root-order limit across two arithmetic products.

T(f)=EXP_no_carry(LOG_Dirichlet(f)) is a nonlinear unit-group transfer.
Local root-lift coefficients are exact polynomials in alpha=1/q. Bernstein
bounds plus a uniform tail can certify EVERY integer q>=2 and the q=inf
limit, instead of extrapolating from finitely many roots.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import random
import time

import flint

from exact_arithmetic import (convolve, factorization, formal_log, sequence,
                              unit, weighted_convolution)


def rational(value):
    return Q(int(value.numerator), int(value.denominator))


def local_no_carry_product(left, right):
    size = len(left)
    zero = left[0] * 0
    result = [zero for _ in left]
    for n in range(size):
        for i in range(n + 1):
            if not i & (n - i):
                result[n] += left[i] * right[n - i]
    return result


def local_root_lift_polynomials(degree):
    alpha = flint.fmpq_poly([0, 1])
    zero, one = flint.fmpq_poly(), flint.fmpq_poly([1])
    # d_e(alpha)=c_alpha(e)/alpha, with its polynomial value at alpha=0.
    d = [zero, one]
    for e in range(2, degree + 1):
        d.append(d[-1] * (alpha + e - 1) / e)
    output = [one] + [zero] * degree
    term = list(output)
    coefficient = one
    # No-carry multiplication cannot create an exponent with fewer binary
    # digits than its number of nonunit factors. This is a proved bound.
    maximum_factors = max(e.bit_count() for e in range(degree + 1))
    for k in range(1, maximum_factors + 1):
        term = local_no_carry_product(term, d)
        coefficient *= (1 - (k - 1) * alpha)
        coefficient /= k
        output = [value + coefficient * summand for value, summand in zip(output, term)]
    return output


def evaluate(poly, value):
    value = Q(value)
    result = Q(0)
    for coefficient in reversed(poly.coeffs()):
        result = result * value + rational(coefficient)
    return result


def bernstein_bound(poly, lower, upper):
    """Exact convex-hull bound on a real polynomial over an interval."""
    variable = flint.fmpq_poly([flint.fmpq(lower.numerator, lower.denominator),
                               flint.fmpq((upper-lower).numerator, (upper-lower).denominator)])
    transformed = flint.fmpq_poly()
    for coefficient in reversed(poly.coeffs()):
        transformed = transformed * variable + coefficient
    powers = [rational(coefficient) for coefficient in transformed.coeffs()]
    degree = max(len(powers) - 1, 0)
    if not powers:
        return Q(0), []
    coefficients = [sum((powers[j] * Q(comb(k, j), comb(degree, j)) for j in range(k+1)), Q(0))
                    for k in range(degree+1)]
    return max(map(abs, coefficients)), coefficients


def uniform_root_certificate(polynomials, radius, intervals):
    degree = len(polynomials) - 1
    corrections = [polynomials[0]] + [polynomials[e] - polynomials[e-1]
                                      for e in range(1, degree+1)]
    certificates = []
    for lower, upper in intervals:
        finite, bounds = Q(0), []
        for e in range(2, degree+1):
            cap, bernstein = bernstein_bound(corrections[e], lower, upper)
            finite += cap * radius ** e
            bounds.append({"exponent": e, "coefficient_bound": str(cap),
                           "bernstein_coefficients": [str(value) for value in bernstein]})
        tail = 2 * radius ** (degree+1) / (1-radius)
        total = finite + tail
        certificates.append({"alpha_interval": [str(lower), str(upper)], "radius": str(radius),
                             "degree": degree, "finite_sum_bound": str(finite), "uniform_tail_bound": str(tail),
                             "total_bound": str(total), "total_decimal_diagnostic": float(total),
                             "passed": total < 1, "coefficient_bounds": bounds})
    return certificates


def no_carry_arithmetic_product(left, right):
    def weight(i, j):
        a, b = factorization(i), factorization(j)
        return int(all(not a.get(p, 0) & b.get(p, 0) for p in a.keys() | b.keys()))
    return weighted_convolution(left, right, weight)


def algebra_log(values, product):
    if values[1] != 1:
        raise ValueError("Arithmetic logarithms require f(1)=1")
    h = list(values)
    h[1] -= 1
    term = unit(len(values)-1)
    output = [Q(0)] * len(values)
    for k in range(1, (len(values)-1).bit_length()):
        term = product(term, h)
        coefficient = Q((-1)**(k+1), k)
        output = [a + coefficient*b for a, b in zip(output, term)]
    return output


def algebra_exp(values, product):
    if values[1] != 0:
        raise ValueError("Arithmetic exponentials require h(1)=0")
    term = unit(len(values)-1)
    output = list(term)
    coefficient = Q(1)
    for k in range(1, (len(values)-1).bit_length()):
        term = product(term, values)
        coefficient /= k
        output = [a + coefficient*b for a, b in zip(output, term)]
    return output


def transfer(values):
    return algebra_exp(formal_log(values), no_carry_arithmetic_product)


def inverse_transfer(values):
    return algebra_exp(algebra_log(values, no_carry_arithmetic_product), convolve)


def exact_transfer_checks():
    rng = random.Random(2026100610)
    records = []
    for size in (32, 65, 128):
        a, b = [sequence([1] + [Q(rng.randint(-3, 3), rng.randint(1, 5))
                               for _ in range(size-1)]) for _ in range(2)]
        laws = {
            "transfers_product": transfer(convolve(a,b)) == no_carry_arithmetic_product(transfer(a), transfer(b)),
            "inverse_transfer": inverse_transfer(transfer(a)) == a,
            "forward_transfer": transfer(inverse_transfer(a)) == a,
            "prefix_consistency": transfer(a)[:size//2+1] == transfer(a[:size//2+1]),
        }
        records.append({"cutoff": size, "laws": laws})
    f, g = sequence([1,1,0,0]), sequence([1,1,0,0])
    fg = [x+y for x,y in zip(f,g)]
    fg[1] = Q(1)  # normalized affine addition f+g-delta
    expected = [x+y for x,y in zip(transfer(f),transfer(g))]
    expected[1] = Q(1)
    nonlinear = transfer(fg) != expected
    impulse = sequence([0,1,0,0])
    return {"records": records,
            "affine_linearity_negative_control_rejected": nonlinear,
            "nilpotent_no_carry_impulse": no_carry_arithmetic_product(impulse,impulse) == [Q(0)]*5,
            "ordinary_impulse_square_nonzero": convolve(impulse,impulse)[4] == 1,
            "all_checks_passed": all(all(x["laws"].values()) for x in records) and nonlinear}


def main():
    started = time.monotonic()
    output = Path(__file__).resolve().parent / "transfer-results"
    output.mkdir(parents=True, exist_ok=True)
    degree, radius = 32, Q(71,100)
    print("Synthesizing root-lift coefficient polynomials in alpha=1/q", flush=True)
    polynomials = local_root_lift_polynomials(degree)
    intervals = [(Q(0), Q(1,2))]
    certificates = uniform_root_certificate(polynomials, radius, intervals)
    # If a broad convex-hull bound is too loose, subdivide the parameter
    # domain; a failed bound is not a counterexample to the proposed law.
    if not all(record["passed"] for record in certificates):
        intervals = [(Q(k,16),Q(k+1,16)) for k in range(8)]
        certificates = uniform_root_certificate(polynomials, radius, intervals)
    print("Checking the nonlinear product-transfer operator on unrelated inputs", flush=True)
    checks = exact_transfer_checks()
    limit = [evaluate(poly,Q(0)) for poly in polynomials]
    u = sequence([1]*128)
    actual = transfer(u)
    predicted = [Q(0)]+[Q(1)]
    for n in range(2,129):
        value=Q(1)
        for e in factorization(n).values():
            value*=limit[e]
        predicted.append(value)
    result = {"operator": "EXP_no_carry(LOG_Dirichlet(f))", "domain": "rational arithmetic functions f with f(1)=1",
              "source": "coefficientwise q->infinity limit of previously measured and verified zeta-root lifts",
              "formal_checks": checks, "limit_local_coefficients": [str(value) for value in limit],
              "first_root_lift_polynomials": [str(poly) for poly in polynomials[:13]],
              "all_polynomial_coefficients": [[str(value) for value in poly.coeffs()] for poly in polynomials],
              "uniform_certificate": certificates,
              "uniform_domain": "all integer q>=2 and q=infinity, binary carry parameter t=0",
              "uniform_nonzero_correction_Re_s_gt_half_proved": all(x["passed"] for x in certificates),
              "direct_arithmetic_limit_equals_local_polynomial_evaluation": actual==predicted,
              "first_arithmetic_coefficients": [str(x) for x in actual[1:33]],
              "proof": "root_transfer_proof.txt", "historical_novelty": "unresolved; composition of known logarithm and exponential in DIFFERENT arithmetic algebras",
              "counts_as_verified_new_operator": False, "elapsed_seconds": time.monotonic()-started}
    (output/"root_transfer_probe.json").write_text(json.dumps(result,indent=2)+"\n")
    print(f"Uniform certificate passed={result['uniform_nonzero_correction_Re_s_gt_half_proved']}; bounds={[x['total_decimal_diagnostic'] for x in certificates]}")
    print(f"Saved {output/'root_transfer_probe.json'}; elapsed {result['elapsed_seconds']:.1f}s")
    assert checks["all_checks_passed"] and actual==predicted


if __name__=="__main__":
    main()
