#!/usr/bin/env python3
"""Extend zeta discovery to exact roots and exponent-digit arithmetic.

The first stage fits a label-blind rational-power grammar to coefficients
reconstructed from stored zeta observations. The second stage studies EXACT
denominators of the accepted root programs. Prime exponents, quotient,
remainder, digit sums and factorial valuations are explicit new primitives.
Finite tests are recorded separately from universal mathematical proofs.
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
import time
from fractions import Fraction as Q
from pathlib import Path

import mpmath as mp

from exact_arithmetic import (add, convolve, digit_sum, factorial_valuation,
                              factorization, formal_exp, formal_log,
                              integer_power, normalized_power,
                              recursive_square_root, scale, sequence, unit,
                              valuation, weighted_convolution)


ROOT_ORDERS = (2, 3, 4, 5, 6, 7)


def encoded(value, digits=30):
    return [mp.nstr(mp.re(value), digits), mp.nstr(mp.im(value), digits)]


def rational_number(value):
    return mp.mpf(value.numerator) / value.denominator


def reconstruct_roots(path):
    """Reuse raw observations, changing only the measured transforms."""
    source = json.loads(path.read_text())
    config = source["config"]
    mp.mp.dps = config["digits"]
    size = config["fit_size"]
    logs = [mp.log(n) for n in range(1, size + 1)]
    design = mp.matrix(config["sample_size"], size)
    measured = mp.matrix(config["sample_size"], len(ROOT_ORDERS))
    for row, sample in enumerate(source["samples"]):
        sigma, height = map(mp.mpf, sample["s"])
        z = mp.mpc(*sample["values"]["z"])
        for column, log_n in enumerate(logs):
            design[row, column] = mp.exp(-mp.j * height * log_n)
        for column, order in enumerate(ROOT_ORDERS):
            # These samples are deep in Re(s)>1, near zeta=1. The principal
            # numerical power there agrees with the normalized Euler branch.
            measured[row, column] = mp.exp(mp.log(z) / order)
    fitted = (design.H * design) ** -1 * design.H * measured
    return {f"anonymous_{column:02d}": [
        fitted[n - 1, column] * mp.exp(config["sigma"] * logs[n - 1])
        for n in range(1, config["retained"] + 1)]
        for column in range(len(ROOT_ORDERS))}, config


def exact_checks():
    rng = random.Random(2026100603)
    records = []
    for size in (16, 33, 65, 127):
        values = sequence([1] + [Q(rng.randint(-5, 5), rng.randint(1, 7))
                                  for _ in range(size - 1)])
        zero_values = list(values)
        zero_values[1] = Q(0)
        square_root = recursive_square_root(values)
        laws = {
            "independent_square_root_equals_binomial_program":
                square_root == normalized_power(values, Q(1, 2)),
            "square_of_recursive_root": convolve(square_root, square_root) == values,
            "exp_log": formal_exp(formal_log(values)) == values,
            "log_exp": formal_log(formal_exp(zero_values)) == zero_values,
        }
        for order in ROOT_ORDERS:
            root = normalized_power(values, Q(1, order))
            laws[f"root_order_{order}"] = integer_power(root, order) == values
        for left, right in ((Q(-2, 3), Q(5, 7)), (Q(1, 2), Q(1, 3)),
                            (Q(2), Q(-1)), (Q(0), Q(1))):
            laws[f"power_add_{left}_{right}"] = (
                convolve(normalized_power(values, left), normalized_power(values, right))
                == normalized_power(values, left + right))
            laws[f"power_compose_{left}_{right}"] = (
                normalized_power(normalized_power(values, left), right)
                == normalized_power(values, left * right))
        smaller = size // 2
        laws["prefix_consistency"] = (
            normalized_power(values, Q(1, 3))[:smaller + 1]
            == normalized_power(values[:smaller + 1], Q(1, 3)))
        records.append({"cutoff": size, "laws": laws})
    invalid = sequence([2, 1, 1, 1])
    try:
        normalized_power(invalid, Q(1, 2))
    except ValueError:
        rejected = True
    else:
        rejected = False
    return {"random_input_records": records, "invalid_normalization_rejected": rejected,
            "all_passed": rejected and all(all(record["laws"].values()) for record in records)}


def match_root_grammar(discovery, validation):
    training_size = len(next(iter(discovery.values())))
    validation_size = len(next(iter(validation.values())))
    exponents = sorted({Q(numerator, denominator) for numerator in range(-3, 4)
                        for denominator in range(1, 13)})
    training_one = sequence([1] * training_size)
    held_one = sequence([1] * validation_size)
    output, checked = {}, 0
    predictions = {alpha: normalized_power(training_one, alpha) for alpha in exponents}
    for name, target in discovery.items():
        ranking = []
        for alpha, values in predictions.items():
            checked += 1
            error = max(abs(observed - rational_number(exact))
                        for observed, exact in zip(target, values[1:]))
            ranking.append((error, alpha))
        error, alpha = min(ranking)
        exact_held = normalized_power(held_one, alpha)
        held_error = max(abs(observed - rational_number(exact))
                         for observed, exact in zip(validation[name], exact_held[1:]))
        old_grammar_options = [training_one, unit(training_size),
                               integer_power(training_one, 2),
                               normalized_power(training_one, -1)]
        old_error = min(max(abs(observed - rational_number(exact))
                            for observed, exact in zip(target, candidate[1:]))
                        for candidate in old_grammar_options)
        output[name] = {
            "program": {"kind": "power", "exponent": str(alpha),
                        "arg": {"kind": "input", "name": "zeta_coefficients"}},
            "training_error": mp.nstr(error, 16),
            "validation_error": mp.nstr(held_error, 16),
            "accepted": bool(error < mp.mpf("1e-9") and held_error < mp.mpf("1e-12")),
            "representative_old_grammar_error": mp.nstr(old_error, 12),
            "first_exact_coefficients": [str(value) for value in exact_held[1:17]],
        }
    return output, checked


def local_root_coefficients(order, degree):
    """Independent generic polynomial q-root recursion; no binomial formula.

    The target local series is 1+x+x**2+... . The coefficient of x**e in
    r**q is q*r[e] plus a polynomial in earlier coefficients.
    """
    def polynomial_product(left, right, cutoff):
        result = [Q(0)] * (cutoff + 1)
        for i, a in enumerate(left):
            for j, b in enumerate(right[:cutoff - i + 1]):
                result[i + j] += a * b
        return result

    root = [Q(1)]
    for e in range(1, degree + 1):
        partial = root + [Q(0)]
        powered = [Q(1)]
        for _ in range(order):
            powered = polynomial_product(powered, partial, e)
        root.append((1 - powered[e]) / order)
    return root


def fit_valuation_rule(target, prime, train_degree=8):
    """Search TWO-term rational linear rules; no denominator identity given."""
    exponents = range(1, len(target))
    features = {
        "e": list(exponents),
        "1": [1 for _ in exponents],
        **{f"digit_sum(e,{base})": [digit_sum(e, base) for e in exponents]
           for base in range(2, 8)},
        **{f"v_{base}(e!)": [factorial_valuation(e, base) for e in exponents]
           for base in (2, 3, 5, 7)},
        **{f"floor(e/{base})": [e // base for e in exponents]
           for base in range(2, 8)},
        **{f"e mod {base}": [e % base for e in exponents]
           for base in range(2, 8)},
    }
    matches, checked = [], 0
    y = target[1:]
    for left, right in itertools.combinations(features, 2):
        a, b = features[left], features[right]
        pivots = next(((i, j) for i in range(train_degree) for j in range(i + 1, train_degree)
                       if a[i] * b[j] != a[j] * b[i]), None)
        if pivots is None:
            continue
        i, j = pivots
        determinant = a[i] * b[j] - a[j] * b[i]
        c = Q(y[i] * b[j] - y[j] * b[i], determinant)
        d = Q(a[i] * y[j] - a[j] * y[i], determinant)
        checked += 1
        if not c or not d or max(abs(c), abs(d)) > 8:
            continue
        predicted = [c * x + d * z for x, z in zip(a, b)]
        if predicted[:train_degree] != y[:train_degree]:
            continue
        first_failure = next((e for e, (found, expected) in enumerate(zip(predicted, y), 1)
                              if found != expected), None)
        matches.append({"left": left, "right": right, "coefficients": [str(c), str(d)],
                        "training_degree": train_degree, "held_out_through_degree": len(y),
                        "held_out_passed": first_failure is None,
                        "first_counterexample": first_failure,
                        "rule": f"({c})*{left} + ({d})*{right}"})
    return {"prime": prime, "programs_checked": checked, "training_matches": matches}


def denominator_search():
    # A base-7 floor rule agrees below 7**2 but is false at e=49. Validation
    # must cross that boundary, rather than letting the initial cutoff hide it.
    degree = 96
    results = []
    for order in ROOT_ORDERS:
        local = local_root_coefficients(order, degree)
        for prime in factorization(order):
            values = [valuation(value.denominator, prime) for value in local]
            fitted = fit_valuation_rule(values, prime)
            results.append({"root_order": order, "values": values, **fitted})
    return results


def denominator_degree(n, root_order, prime):
    """INTERPRETED rule, introduced only after empirical rule search."""
    return sum(e * valuation(root_order, prime) + factorial_valuation(e, prime)
               for e in factorization(n).values())


def carry_count(i, j, prime):
    left, right = factorization(i), factorization(j)
    return sum(factorial_valuation(left.get(p, 0) + right.get(p, 0), prime)
               - factorial_valuation(left.get(p, 0), prime)
               - factorial_valuation(right.get(p, 0), prime)
               for p in left.keys() | right.keys())


def carry_operator_checks():
    rng = random.Random(2026100604)
    size = 96
    arrays = [sequence([Q(rng.randint(-3, 3), rng.randint(1, 4)) for _ in range(size)])
              for _ in range(3)]
    records = []
    for prime in (2, 3, 5, 7):
        for parameter in (Q(0), Q(1, 2), Q(1), Q(2), Q(-1)):
            # 0**0=1 retains no-carry factorizations; 0**positive=0.
            def product(left, right):
                return weighted_convolution(left, right,
                                            lambda i, j: parameter ** carry_count(i, j, prime))
            a, b, c = arrays
            associative = product(product(a, b), c) == product(a, product(b, c))
            commutative = product(a, b) == product(b, a)
            has_unit = product(a, unit(size)) == a
            records.append({"base_prime": prime, "parameter": str(parameter),
                            "associative": associative, "commutative": commutative,
                            "identity": has_unit})
    # A tempting overlap kernel fails associativity, despite looking natural.
    def overlap(left, right):
        from math import gcd
        return weighted_convolution(left, right,
                                    lambda i, j: Q(2) ** sum(factorization(gcd(i, j)).values()))
    a, b, c = arrays
    lhs, rhs = overlap(overlap(a, b), c), overlap(a, overlap(b, c))
    failure = next((n for n in range(1, size + 1) if lhs[n] != rhs[n]), None)
    impulse_a, impulse_b, impulse_c = [sequence([0] * 16) for _ in range(3)]
    impulse_a[2], impulse_b[2], impulse_c[4] = Q(1), Q(1), Q(1)
    impulse_left = overlap(overlap(impulse_a, impulse_b), impulse_c)
    impulse_right = overlap(impulse_a, overlap(impulse_b, impulse_c))
    return {"cutoff": size, "carry_family_checks": records,
            "all_family_checks_passed": all(r[law] for r in records
                                             for law in ("associative", "commutative", "identity")),
            "overlap_weight_negative_control": {"rejected": failure is not None,
                                                "first_associativity_counterexample_n": failure,
                                                "left": str(lhs[failure]) if failure else None,
                                                "right": str(rhs[failure]) if failure else None,
                                                "minimal_impulse_example": {
                                                    "inputs": [2, 2, 4], "output_index": 16,
                                                    "left": str(impulse_left[16]),
                                                    "right": str(impulse_right[16])}}}


def analytic_bridge_checks(size=512):
    """Rigorous tail bound plus independent Arb ball containment checks.

    On Re(s)>1, 0<b_(1/q)(n)<=1 implies tail <=N**(1-sigma)/(sigma-1).
    Arb evaluates BOTH the finite coefficient sum and zeta's numerical root.
    The algebraic proof in root_proofs.txt establishes the branch identity;
    this numerical check does not establish it by itself.
    """
    import flint

    flint.ctx.prec = 300
    records = []
    one = sequence([1] * size)
    for order in ROOT_ORDERS:
        coefficients = normalized_power(one, Q(1, order))
        for real, imag in ((4, "0"), (4, "17.3"), (6, "109.7")):
            s = flint.acb(str(real), imag)
            finite = flint.acb(0)
            for n in range(1, size + 1):
                coefficient = flint.arb(coefficients[n].numerator) / coefficients[n].denominator
                finite += coefficient * (-s * flint.arb(n).log()).exp()
            root = (s.zeta().log() / order).exp()
            tail = flint.arb(size) ** (1 - real) / (real - 1)
            difference = (finite - root).abs_upper()
            records.append({"order": order, "s": [str(real), imag], "cutoff": size,
                            "difference_upper_ball": str(difference), "tail_bound_ball": str(tail),
                            "within_proved_tail_bound": bool(difference < tail)})
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "root-results")
    parser.add_argument("--exact-only", action="store_true")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    print("Checking exact recursive grammar on unrelated rational inputs", flush=True)
    result = {"exact_grammar": exact_checks()}
    if not args.exact_only:
        source = Path(__file__).resolve().parent / "zeta-results"
        print("Reconstructing anonymous root profiles from discovery observations", flush=True)
        discovery, discovery_config = reconstruct_roots(source / "coefficients_discovery.json")
        print("Reconstructing root profiles at independent points and larger cutoff", flush=True)
        validation, validation_config = reconstruct_roots(source / "coefficients_validation.json")
        matches, checked = match_root_grammar(discovery, validation)
        result.update({"coefficients": {
            "discovery": {name: [encoded(value) for value in values]
                          for name, values in discovery.items()},
            "validation": {name: [encoded(value) for value in values]
                           for name, values in validation.items()}},
            "measurement_configs": [discovery_config, validation_config],
            "root_grammar": {"programs_checked": checked, "matches": matches},
            "evaluation_only_order_labels": dict(zip(matches, ROOT_ORDERS))})
    print("Searching exact root-denominator rules with digital index grammar", flush=True)
    result["denominator_search"] = denominator_search()
    print("Testing inferred carry kernels and rejecting overlap-weight control", flush=True)
    result["carry_operators"] = carry_operator_checks()
    print("Checking analytic root bridge with Arb and a proved tail bound", flush=True)
    result["analytic_bridge"] = analytic_bridge_checks()
    result["elapsed_seconds"] = time.monotonic() - started
    destination = args.output_dir / ("root_exact_checks.json" if args.exact_only else "root_probe.json")
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Saved {destination}; elapsed {result['elapsed_seconds']:.1f}s", flush=True)
    assert result["exact_grammar"]["all_passed"]
    assert result["carry_operators"]["all_family_checks_passed"]
    assert result["carry_operators"]["overlap_weight_negative_control"]["rejected"]
    assert all(r["within_proved_tail_bound"] for r in result["analytic_bridge"])
    if not args.exact_only:
        assert all(r["accepted"] for r in result["root_grammar"]["matches"].values())


if __name__ == "__main__":
    main()
