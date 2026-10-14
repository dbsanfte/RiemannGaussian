#!/usr/bin/env python3
"""Search generic arithmetic programs on numerically inferred zeta coefficients.

Run after both passes of zeta_data.py, using the project's existing .venv.
The learner sees coefficient estimates, not arithmetic identities or primes.
Its seed profiles are 1, n, log(n), 1/log(n) (zero at n=1), and delta(n=1).
Two rounds use generic index kernels, matrix inverses, products, and scales.
After direct rule fitting, implicit relations between measured profiles are
tested too. A profile match is not identification of an operator on all inputs.
"""

from __future__ import annotations

import argparse
import itertools
import json
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import numpy as np

from search import cost as operator_cost
from search import inverse_kernel, kernel, make_dictionary, render


TOLERANCE = 1e-7
SCALES = (-2, -1, .5, 1, 2)


def decoded(data):
    return {name: np.array([complex(float(real), float(imag)) for real, imag in entries])
            for name, entries in data["coefficients"].items()}


def mismatch(expected, prediction):
    return float(np.max(np.abs(expected - prediction) / np.maximum(1, np.abs(expected))))


def program_cost(program):
    kind = program["kind"]
    if kind == "seed":
        return 1
    if kind == "linear":
        return 1 + operator_cost(program["operator"]) + program_cost(program["arg"])
    if kind == "scale":
        return 1 + program_cost(program["arg"])
    return 1 + program_cost(program["left"]) + program_cost(program["right"]) + (
        operator_cost(program["operator"]) if kind == "bilinear" else 0)


def rule_text(program):
    kind = program["kind"]
    if kind == "seed":
        return {"one": "1", "index": "n", "log": "log(n)",
                "invlog": "1/log(n), with 0 at n=1", "unit": "[n=1]"}[program["name"]]
    if kind == "linear":
        return f"({render(program['operator'], 1)})(a <- {rule_text(program['arg'])})"
    if kind == "bilinear":
        return f"({render(program['operator'], 2)})(a <- {rule_text(program['left'])}, b <- {rule_text(program['right'])})"
    if kind == "scale":
        return f"{program['factor']} * ({rule_text(program['arg'])})"
    return f"({rule_text(program['left'])}) * ({rule_text(program['right'])}) pointwise"


@lru_cache(maxsize=None)
def numeric_kernel(serialized, size, arity):
    return np.array(kernel(json.loads(serialized), arity, size, size), dtype=float).reshape(
        (size, size) if arity == 1 else (size, size, size))


@lru_cache(maxsize=None)
def profile(serialized, size):
    program = json.loads(serialized)
    kind = program["kind"]
    if kind == "seed":
        indices = np.arange(1, size + 1, dtype=float)
        if program["name"] == "one":
            return np.ones(size)
        if program["name"] == "index":
            return indices
        if program["name"] == "log":
            return np.log(indices)
        if program["name"] == "invlog":
            return np.r_[0, 1 / np.log(indices[1:])]
        return np.r_[1, np.zeros(size - 1)]
    if kind == "linear":
        return numeric_kernel(json.dumps(program["operator"], sort_keys=True), size, 1) @ profile(
            json.dumps(program["arg"], sort_keys=True), size)
    if kind == "scale":
        return program["factor"] * profile(json.dumps(program["arg"], sort_keys=True), size)
    left = profile(json.dumps(program["left"], sort_keys=True), size)
    right = profile(json.dumps(program["right"], sort_keys=True), size)
    if kind == "pointwise":
        return left * right
    return np.einsum("nij,i,j->n", numeric_kernel(
        json.dumps(program["operator"], sort_keys=True), size, 2), left, right)


def operators(size):
    unary = make_dictionary(1, size, size, multiply=True)
    extended = []
    for program, entries in unary:
        extended.append(program)
        try:
            inverse_kernel(entries, size)
        except ValueError:
            continue
        extended.append({"kind": "inverse", "operand": program})
    binary = [program for program, _ in make_dictionary(2, size, size, multiply=True)]
    return sorted(extended, key=operator_cost), binary


def generated(seeds, unary, binary):
    yield from seeds
    for arg in seeds:
        for operator in unary:
            yield {"kind": "linear", "operator": operator, "arg": arg}
    for left, right in itertools.product(seeds, repeat=2):
        yield {"kind": "pointwise", "left": left, "right": right}
        for operator in binary:
            yield {"kind": "bilinear", "operator": operator, "left": left, "right": right}


def direct_search(observed):
    size = len(next(iter(observed.values())))
    unary, binary = operators(size)
    seeds = [{"kind": "seed", "name": name} for name in ("one", "index", "log", "invlog", "unit")]
    best, checked, seen = {}, 0, set()
    for round_index in range(2):
        for raw_program in generated(seeds, unary, binary):
            raw_key = json.dumps(raw_program, sort_keys=True)
            if raw_key in seen:
                continue
            seen.add(raw_key)
            raw_values = profile(raw_key, size)
            for scale in SCALES:
                checked += 1
                program = raw_program if scale == 1 else {
                    "kind": "scale", "factor": scale, "arg": raw_program}
                values = scale * raw_values
                complexity = program_cost(program)
                for name, target in observed.items():
                    error = mismatch(target, values)
                    exact_fit = error < TOLERANCE
                    candidate = {"program": program, "rule": rule_text(program), "cost": complexity,
                                 "training_error": error, "training_match": exact_fit,
                                 "round": round_index + 1}
                    previous = best.get(name)
                    ranking = (not exact_fit, complexity if exact_fit else error,
                               error if exact_fit else complexity)
                    if previous is None or ranking < previous["ranking"]:
                        best[name] = {**candidate, "ranking": ranking}
        if round_index == 0:
            # Only matched programs can supply new building blocks. Held-out
            # coefficients play no role in either discovery round.
            new_keys = {json.dumps(seed, sort_keys=True) for seed in seeds}
            for candidate in best.values():
                key = json.dumps(candidate["program"], sort_keys=True)
                if candidate["training_match"] and key not in new_keys:
                    seeds.append(candidate["program"])
                    new_keys.add(key)
        print(f"Arithmetic search round {round_index + 1}: {checked} programs checked", flush=True)
    for candidate in best.values():
        candidate.pop("ranking")
    return best, checked, binary


def implicit_search(discovery, validation, binary):
    size = len(next(iter(discovery.values())))
    larger = len(next(iter(validation.values())))
    train = {**discovery, "unit_series": np.r_[1, np.zeros(size - 1)]}
    held = {**validation, "unit_series": np.r_[1, np.zeros(larger - 1)]}
    matches, checked = [], 0
    # Input order is retained because the grammar includes noncommutative maps.
    # Exact duplicate relations are eliminated below.
    for operator in binary:
        tensor = numeric_kernel(json.dumps(operator, sort_keys=True), size, 2)
        for left, right in itertools.product(train, repeat=2):
            values = np.einsum("nij,i,j->n", tensor, train[left], train[right])
            for output, target in train.items():
                checked += 1
                if "unit_series" in (left, right) and output in (left, right):
                    continue
                error = mismatch(target, values)
                if error >= TOLERANCE:
                    continue
                tensor_large = numeric_kernel(json.dumps(operator, sort_keys=True), larger, 2)
                prediction = np.einsum("nij,i,j->n", tensor_large, held[left], held[right])
                validation_error = mismatch(held[output], prediction)
                if validation_error < TOLERANCE:
                    matches.append({"operator": operator, "rule": render(operator, 2),
                                    "left": left, "right": right, "output": output,
                                    "training_error": error, "validation_error": validation_error})
    unique = {}
    for relation in matches:
        pair = tuple(sorted((relation["left"], relation["right"])))
        key = (relation["rule"], pair, relation["output"])
        unique.setdefault(key, relation)
    return list(unique.values()), checked


def backend_check():
    """Compare raw zeta values with FLINT/Arb complex ball arithmetic."""
    import flint

    mp.mp.dps = 160
    flint.ctx.prec = 600
    points = [("0.23", "7.1"), ("0.5", "14.13472514173469"),
              ("0.71", "23.4"), ("-0.4", "51.7"), ("1.3", "87.2"),
              ("0.37", "151.3"), ("28", "731.23"), ("50", "1721.6")]
    checks = []
    for real, imag in points:
        s = mp.mpc(real, imag)
        estimate = mp.zeta(s)
        ball = flint.acb(real, imag).zeta()
        rounded = flint.acb(mp.nstr(mp.re(estimate), 155), mp.nstr(mp.im(estimate), 155))
        bound = (ball - rounded).abs_upper()
        passed = bool(bound < flint.arb("1e-140"))
        checks.append({"s": [real, imag], "difference_absolute_upper_bound": str(bound),
                       "below_1e_minus_140": passed})
    return {"mpmath_decimal_digits": 160, "flint_bits": 600, "checks": checks,
            "all_passed": all(check["below_1e_minus_140"] for check in checks)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "zeta-results")
    args = parser.parse_args()
    discovery_data = json.loads((args.output_dir / "coefficients_discovery.json").read_text())
    validation_data = json.loads((args.output_dir / "coefficients_validation.json").read_text())
    discovery, validation = decoded(discovery_data), decoded(validation_data)
    agreement = {name: mismatch(discovery[name], validation[name][:len(discovery[name])])
                 for name in discovery}
    print(f"Cross-cutoff reconstruction disagreement: {max(agreement.values()):.3e}", flush=True)
    if max(agreement.values()) >= TOLERANCE:
        raise SystemExit("Coefficient estimates are not stable enough for this rule search")
    direct, checked, binary = direct_search(discovery)
    for name, candidate in direct.items():
        prediction = profile(json.dumps(candidate["program"], sort_keys=True), len(validation[name]))
        candidate["validation_error"] = mismatch(validation[name], prediction)
        candidate["accepted"] = candidate["training_match"] and candidate["validation_error"] < TOLERANCE
    implicit, implicit_checked = implicit_search(discovery, validation, binary)
    backend = backend_check()
    result = {"scope": "Dirichlet coefficient profiles, not full operator identification",
              "grammar": {"seed_profiles": ["1", "n", "log(n)", "1/log(n), zero at 1", "delta_1"],
                          "index_operations": ["+", "-", "*"], "comparisons": ["=", "<="],
                          "bounded_auxiliary_sum": "1..n", "matrix_inverse": True,
                          "rounds": 2, "pointwise_product": True, "scales": SCALES},
              "tolerance": TOLERANCE, "cross_cutoff_disagreement": agreement,
              "direct_programs_checked": checked, "direct": direct,
              "implicit_relations_checked": implicit_checked, "implicit": implicit,
              "independent_backend": backend}
    (args.output_dir / "arithmetic_search.json").write_text(json.dumps(result, indent=2) + "\n")
    lines = ["Arithmetic search on measured zeta coefficient profiles", "",
             f"Direct programs checked: {checked}", f"Implicit relations checked: {implicit_checked}",
             f"Cross-cutoff coefficient discrepancy: {max(agreement.values()):.3e}", ""]
    for name, candidate in direct.items():
        lines += [f"{name}: {'ACCEPT' if candidate['accepted'] else 'NO MATCH'}",
                  f"  Rule: {candidate['rule']}",
                  f"  Training error: {candidate['training_error']:.3e}",
                  f"  Held-out coefficient error: {candidate['validation_error']:.3e}"]
    lines += ["", "Implicit relations surviving larger coefficients:"]
    for relation in implicit:
        lines.append(f"  ({relation['left']}, {relation['right']}) -> {relation['output']}: {relation['rule']}")
    lines += ["", f"Independent mpmath versus FLINT/Arb checks: {sum(check['below_1e_minus_140'] for check in backend['checks'])}/8",
              "Matches are finite evidence in this grammar. Arithmetic formulas were not used as input.",
              "A single coefficient profile does not identify an operator on arbitrary sequences.",
              "The logarithm and square root use their branches near zeta(s)=1 in the fitting region."]
    report = "\n".join(lines) + "\n"
    (args.output_dir / "arithmetic_report.txt").write_text(report)
    print(report)
    if not backend["all_passed"]:
        raise SystemExit("Independent numerical evaluation check failed")


if __name__ == "__main__":
    main()
