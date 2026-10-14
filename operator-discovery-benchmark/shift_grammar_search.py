#!/usr/bin/env python3
"""Find parameterized coefficient operators with richer index rules.

Exact training data come from root programs already reconstructed from actual
zeta data and proved correct. The learner receives anonymous sequences and a
parameter measured at index 2. It does not receive prime factorizations,
Euler-factor coefficient formulae, or a target recurrence. The new index
grammar explicitly includes bounded divisibility counts, floor and remainder.
"""

from __future__ import annotations

import itertools
import json
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd, lcm
from pathlib import Path
import time

import mpmath as mp
import sympy as sp

from exact_arithmetic import factorization, normalized_power, sequence


@lru_cache(maxsize=None)
def bounded_divisibility_count(n, base):
    # Composite bases are allowed. The learner is not given a primality test.
    count, power = 0, base
    while power <= n:
        count += int(n % power == 0)
        power *= base
    return count


def index_maps():
    for multiplier in range(2, 13):
        yield {"kind": "affine", "multiplier": multiplier, "offset": 0}
    for offset in range(1, 9):
        yield {"kind": "affine", "multiplier": 1, "offset": offset}
    for multiplier in range(2, 9):
        for offset in (-1, 1, 2):
            yield {"kind": "affine", "multiplier": multiplier, "offset": offset}
    for divisor in range(2, 9):
        for kind in ("floor", "remainder", "block_start", "gcd"):
            yield {"kind": kind, "divisor": divisor}


def mapped_index(program, n):
    kind = program["kind"]
    if kind == "affine":
        return program["multiplier"] * n + program["offset"]
    divisor = program["divisor"]
    if kind == "floor":
        return n // divisor + 1
    if kind == "remainder":
        return n % divisor + 1
    if kind == "block_start":
        return divisor * (n // divisor) + 1
    if kind == "gcd":
        return gcd(n, divisor)
    raise ValueError(kind)


def weight_libraries():
    for base in range(2, 9):
        yield ("alpha", "n", f"v{base}")
    for left, right in itertools.combinations(range(2, 9), 2):
        yield ("alpha", f"v{left}", f"v{right}")


def monomials(variables, degree=2):
    return [powers for powers in itertools.product(range(degree + 1), repeat=len(variables))
            if sum(powers) <= degree]


def monomial_value(variables, powers, n, parameter):
    result = Q(1)
    for variable, power in zip(variables, powers):
        if variable == "alpha":
            value = parameter
        elif variable == "n":
            value = n
        else:
            value = bounded_divisibility_count(n, int(variable[1:]))
        result *= value ** power
    return result


def normalize_vector(vector):
    denominator = lcm(*(int(x.q) for x in vector))
    integers = [int(x * denominator) for x in vector]
    divisor = 0
    for value in integers:
        divisor = gcd(divisor, abs(value))
    integers = [value // divisor for value in integers]
    if next(value for value in integers if value) < 0:
        integers = [-value for value in integers]
    return integers


def polynomial_text(variables, powers, coefficients):
    symbols = [sp.Symbol(variable) for variable in variables]
    return str(sp.expand(sum(coefficient * sp.prod(symbol ** power for symbol, power in zip(symbols, exponent))
                             for exponent, coefficient in zip(powers, coefficients))))


def training_matrix(mapping, variables, powers, profiles, indices):
    rows = []
    for parameter, values in profiles.items():
        for n in indices:
            weights = [monomial_value(variables, exponent, n, parameter) for exponent in powers]
            target = values[mapped_index(mapping, n)]
            source = values[n]
            rows.append([sp.Rational(value.numerator, value.denominator)
                         for value in [*(weight * target for weight in weights),
                                       *(weight * source for weight in weights)]])
    return sp.Matrix(rows)


def evaluate_relation(candidate, profiles, indices):
    variables, powers = candidate["variables"], candidate["monomials"]
    split = len(powers)
    coefficients = candidate["coefficients"]
    for parameter, values in profiles.items():
        for n in indices:
            weights = [monomial_value(variables, exponent, n, parameter) for exponent in powers]
            left = sum((coefficient * weight for coefficient, weight in zip(coefficients[:split], weights)), Q(0))
            right = sum((coefficient * weight for coefficient, weight in zip(coefficients[split:], weights)), Q(0))
            residue = left * values[mapped_index(candidate["index_map"], n)] + right * values[n]
            if residue:
                return {"passed": False, "first_counterexample": {
                    "parameter": str(parameter), "n": n, "residue": str(residue)}}
    return {"passed": True, "first_counterexample": None}


def proof_classification(candidate):
    """Sound sufficient proof recognizer; discovery does not use this rule."""
    mapping = candidate["index_map"]
    if mapping["kind"] != "affine" or mapping["offset"] or mapping["multiplier"] < 2:
        return {"status": "universal_proof_pending", "counts_as_new": False}
    bases = [int(variable[1:]) for variable in candidate["variables"] if variable.startswith("v")]
    alpha = sp.Symbol("alpha")
    symbols = {variable: sp.Symbol(variable) for variable in candidate["variables"]}
    def polynomial(coefficients):
        return sp.expand(sum(coefficient * sp.prod(symbols[var] ** power for var, power in
                                                  zip(candidate["variables"], exponent))
                             for exponent, coefficient in zip(candidate["monomials"], coefficients)))
    left = polynomial(candidate["coefficients"][:len(candidate["monomials"])])
    right = polynomial(candidate["coefficients"][len(candidate["monomials"]):])
    numerator, denominator = sp.Integer(1), sp.Integer(1)
    for prime, degree in factorization(mapping["multiplier"]).items():
        v = sp.Symbol(f"v{prime}")
        for j in range(degree):
            numerator *= v + alpha + j
            denominator *= v + j + 1
    cross = sp.expand(left * numerator + right * denominator)
    proved = cross == 0
    remainder_certificates = []
    if not proved:
        # If b=p**k, the observed bounded count is floor(v_p(n)/k).
        # Enumerate the FINITE remainders; the quotient remains a symbolic
        # indeterminate. This proves all exponents, rather than another cutoff.
        periods = {}
        power_counts = {}
        for base in bases:
            factors = factorization(base)
            if len(factors) == 1:
                prime, exponent = next(iter(factors.items()))
                power_counts[base] = (prime, exponent)
                periods[prime] = lcm(periods.get(prime, 1), exponent)
        branches = list(itertools.product(*(range(period) for period in periods.values())))
        if len(branches) <= 64:
            for remainders in branches:
                substitutions = {}
                for (prime, period), remainder in zip(periods.items(), remainders):
                    quotient = sp.Symbol(f"quotient_{prime}")
                    substitutions[sp.Symbol(f"v{prime}")] = period * quotient + remainder
                    for base, (p, exponent) in power_counts.items():
                        if p == prime:
                            substitutions[sp.Symbol(f"v{base}")] = period // exponent * quotient + remainder // exponent
                reduced = sp.expand(cross.subs(substitutions, simultaneous=True))
                remainder_certificates.append({"remainders": list(remainders), "zero_polynomial": reduced == 0})
            proved = bool(remainder_certificates) and all(x["zero_polynomial"] for x in remainder_certificates)
    return {"status": "proved_classical_root_lowering" if proved else "universal_proof_pending",
            "proof": "shift_operator_proofs.txt" if proved else None,
            "canonical_numerator": str(sp.expand(numerator)),
            "canonical_denominator": str(sp.expand(denominator)),
            "prime_power_remainder_branches": remainder_certificates,
            "historical_novelty": "Known Euler-factor recurrence and prime-basic derivation framework" if proved else "unresolved",
            "counts_as_new": False}


def numerical_zeta_check(candidate):
    """Use held-out ACTUAL zeta coefficient estimates where indices fit."""
    source = Path(__file__).resolve().parent / "root-results" / "root_probe.json"
    observed = json.loads(source.read_text())["coefficients"]["validation"]
    mp.mp.dps = 60
    maximum, checks = mp.mpf(0), 0
    split = len(candidate["monomials"])
    for values in observed.values():
        data = [mp.mpc(0)] + [mp.mpc(real, imag) for real, imag in values]
        parameter = data[2]
        for n in range(1, len(data)):
            index = mapped_index(candidate["index_map"], n)
            if index >= len(data):
                continue
            weights = [monomial_value(candidate["variables"], exponent, n, parameter)
                       for exponent in candidate["monomials"]]
            left = sum(c * w for c, w in zip(candidate["coefficients"][:split], weights))
            right = sum(c * w for c, w in zip(candidate["coefficients"][split:], weights))
            numerator = abs(left * data[index] + right * data[n])
            residual = numerator / max(1, abs(left * data[index]), abs(right * data[n]))
            maximum = max(maximum, residual)
            checks += 1
    return {"actual_zeta_coefficient_checks": checks, "maximum_normalized_residual": mp.nstr(maximum, 12),
            "passed": bool(checks and maximum < mp.mpf("1e-12")),
            "empirical_only_not_a_tail_enclosure": True}


def main():
    started = time.monotonic()
    output = Path(__file__).resolve().parent / "shift-results"
    output.mkdir(parents=True, exist_ok=True)
    print("Generating exact profiles from the previously discovered generic root programs", flush=True)
    cutoff = 2048
    parameters = [Q(1, q) for q in range(2, 8)]
    fresh_parameters = [Q(-1, 2), Q(2, 3), Q(3, 2), Q(5, 7)]
    profiles = {parameter: normalized_power(sequence([1] * cutoff), parameter)
                for parameter in parameters + fresh_parameters}
    train = {profiles[parameter][2]: profiles[parameter] for parameter in parameters}
    held = {profiles[parameter][2]: profiles[parameter] for parameter in fresh_parameters}
    mappings = list(index_maps())
    libraries = list(weight_libraries())
    candidates, survivors, checked, duplicate = [], [], 0, set()
    for mapping_index, mapping in enumerate(mappings):
        for variables in libraries:
            powers = monomials(variables)
            matrix = training_matrix(mapping, variables, powers, train, range(1, 17))
            checked += 1
            for vector in matrix.nullspace():
                coefficients = normalize_vector(vector)
                split = len(powers)
                if not any(coefficients[:split]) or not any(coefficients[split:]):
                    continue
                if sum(bool(x) for x in coefficients) > 12:
                    continue
                left = polynomial_text(variables, powers, coefficients[:split])
                right = polynomial_text(variables, powers, coefficients[split:])
                key = (json.dumps(mapping, sort_keys=True), left, right)
                if key in duplicate:
                    continue
                duplicate.add(key)
                candidate = {"index_map": mapping, "variables": variables, "monomials": powers,
                             "coefficients": coefficients, "shift_weight": left, "diagonal_weight": right,
                             "nonzero_terms": sum(bool(x) for x in coefficients)}
                validation = evaluate_relation(candidate, held, range(17, 161))
                candidates.append({**candidate, "validation": validation})
                if validation["passed"]:
                    survivor = {**candidate, "validation": validation,
                                "proof_audit": proof_classification(candidate)}
                    survivor["actual_zeta_validation"] = numerical_zeta_check(candidate)
                    survivors.append(survivor)
        if (mapping_index + 1) % 8 == 0:
            print(f"Index maps {mapping_index + 1}/{len(mappings)}; {len(candidates)} fits; {len(survivors)} survivors", flush=True)
    result = {"training_indices": [1, 16], "validation_indices": [17, 160],
              "training_parameters_measured_at_index_2": [str(x) for x in parameters],
              "fresh_validation_parameters": [str(x) for x in fresh_parameters],
              "exact_profile_cutoff": cutoff,
              "source": "Generic coefficient-local rational power programs reconstructed from numerical zeta, then proved correct",
              "new_primitives": ["affine index maps", "floor/remainder/block/gcd index maps", "bounded divisibility counts for any integer base", "polynomial weights in the observed parameter and two index features"],
              "models_checked": checked, "training_candidates": candidates,
              "surviving_candidates": survivors, "verified_new_operators": [],
              "elapsed_seconds": time.monotonic() - started}
    (output / "shift_search.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Saved {output / 'shift_search.json'}; elapsed {result['elapsed_seconds']:.1f}s", flush=True)


if __name__ == "__main__":
    main()
