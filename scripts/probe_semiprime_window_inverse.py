#!/usr/bin/env python3
"""Replay the N-only window with an explicit counted Euclidean inverse.

Keep all frozen construction and recovery sources intact. Replace only the
one modular inverse inside the prior counted builder, and include that
implementation and its reports in the timer. Arithmetic counts and operand
bounds are not a full bit certificate or universal one-sixth guarantee.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-window-construction-audit.json"
CONSTRUCTION = runpy.run_path(str(ROOT/"scripts/probe_semiprime_window_construction.py"))
PARENT = CONSTRUCTION["PARENT"]
REPLAY_ID = 202610031701


def counted_inverse(n, a):
    r0, r1, c0, c1 = n, a % n, 0, 1 % n
    trace = []
    steps = quotients = multiplications = 0
    reductions = 2
    max_product_bits = max_padded_bits = 0
    while r1:
        quotient = r0//r1
        remainder = r0 % r1
        product = quotient*c1
        product_residue = product % n
        padded = c0+n
        next_coefficient = (padded-product_residue) % n
        trace.append(dict(first=r0, second=r1, first_coefficient=c0,
                          second_coefficient=c1, quotient=quotient,
                          remainder=remainder, product=product,
                          product_residue=product_residue, padded=padded,
                          next_coefficient=next_coefficient))
        max_product_bits = max(max_product_bits, product.bit_length())
        max_padded_bits = max(max_padded_bits, padded.bit_length())
        steps += 1
        quotients += 1
        multiplications += 1
        reductions += 3
        r0, r1, c0, c1 = r1, remainder, c1, next_coefficient
    return dict(gcd=r0, coefficient=c0, steps=steps, quotients=quotients,
                multiplications=multiplications, reductions=reductions,
                additions=steps, subtractions=steps, zero_tests=steps+1,
                initial_reductions=2, trace=trace,
                max_product_bits=max_product_bits, max_padded_bits=max_padded_bits)


def check_inverse(n, a, report):
    assert n > 0
    assert report["gcd"] == math.gcd(n, a)
    assert 0 <= report["coefficient"] < n
    assert report["coefficient"]*a % n == report["gcd"] % n
    assert report["steps"] <= 2*n.bit_length()
    assert report["quotients"] == report["multiplications"] == report["steps"]
    assert report["reductions"] == 3*report["steps"]+2
    assert len(report["trace"]) == report["steps"]
    state = (n, a % n, 0, 1 % n)
    for frame in report["trace"]:
        assert state == (frame["first"], frame["second"],
                         frame["first_coefficient"], frame["second_coefficient"])
        assert frame["first"] <= n and 0 < frame["second"] <= n
        assert frame["first_coefficient"] < n and frame["second_coefficient"] < n
        assert frame["quotient"] == frame["first"]//frame["second"] <= n
        assert frame["remainder"] == frame["first"] % frame["second"] < frame["second"]
        assert frame["product"] == frame["quotient"]*frame["second_coefficient"] < n*n
        assert frame["product_residue"] == frame["product"] % n < n
        assert frame["product_residue"] <= frame["padded"]
        assert frame["padded"] == frame["first_coefficient"]+n < 2*n
        assert frame["next_coefficient"] == (frame["padded"]-frame["product_residue"]) % n < n
        assert frame["first_coefficient"]*a % n == frame["first"] % n
        assert frame["second_coefficient"]*a % n == frame["second"] % n
        state = (frame["second"], frame["remainder"],
                 frame["second_coefficient"], frame["next_coefficient"])
    assert state[1] == 0 and state[0] == report["gcd"] and state[2] == report["coefficient"]
    assert report["max_product_bits"] <= 2*n.bit_length()
    assert report["max_padded_bits"] <= n.bit_length()+1
    if report["gcd"] == 1:
        assert report["coefficient"] == pow(a, -1, n)


def public_packet(n):
    scope = CONSTRUCTION["build_source"].__globals__
    previous_pow = scope.get("pow")
    had_pow = "pow" in scope
    reports = []

    def acquired_inverse(a, e, modulus):
        assert e == -1
        report = counted_inverse(modulus, a)
        reports.append(report)
        if report["gcd"] != 1:
            raise ValueError("public active scalar is not invertible")
        return report["coefficient"]

    start = time.perf_counter()
    scope["pow"] = acquired_inverse
    try:
        actual = CONSTRUCTION["public_packet"](n)
        window = actual["parent"]["source"]
        if window is not None:
            assert len(reports) == 1
            inverse = reports[0]
            window["construction"]["inverse"] = inverse
            raw = window["construction"]["arithmetic"]
            total = dict(multiplications=raw["multiplications"]+inverse["multiplications"],
                         reductions=raw["reductions"]+inverse["reductions"],
                         quotients=inverse["quotients"], euclid_steps=inverse["steps"],
                         halvings=raw["halvings"], parity_tests=raw["parity_tests"],
                         inverse_additions=inverse["additions"],
                         inverse_subtractions=inverse["subtractions"],
                         inverse_zero_tests=inverse["zero_tests"], inverse_gcd_tests=1,
                         max_product_bits=max(raw["max_product_bits"], inverse["max_product_bits"]),
                         max_inverse_padded_bits=inverse["max_padded_bits"],
                         inverse_acquisitions=1, opaque_inverse_queries=0,
                         centre_square_roots=raw["centre_square_roots"], input_bits=raw["input_bits"])
            window["construction"]["initial_arithmetic"] = total
        else:
            assert not reports
    finally:
        if had_pow:
            scope["pow"] = previous_pow
        else:
            scope.pop("pow", None)
    actual["elapsed_ms"] = 1000*(time.perf_counter()-start)
    if window is not None:
        check_inverse(window["N"], window["active_base"], inverse)
        total = window["construction"]["initial_arithmetic"]
        assert total["multiplications"] <= 4*actual["width"]+6*n.bit_length()+2
        assert total["reductions"] <= 8*actual["width"]+12*n.bit_length()+7
        assert total["quotients"] <= 2*n.bit_length()
        assert total["halvings"] <= 2*n.bit_length()+1
        assert total["max_product_bits"] <= 2*n.bit_length()
    return actual


def validate_inverses():
    cases = units = 0
    fibonacci = []
    for n in range(1, 97):
        for a in range(3*n+1):
            report = counted_inverse(n, a)
            check_inverse(n, a, report)
            cases += 1
            units += int(report["gcd"] == 1)
    a, n = 1, 2
    for index in range(1, 257):
        if index % 8 == 0:
            report = counted_inverse(n, a)
            check_inverse(n, a, report)
            fibonacci.append(dict(index=index, N=n, a=a, input_bits=n.bit_length(),
                                  steps=report["steps"], quotients=report["quotients"],
                                  reductions=report["reductions"],
                                  max_product_bits=report["max_product_bits"],
                                  max_padded_bits=report["max_padded_bits"]))
        a, n = n, n+a
    return dict(inverse_cases=cases, unit_cases=units, nonunit_cases=cases-units,
                fibonacci_cases=len(fibonacci), fibonacci_rows=fibonacci)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeWindowInverse.lean",
                  "scripts/CheckSemiprimeWindowInverse.lean",
                  "scripts/probe_semiprime_window_inverse.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    primitives = validate_inverses()
    prior = json.loads((ROOT/PARENT_AUDIT).read_text())
    counts, squares = Counter(), 0
    primes = list(primerange(2, 200))
    for i, p in enumerate(primes):
        for q in primes[i:]:
            actual = public_packet(p*q)
            PARENT["check_packet"](actual, p, q)
            counts[actual["status"]] += 1
            squares += int(p == q)
    populations, initial_rows = {}, []
    for name in ("inputs", "controls", "positive_controls", "negative_controls", "wrapped_controls"):
        population = []
        for previous in prior[name]:
            p, q = previous["reference_p"], previous["reference_q"]
            actual = public_packet(p*q)
            PARENT["check_packet"](actual, p, q)
            assert (actual["factor"], actual["status"]) == (previous["factor"], previous["status"])
            window, old_window = actual["parent"]["source"], previous["parent"]["source"]
            if window is not None:
                for key in ("active_base", "centre", "target", "inverse_step", "babies", "giants",
                            "collision", "candidate", "factor"):
                    assert json.dumps(window[key]) == json.dumps(old_window[key]), key
                assert window["construction"]["arithmetic"] == old_window["construction"]["arithmetic"]
                initial_rows.append(dict(original_N=p*q, leaf_N=window["N"], leaf_width=window["width"],
                                         **window["construction"]["initial_arithmetic"]))
            actual.update(reference_p=p, reference_q=q)
            if "regime" in previous:
                actual["regime"] = previous["regime"]
            population.append(actual)
        populations[name] = population
    assert len(initial_rows) == 5
    result = dict(replay_id=REPLAY_ID, scope="N-only window initialization with counted Euclidean inverse",
                  one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False,
                  is_bit_complexity_certificate=False, source_sha256=sources,
                  validation=dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
                                  status_counts=dict(counts), outcomes_preserved=True,
                                  initialised_sources=len(initial_rows), **primitives),
                  initial_rows=initial_rows,
                  summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
                  timing_protocol="Scoped replacement of only the inverse in the frozen counted builder. The complete preceding N-only pipeline, counted Euclid, raw powers and walks, sorted lookup, proper residue continuation, report retention and transport are timed. The native Python inverse is used only for independent validation after timing. Factors, local orders, offsets, trace invariant checks and frozen source comparisons are outside timing. Every prior source hash is retained.",
                  limitations="The inverse now has explicit quotient, multiplication, reduction, addition, subtraction and guard counts, with bounded intermediate products. This is not an implemented bit certificate for the arithmetic primitives, square roots, sorting, polynomial backend, preceding descent or transport. There is no new universal offset coverage, factoring exponent, unbiased corpus, timing scaling claim or tuned software comparison. The prior 61-bit negative still survives.",
                  **populations)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(validation={k:v for k,v in result["validation"].items() if k != "fibonacci_rows"},
                          source_pins=len(sources), summary=result["summary"], initial_rows=initial_rows,
                          surviving_negative=populations["negative_controls"][0]["N"],
                          one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()
