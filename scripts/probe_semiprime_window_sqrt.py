#!/usr/bin/env python3
"""Replay explicit restoring roots and the counted quadratic decoder.

Preserve the complete frozen inverse/construction/recovery chain. Only the
retained window's inverse, centre root, candidate root and candidate gcd use
the counted implementations. Their reports and the full preceding N-only
route are timed. No full bit certificate or universal coverage is claimed.
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
PARENT_AUDIT = "docs/semiprime-window-inverse-audit.json"
INVERSE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_window_inverse.py"))
CONSTRUCTION = INVERSE["CONSTRUCTION"]
PARENT = INVERSE["PARENT"]
REPLAY_ID = 202610031801


def counted_sqrt(n):
    prefixes = []
    prefix = n
    quotients = zero_tests = 0
    while prefix:
        zero_tests += 1
        prefixes.append(prefix)
        prefix //= 4
        quotients += 1
    zero_tests += 1
    root = remainder = 0
    digit_reductions = shifts = additions = subtractions = comparisons = 0
    frames = []
    max_temporary_bits = 0
    for prefix in reversed(prefixes):
        digit = prefix % 4
        expanded = 4*remainder+digit
        trial = 4*root+1
        doubled = 2*root
        odd = trial <= expanded
        child_root, child_remainder = root, remainder
        if odd:
            root = doubled+1
            remainder = expanded-trial
            additions += 1
            subtractions += 1
        else:
            root, remainder = doubled, expanded
        digit_reductions += 1
        shifts += 3
        additions += 2
        comparisons += 1
        max_temporary_bits = max(max_temporary_bits, expanded.bit_length(),
                                 trial.bit_length(), doubled.bit_length(),
                                 root.bit_length(), remainder.bit_length())
        frames.append(dict(input=prefix, child_root=child_root, child_remainder=child_remainder,
                           digit=digit, expanded=expanded, trial=trial, odd=odd,
                           root=root, remainder=remainder))
    return dict(root=root, remainder=remainder, steps=len(frames), quotients=quotients,
                digit_reductions=digit_reductions, shifts=shifts, additions=additions,
                subtractions=subtractions, comparisons=comparisons, zero_tests=zero_tests,
                trace=list(reversed(frames)), max_temporary_bits=max_temporary_bits)


def check_sqrt(n, report):
    assert n >= 0
    assert report["root"] == math.isqrt(n)
    assert report["root"]**2+report["remainder"] == n
    assert report["remainder"] <= 2*report["root"]
    steps = (n.bit_length()+1)//2
    assert report["steps"] == steps <= n.bit_length()
    assert report["quotients"] == report["digit_reductions"] == report["comparisons"] == steps
    assert report["shifts"] == 3*steps
    assert report["additions"] == 2*steps+report["subtractions"]
    assert report["subtractions"] <= steps
    assert report["zero_tests"] == steps+1
    assert len(report["trace"]) == steps
    prefix = n
    for frame in report["trace"]:
        assert frame["input"] == prefix <= n
        child_root = math.isqrt(prefix//4)
        assert frame["child_root"] == child_root <= prefix//4
        assert frame["child_remainder"] == prefix//4-child_root**2 <= prefix//4
        assert frame["digit"] == prefix % 4 < 4
        assert frame["expanded"] == 4*frame["child_remainder"]+frame["digit"] <= prefix
        assert frame["trial"] == 4*child_root+1 <= prefix+1
        assert frame["odd"] == (frame["trial"] <= frame["expanded"])
        assert frame["root"] == 2*child_root+int(frame["odd"]) <= prefix
        assert frame["remainder"] == frame["expanded"]-int(frame["odd"])*frame["trial"] <= prefix
        assert frame["root"]**2+frame["remainder"] == prefix
        assert frame["remainder"] <= 2*frame["root"]
        prefix //= 4
    assert prefix == 0
    if report["trace"]:
        assert (report["trace"][0]["root"], report["trace"][0]["remainder"]) == (
            report["root"], report["remainder"])
    assert report["max_temporary_bits"] <= n.bit_length()+1


def counted_decoder(n, modulus):
    signal = (n+1) % modulus if modulus else n+1
    discriminant = max(signal*signal-4*n, 0)
    square_root = counted_sqrt(discriminant)
    candidate = max(signal-square_root["root"], 0)//2
    gcd_run = INVERSE["counted_inverse"](n, candidate)
    factor = gcd_run["gcd"] if 1 < gcd_run["gcd"] < n else None
    return dict(signal=signal, discriminant=discriminant, square_root=square_root,
                candidate=candidate, gcd_run=gcd_run, factor=factor)


def check_decoder(n, modulus, report):
    signal = (n+1) % modulus if modulus else n+1
    discriminant = max(signal*signal-4*n, 0)
    assert report["signal"] == signal <= n+1
    assert report["discriminant"] == discriminant <= n*n
    candidate = max(signal-math.isqrt(discriminant), 0)//2
    assert report["candidate"] == candidate <= n
    check_sqrt(discriminant, report["square_root"])
    INVERSE["check_inverse"](n, candidate, report["gcd_run"])
    gcd = math.gcd(n, candidate)
    assert report["factor"] == (gcd if 1 < gcd < n else None)
    assert report["square_root"]["steps"] <= 2*n.bit_length()
    assert (signal*signal).bit_length() <= 2*n.bit_length()+1
    assert report["gcd_run"]["quotients"] <= 2*n.bit_length()
    assert report["gcd_run"]["reductions"] <= 6*n.bit_length()+2


def public_packet(n):
    scope = CONSTRUCTION["build_source"].__globals__
    previous_math = scope["math"]
    previous_pow, had_pow = scope.get("pow"), "pow" in scope
    inverse_reports, root_reports, gcd_reports = [], [], []

    def acquired_inverse(a, e, modulus):
        assert e == -1
        report = INVERSE["counted_inverse"](modulus, a)
        inverse_reports.append(report)
        if report["gcd"] != 1:
            raise ValueError("public active scalar is not invertible")
        return report["coefficient"]

    class ChargedMath:
        def isqrt(self, value):
            report = counted_sqrt(value)
            root_reports.append((value, report))
            return report["root"]

        def gcd(self, modulus, a):
            report = INVERSE["counted_inverse"](modulus, a)
            gcd_reports.append((modulus, a, report))
            return report["gcd"]

        def __getattr__(self, name):
            return getattr(previous_math, name)

    start = time.perf_counter()
    scope["pow"], scope["math"] = acquired_inverse, ChargedMath()
    try:
        actual = CONSTRUCTION["public_packet"](n)
        window = actual["parent"]["source"]
        if window is not None:
            assert len(inverse_reports) == 1
            inverse = inverse_reports[0]
            assert root_reports[0][0] == window["N"]
            centre_root = root_reports[0][1]
            decoder = None
            if window["collision"] is not None:
                assert len(root_reports) == 2 and len(gcd_reports) == 1
                old = window["candidate"]
                assert root_reports[1][0] == old["discriminant"]
                assert gcd_reports[0][:2] == (window["N"], old["smaller_candidate"])
                decoder = dict(signal=old["sum_signal"], discriminant=old["discriminant"],
                               square_root=root_reports[1][1], candidate=old["smaller_candidate"],
                               gcd_run=gcd_reports[0][2], factor=window["factor"])
            else:
                assert len(root_reports) == 1 and not gcd_reports
            raw = window["construction"]["arithmetic"]
            initial = dict(multiplications=raw["multiplications"]+inverse["multiplications"],
                           reductions=raw["reductions"]+inverse["reductions"],
                           quotients=inverse["quotients"], euclid_steps=inverse["steps"],
                           halvings=raw["halvings"], parity_tests=raw["parity_tests"],
                           inverse_additions=inverse["additions"], inverse_subtractions=inverse["subtractions"],
                           inverse_zero_tests=inverse["zero_tests"], inverse_gcd_tests=1,
                           max_product_bits=max(raw["max_product_bits"], inverse["max_product_bits"]),
                           max_inverse_padded_bits=inverse["max_padded_bits"], inverse_acquisitions=1,
                           opaque_inverse_queries=0, centre_square_roots=1, input_bits=raw["input_bits"])
            decoder_gcd = decoder["gcd_run"] if decoder else None
            roots = [report for _, report in root_reports]
            totals = dict(multiplications=initial["multiplications"]+
                                            (decoder_gcd["multiplications"]+2 if decoder else 0),
                          reductions=initial["reductions"]+(decoder_gcd["reductions"]+1 if decoder else 0),
                          euclid_quotients=inverse["quotients"]+(decoder_gcd["quotients"] if decoder else 0),
                          sqrt_steps=sum(report["steps"] for report in roots),
                          sqrt_quotients=sum(report["quotients"] for report in roots),
                          sqrt_digit_reductions=sum(report["digit_reductions"] for report in roots),
                          sqrt_shifts=sum(report["shifts"] for report in roots),
                          sqrt_additions=sum(report["additions"] for report in roots),
                          sqrt_subtractions=sum(report["subtractions"] for report in roots),
                          sqrt_trial_comparisons=sum(report["comparisons"] for report in roots),
                          sqrt_zero_tests=sum(report["zero_tests"] for report in roots),
                          power_halvings=raw["halvings"], parity_tests=raw["parity_tests"],
                          other_fixed_divisions=1+int(decoder is not None),
                          setup_fixed_shifts=2+int(decoder is not None),
                          centre_roots=1, decoder_roots=int(decoder is not None),
                          decoder_gcd_runs=int(decoder is not None), opaque_centre_roots=0,
                          opaque_decoder_roots=0, opaque_decoder_gcds=0, opaque_inverse_queries=0,
                          max_product_bits=max(initial["max_product_bits"],
                                               decoder_gcd["max_product_bits"] if decoder else 0),
                          max_sqrt_temporary_bits=max(report["max_temporary_bits"] for report in roots),
                          input_bits=raw["input_bits"])
            window["construction"].update(inverse=inverse, initial_arithmetic=initial,
                                            centre_root=centre_root, decoder=decoder,
                                            rooted_arithmetic=totals)
        else:
            assert not inverse_reports and not root_reports and not gcd_reports
    finally:
        scope["math"] = previous_math
        if had_pow:
            scope["pow"] = previous_pow
        else:
            scope.pop("pow", None)
    actual["elapsed_ms"] = 1000*(time.perf_counter()-start)
    if window is not None:
        other_products = [] if decoder is None else [
            decoder["signal"]**2, window["block"]*window["collision"]["giant_index"]]
        totals["max_product_bits"] = max([totals["max_product_bits"]]+[v.bit_length() for v in other_products])
        INVERSE["check_inverse"](window["N"], window["active_base"], inverse)
        check_sqrt(window["N"], centre_root)
        if decoder is not None:
            check_decoder(window["N"], window["candidate"]["modulus"], decoder)
            assert window["collision"]["baby_index"] < window["block"]
            assert window["collision"]["giant_index"] < window["block"]
            assert other_products[1].bit_length() <= 2*window["N"].bit_length()+2
        assert totals["multiplications"] <= 4*actual["width"]+8*n.bit_length()+4
        assert totals["reductions"] <= 8*actual["width"]+18*n.bit_length()+10
        assert totals["euclid_quotients"] <= 4*n.bit_length()
        assert totals["sqrt_steps"] <= 3*n.bit_length()
        assert totals["power_halvings"] <= 2*n.bit_length()+1
        assert totals["max_product_bits"] <= 2*n.bit_length()+2
        assert totals["max_sqrt_temporary_bits"] <= 2*n.bit_length()+1
    return actual


def validate_primitives():
    values = set(range(8192))
    for root in range(1, 257):
        values.update((root*root-1, root*root, root*root+1))
    for bits in (1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256,
                 511, 512, 1023, 1024, 2047, 2048, 4095, 4096):
        value = 1 << bits
        values.update((value-1, value, value+1))
    for bits in (16, 32, 64, 128, 256, 512, 1024, 2048):
        root = (1 << bits)+17
        values.update((root*root-1, root*root, root*root+1))
    for n in sorted(values):
        check_sqrt(n, counted_sqrt(n))
    decoder_cases = decoded = 0
    for n in range(1, 97):
        for modulus in range(2*n+3):
            actual = counted_decoder(n, modulus)
            check_decoder(n, modulus, actual)
            decoder_cases += 1
            decoded += int(actual["factor"] is not None)
    return dict(square_root_cases=len(values), largest_square_root_input_bits=max(values).bit_length(),
                decoder_cases=decoder_cases, decoder_proper_factors=decoded)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeWindowSqrt.lean",
                  "scripts/CheckSemiprimeWindowSqrt.lean", "scripts/probe_semiprime_window_sqrt.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources, primitives = source_inventory(), validate_primitives()
    prior = json.loads((ROOT/PARENT_AUDIT).read_text())
    counts, squares = Counter(), 0
    primes = list(primerange(2, 200))
    for i, p in enumerate(primes):
        for q in primes[i:]:
            actual = public_packet(p*q)
            PARENT["check_packet"](actual, p, q)
            counts[actual["status"]] += 1
            squares += int(p == q)
    populations, rooted_rows = {}, []
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
                for key in ("arithmetic", "inverse", "initial_arithmetic"):
                    assert window["construction"][key] == old_window["construction"][key], key
                rooted_rows.append(dict(original_N=p*q, leaf_N=window["N"], leaf_width=window["width"],
                                        **window["construction"]["rooted_arithmetic"]))
            actual.update(reference_p=p, reference_q=q)
            if "regime" in previous:
                actual["regime"] = previous["regime"]
            population.append(actual)
        populations[name] = population
    assert len(rooted_rows) == 5
    result = dict(replay_id=REPLAY_ID, scope="N-only retained window with explicit roots and quadratic decoder gcd",
                  one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False,
                  is_bit_complexity_certificate=False, source_sha256=sources,
                  validation=dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
                                  status_counts=dict(counts), outcomes_preserved=True,
                                  constructed_sources=len(rooted_rows), **primitives),
                  rooted_rows=rooted_rows,
                  summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
                  timing_protocol="Scoped replacements inside the frozen counted window builder only: public inverse and candidate gcd use explicit counted Euclid; centre and candidate roots use restoring base-four code. The complete preceding N-only pipeline, all actual retained window construction, reports, proper-residue continuation and transport are timed. Native isqrt, gcd and inverse are independent references after timing. Private factors, local orders, offsets, invariant checks and frozen source comparisons are outside timing. Unrelated earlier routing primitives keep their prior separate charges.",
                  limitations="The retained window's roots and decoder gcd now have implementations, exact counter bounds and bounded intermediate values. Full bit implementations of general multiplication, quotient/remainder, sorting, polynomial work, preceding descent and transport remain unproved. There is no new universal collision coverage, exponent claim, unbiased corpus or tuned-software comparison. The preceding 61-bit negative survives.",
                  **populations)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(validation=result["validation"], source_pins=len(sources),
                          summary=result["summary"], rooted_rows=rooted_rows,
                          surviving_negative=populations["negative_controls"][0]["N"],
                          one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()
