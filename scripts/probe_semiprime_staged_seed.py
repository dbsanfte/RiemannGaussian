#!/usr/bin/env python3
"""Public raw screening, one checked projection, and original row sources.

Optional exact research replay. All raw tests, projection stages and row
construction are timed and counted. A bounded raw scan may be exhausted;
no short-scan coverage theorem or universal sixth-root bit bound is claimed.
The geometric control distinguishes adjacent-power telescoping from the
literal alpha^N row step. Known factors are validation references only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_source_head.py"))
PREFIX, CENTRE, RECOVERY = (SOURCE[k] for k in ("PREFIX", "CENTRE", "RECOVERY"))
SEED = 202610030408
PARENT = "docs/semiprime-source-head-audit.json"


def screen_raw(n, width):
    """Only public candidates 2,...,width+1; no local-order advice."""
    metrics = {"base_gcds": 0, "raw_powers": 0, "raw_gcds": 0,
               "projection_attempts": 0, "stage_powers": 0, "stage_gcds": 0}
    screened = []
    for base in range(2, width+2):
        metrics["base_gcds"] += 1
        d = math.gcd(base, n)
        if 1 < d < n:
            return dict(status="base-factor", factor=d, base=base,
                        screened=screened, metrics=metrics)
        if d != 1:
            screened.append(dict(base=base, status="nonunit"))
            continue
        metrics["raw_powers"] += 1
        raw = pow(base, n-1, n)
        if raw == 1:
            screened.append(dict(base=base, status="raw-kernel"))
            continue
        screened.append(dict(base=base, status="raw-nontrivial", value=raw))
        metrics["raw_gcds"] += 1
        d = math.gcd(raw-1, n)
        assert d != n
        return dict(status="raw-factor" if d != 1 else "usable",
                    factor=d if d != 1 else None, base=base, raw=raw,
                    screened=screened, metrics=metrics)
    return dict(status="no-raw-seed", factor=None, base=None,
                screened=screened, metrics=metrics)


def project_screened(n, base, raw, width):
    """At most one factorial-stage pass; retain every checked residual."""
    assert math.gcd(base, n) == 1 and raw == pow(base, n-1, n) and raw != 1
    assert math.gcd(raw-1, n) == 1
    alpha, repetitions = raw, n.bit_length()
    trace = [dict(stage=0, value=raw, gcd=1)]
    metrics = {"projection_attempts": 1, "stage_powers": 0, "stage_gcds": 0}
    for stage in range(2, width+1):
        alpha = pow(alpha, stage**repetitions, n)
        metrics["stage_powers"] += 1
        d = math.gcd(alpha-1, n)
        metrics["stage_gcds"] += 1
        trace.append(dict(stage=stage, value=alpha, gcd=d))
        # The compiled theorem rules out this jump from a clear stage.
        assert d != n, (n, base, stage, trace)
        if d != 1:
            return dict(alpha=alpha, factor=d, trace=trace, metrics=metrics)
    return dict(alpha=alpha, factor=None, trace=trace, metrics=metrics)


def seeded_source_pass(n, scan_cap=None):
    start = time.perf_counter()
    width = PREFIX["sixth_width"](n)
    result = {"N": n, "width": width, "groups": [], "factor": None}

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        result.update(status=status, factor=factor,
                      elapsed_ms=1000*(time.perf_counter()-start))
        return result

    result["prefix"] = PREFIX["factor_prefix"](n)
    if result["prefix"]["factor"] is not None:
        return finish("prefix-factor", result["prefix"]["factor"])
    scan_width = width if scan_cap is None else min(scan_cap, width)
    result["scan_width"] = scan_width
    raw = screen_raw(n, scan_width)
    result["raw_screen"] = raw
    if raw["status"] != "usable":
        return finish(raw["status"], raw["factor"])
    result["projection"] = project_screened(n, raw["base"], raw["raw"], width)
    projected = result["projection"]
    if projected["factor"] is not None:
        return finish("projection-factor", projected["factor"])
    alpha = projected["alpha"]
    assert math.gcd(alpha-1, n) == 1
    result["alpha"] = alpha
    short_width = 2*width+1
    step = pow(alpha, short_width, n)
    result["short_pass"] = RECOVERY(n, CENTRE["geometric"](1, alpha, short_width, n),
                                   CENTRE["geometric"](step, step, short_width, n))
    if result["short_pass"]["factor"] is not None:
        return finish("short-period-factor", result["short_pass"]["factor"])
    axis, length, first, group_size = pow(alpha, n, n), 3*width*width+1, 1, 1
    x = axis*pow(alpha, width*width, n) % n
    while first <= width:
        count = min(group_size, width-first+1)
        targets = CENTRE["geometric"](x, axis, count, n)
        source = SOURCE["shared_products"](
            n, alpha, targets, length, min(width*width, math.isqrt(count*length)+1))
        gcds = [math.gcd(row["product"], n) for row in source["rows"]]
        group = dict(first_a=first, source_ms=source["elapsed_ms"],
                     source_metrics=source["metrics"], row_gcds=gcds)
        result["groups"].append(group)
        for d in gcds:
            if 1 < d < n:
                return finish("residual-factor", d)
        selected = [i for i, d in enumerate(gcds) if d == n]
        if selected:
            extra = SOURCE["selected_jets"](source, selected)
            group["derivative_ms"] = extra["elapsed_ms"]
            for row in extra["rows"]:
                source["rows"][row["source_index"]].update(row)
            for i, row in enumerate(source["rows"]):
                row["a"] = first+i
            decoded = SOURCE["decode_public_heads"](
                n, source["rows"], source["metrics"]["padded_interval"], gcds)
            group["head_decode"] = decoded
            if decoded["factor"] is not None:
                return finish(decoded["status"], decoded["factor"])
            assert decoded["status"] == "no-proper-labelled-hit", decoded
        first += count
        x = x*pow(axis, count, n) % n
        group_size *= 2
    return finish("no-proper-row")


def direct_product(n, alpha, x, length):
    value, root = 1, 1
    for _ in range(length):
        value = value*(x-root) % n
        root = root*alpha % n
    return value


def validate():
    rng = random.Random(SEED)
    telescoping_comparisons = zero_endpoint_comparisons = 0
    for _ in range(256):
        n = rng.choice((35, 49, 77, 143, 221, 323, 1009))
        alpha, x, length = rng.randrange(n), rng.randrange(n), rng.randrange(33)
        left = direct_product(n, alpha, alpha*x % n, length)*(alpha*x-pow(alpha, length, n)) % n
        right = pow(alpha, length, n)*(alpha*x-1)*direct_product(n, alpha, x, length) % n
        assert left == right
        telescoping_comparisons += 1
        zero_endpoint_comparisons += int((alpha*x-1) % n == 0 or
                                        (alpha*x-pow(alpha, length, n)) % n == 0)
    raw_nontrivial_cases = raw_kernel_cases = stage_comparisons = separated_before_collapse = 0
    primes = (7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
    for index, p in enumerate(primes):
        for q in primes[index+1:]:
            n, width = p*q, PREFIX["sixth_width"](p*q)
            for base in range(2, 18):
                if math.gcd(base, n) != 1:
                    continue
                raw = pow(base, n-1, n)
                if raw == 1:
                    raw_kernel_cases += 1
                    continue
                raw_nontrivial_cases += 1
                alpha, proper_seen = raw, False
                for stage in range(width+1):
                    if stage:
                        alpha = pow(alpha, stage**n.bit_length(), n)
                    d = math.gcd(alpha-1, n)
                    if 1 < d < n:
                        proper_seen = True
                    assert d != n or proper_seen, (n, base, stage)
                    if d == n:
                        separated_before_collapse += 1
                    stage_comparisons += 1
                literal = pow(base, (n-1)*math.factorial(width)**n.bit_length(), n)
                assert alpha == literal
    kernel = screen_raw(1373653, 11)
    assert kernel["factor"] == 829 and kernel["base"] == 5
    exhausted = screen_raw(1373653, 2)
    assert exhausted["status"] == "no-raw-seed"
    staged = project_screened(551, 2, 245, 7)
    assert staged["factor"] == 19 and staged["trace"][-1]["stage"] == 3
    assert pow(2, 550*math.factorial(7)**10, 551) == 1
    p, alpha, period, shift, length = 44963, 1823692905, 22481, 17385, 4333
    original = set(CENTRE["geometric"](1, alpha, length, p))
    actual_shift = set(CENTRE["geometric"](pow(alpha, shift, p), alpha, length, p))
    adjacent_shift = set(CENTRE["geometric"](alpha % p, alpha, length, p))
    assert len(original) == length and not original.intersection(actual_shift)
    assert len(original.intersection(adjacent_shift)) == length-1
    assert pow(alpha, 2803308161, p) == pow(alpha, shift, p)
    return dict(telescoping_comparisons=telescoping_comparisons,
                zero_endpoint_comparisons=zero_endpoint_comparisons,
                raw_nontrivial_cases=raw_nontrivial_cases, raw_kernel_cases=raw_kernel_cases,
                stage_comparisons=stage_comparisons,
                collapsed_stages_with_prior_proper_factor=separated_before_collapse,
                saved_kernel_screen=kernel, deliberately_exhausted_scan=exhausted,
                staged_factor_control=staged,
                geometric_control=dict(prime=p, period=period, literal_row_shift=shift,
                                       interval_length=length, adjacent_overlap=length-1,
                                       literal_row_overlap=0,
                                       compiled_denominator_degree_lower_bound=length))


def source_inventory():
    parent = json.loads((ROOT/PARENT).read_text())
    for path, expected in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT, "RiemannGaussian/SemiprimeStagedSeed.lean",
                  "RiemannGaussian/SemiprimeGeometricRows.lean",
                  "scripts/CheckSemiprimeStagedSeed.lean",
                  "scripts/probe_semiprime_staged_seed.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def replay():
    validation = validate()
    parent = json.loads((ROOT/PARENT).read_text())
    cases = []
    for prior in parent["inputs"]:
        n = prior["N"]
        actual = seeded_source_pass(n)
        baseline = SOURCE["source_public_pass"](n)
        assert actual["factor"] is not None or baseline["factor"] is None
        if "raw_screen" in actual:
            assert actual["raw_screen"]["metrics"]["raw_powers"] <= actual["width"]
        if "projection" in actual:
            assert actual["projection"]["metrics"]["projection_attempts"] == 1
            assert actual["projection"]["metrics"]["stage_powers"] < actual["width"]
        actual.update(regime=prior["regime"], reference_p=prior["reference_p"],
                      reference_q=prior["reference_q"], input_bits=n.bit_length(),
                      fixed_base_source=baseline)
        cases.append(actual)
    return dict(seed=SEED, scope="cheap raw screening, one checked projection and geometric row cancellation",
                is_complete_semiprime_factorizer=False, is_bit_complexity_certificate=False,
                one_sixth_guarantee="OPEN", validation=validation, inputs=cases,
                input_count=len(cases), recovered_count=sum(c["factor"] is not None for c in cases),
                summary={s: sum(c["status"] == s for c in cases) for s in sorted({c["status"] for c in cases})},
                source_sha256=source_inventory(),
                timing_protocol="One charged complete pass and one fresh fixed-base replay per input; includes prefix, screening, projection, short search and all constructed original residuals and selected jets. Exact validation is outside algorithm timing.",
                limitations="The raw scan may be exhausted and its sixth-root coverage is unproved. The row source retains B^(3/2) worst shared inputs. The functional-recurrence degree control does not restrict all algorithms or finite-row interpolation. Python execution and backend bit complexity are not certified in Lean.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in
                      ("input_count", "recovered_count", "summary", "one_sixth_guarantee")}, indent=2))


if __name__ == "__main__":
    main()
