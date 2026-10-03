#!/usr/bin/env python3
"""Exact blocked q-factorial jets and CRT exponent-index recovery.

Optional research replay. Each row retains its original interval product
and two derivatives. A saturated simple row decodes one public CRT index,
then uses a short ordinary integer batch. Searching all B rows still costs
O(B squared) inputs across the evaluations in this implementation; no
complete one-sixth bit-cost claim is made.
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
CENTRE = runpy.run_path(str(ROOT / "scripts/probe_semiprime_centre_free_cover.py"))
RECOVERY = CENTRE["RECOVERY"]
PREFIX = CENTRE["PREFIX"]
MonicBatch = PREFIX["MonicBatch"]
SEED = 202610030044
REFERENCE = "https://arxiv.org/abs/2012.08656"


def add_polynomials(a, b, n):
    return [((a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0)) % n
            for i in range(max(len(a), len(b)))]


def multiply_jets(left, right, n):
    p, d, e = left
    q, f, h = right
    return p*q % n, (d*q+p*f) % n, (e*q+p*h) % n


def baby_polynomial_jet(alpha, width, n, batch):
    """Coefficients and their logarithmic alpha derivative; no field division."""
    level = []
    y = 1
    for u in range(width):
        level.append(([(-y) % n, 1], [(-u*y) % n, 0]))
        y = y*alpha % n
    while len(level) > 1:
        new = []
        for i in range(0, len(level)-1, 2):
            a, e = level[i]
            b, f = level[i+1]
            new.append((batch.mul(a, b), add_polynomials(batch.mul(e, b),
                                                        batch.mul(a, f), n)))
        if len(level) % 2:
            new.append(level[-1])
        level = new
    return level[0] if level else ([1], [0])


def interval_jet(n, alpha, x, length):
    """Three scalars from square-root-sized polynomial and point lists."""
    start = time.perf_counter()
    if length < 0 or math.gcd(alpha, n) != 1:
        raise ValueError("nonnegative interval and public unit base required")
    width = max(1, math.isqrt(length)+1)
    blocks, tail = divmod(length, width)
    batch = MonicBatch(n)
    polynomial, base_jet = baby_polynomial_jet(alpha, width, n, batch)
    derivative = [(i*polynomial[i]) % n for i in range(1, len(polynomial))]
    shift = pow(pow(alpha, -1, n), width, n)
    points = CENTRE["geometric"](x, shift, blocks, n)
    values = batch.evaluate(polynomial, points)
    derivatives = batch.evaluate(derivative, points)
    base_values = batch.evaluate(base_jet, points)
    result = (1, 0, 0)
    phase, phase_step, shift_power = 1, pow(alpha, width*width, n), 1
    for j, (z, p, d, e) in enumerate(zip(points, values, derivatives, base_values)):
        block_jet = (phase*p % n, phase*shift_power*d % n,
                     phase*(width*width*j*p+e-width*j*z*d) % n)
        result = multiply_jets(result, block_jet, n)
        phase = phase*phase_step % n
        shift_power = shift_power*shift % n
    y = pow(alpha, blocks*width, n)
    for u in range(blocks*width, length):
        result = multiply_jets(result, ((x-y) % n, 1, (-u*y) % n), n)
        y = y*alpha % n
    return {"product": result[0], "target_derivative": result[1],
            "base_derivative": result[2],
            "elapsed_ms": 1000*(time.perf_counter()-start),
            "metrics": {"baby_factors": width, "polynomial_coefficients": len(polynomial),
                        "base_jet_coefficients": len(base_jet), "evaluation_points": blocks,
                        "derivative_evaluation_points": 3*blocks, "tail_factors": tail,
                        "explicit_interval_targets": 0, "explicit_pair_candidates": 0,
                        **batch.stats()}}


def direct_jet(n, alpha, x, length):
    """Independent scalar product-rule recurrence, outside timed construction."""
    result = (1, 0, 0)
    y = 1
    for u in range(length):
        result = multiply_jets(result, ((x-y) % n, 1, (-u*y) % n), n)
        y = y*alpha % n
    return result


def decode_row(n, alpha, x, length):
    start = time.perf_counter()
    jet = interval_jet(n, alpha, x, length)
    result = {"factor": None, "status": "interval-clear", "jet": jet}
    divisor = math.gcd(jet["product"], n)
    if 1 < divisor < n:
        result.update(status="product-factor", factor=divisor)
    elif divisor == n:
        derivative_gcd = math.gcd(jet["target_derivative"], n)
        result["derivative_gcd"] = derivative_gcd
        if 1 < derivative_gcd < n:
            result.update(status="derivative-factor", factor=derivative_gcd)
        elif derivative_gcd == n:
            result["status"] = "multiple-local-root"
        else:
            denominator = x*jet["target_derivative"] % n
            assert math.gcd(denominator, n) == 1
            index = -jet["base_derivative"]*pow(denominator, -1, n) % n
            result["decoded_index"] = index
            if index < length:
                result["status"] = "common-local-index"
            else:
                width = math.isqrt(length)+1
                roots = [i+1 for i in range(width)]
                points = [(index+1-j*width) % n for j in range(width)]
                recovery = RECOVERY(n, roots, points)
                result["index_recovery"] = recovery
                if recovery["factor"] is not None:
                    offset = recovery["point_index"]*width+recovery["root_index"]
                    assert math.gcd(index-offset, n) == recovery["factor"]
                    result.update(status="crt-index-factor", factor=recovery["factor"],
                                  recovered_index=offset)
                else:
                    result["status"] = "no-proper-index-hit"
    result["elapsed_ms"] = 1000*(time.perf_counter()-start)
    return result


def validate():
    rng = random.Random(SEED)
    checked = 0
    for _ in range(384):
        n = rng.choice((35, 49, 77, 143, 221, 323, 1009, 2803308161))
        while True:
            alpha = rng.randrange(1, n)
            if math.gcd(alpha, n) == 1:
                break
        length = rng.randrange(1, 193)
        x = rng.randrange(n)
        if checked % 3 == 0:
            x = pow(alpha, rng.randrange(length), n)
        actual = interval_jet(n, alpha, x, length)
        expected = direct_jet(n, alpha, x, length)
        assert tuple(actual[k] for k in ("product", "target_derivative", "base_derivative")) == expected
        checked += 1
    n, alpha, length = 2803308161, 1823692905, 4333
    controls = []
    for kind, x in (("saturated-distinct-indices", 387888406),
                    ("proper-interval-product", 76358189),
                    ("shared-root", pow(alpha, 2639, n)),
                    ("interval-clear", 1202134739)):
        row = decode_row(n, alpha, x, length)
        row.update(kind=kind, N=n, alpha=alpha, x=x, length=length)
        expected = direct_jet(n, alpha, x, length)
        assert tuple(row["jet"][k] for k in
                     ("product", "target_derivative", "base_derivative")) == expected
        controls.append(row)
    assert controls[0]["status"] == "crt-index-factor"
    assert controls[0]["jet"]["product"] == 0
    assert controls[0]["decoded_index"] == 1001733316
    assert controls[0]["factor"] in (44963, 62347)
    assert controls[1]["factor"] == 44963
    assert controls[2]["status"] == "common-local-index"
    assert controls[2]["decoded_index"] == 2639
    assert controls[3]["status"] == "interval-clear"
    return {"exact_jet_comparisons": checked+len(controls), "controls": controls}


def projected_cover_rows(n, base=2):
    """Public setup, short pass and at most B exact interval-jet rows."""
    start = time.perf_counter()
    b = PREFIX["sixth_width"](n)
    result = {"N": n, "width": b, "base": base, "factor": None, "rows": []}

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        result.update(status=status, factor=factor, elapsed_ms=1000*(time.perf_counter()-start))
        return result

    result["prefix"] = PREFIX["factor_prefix"](n)
    if result["prefix"]["factor"] is not None:
        return finish("prefix-factor", result["prefix"]["factor"])
    divisor = math.gcd(base, n)
    if 1 < divisor < n:
        return finish("base-factor", divisor)
    if divisor != 1:
        return finish("nonunit-base")
    alpha = pow(base, n-1, n)
    for i in range(1, b+1):
        divisor = math.gcd(alpha-1, n)
        if 1 < divisor < n:
            return finish("projection-factor", divisor)
        if divisor == n:
            return finish("projection-kernel")
        if i >= 2:
            alpha = pow(alpha, i**n.bit_length(), n)
    divisor = math.gcd(alpha-1, n)
    if 1 < divisor < n:
        return finish("projection-factor", divisor)
    if divisor == n:
        return finish("projection-kernel")
    result["alpha"] = alpha
    short_width = 2*b+1
    roots = CENTRE["geometric"](1, alpha, short_width, n)
    step = pow(alpha, short_width, n)
    points = CENTRE["geometric"](step, step, short_width, n)
    result["short_pass"] = RECOVERY(n, roots, points)
    if result["short_pass"]["factor"] is not None:
        return finish("short-period-factor", result["short_pass"]["factor"])
    axis = pow(alpha, n, n)
    x = axis*pow(alpha, b*b, n) % n
    for a in range(1, b+1):
        row = decode_row(n, alpha, x, 3*b*b+1)
        row.update(a=a, x=x)
        result["rows"].append(row)
        if row["factor"] is not None:
            return finish("interval-jet-factor", row["factor"])
        assert row["status"] in ("interval-clear", "common-local-index")
        x = x*axis % n
    return finish("no-proper-row")


def replay():
    validation = validate()
    rng = random.Random(SEED)
    corpus = [(bits, regime, *PREFIX["fresh_pair"](bits, regime, rng))
              for bits in (32, 40, 48) for regime in ("balanced", "small-factor")
              for _ in range(3)]
    corpus += [(32, "prior-long-control", 44963, 62347),
               (40, "prior-long-control", 714107, 1013003),
               (21, "explicit-base-kernel", 829, 1657)]
    cases = []
    for _, regime, p, q in corpus:
        actual = projected_cover_rows(p*q)
        baseline = CENTRE["centre_free_pass"](p*q)
        assert (actual["factor"] is not None) == (baseline["factor"] is not None)
        assert actual["status"] != "no-proper-row"
        actual.update(reference_p=p, reference_q=q, input_bits=(p*q).bit_length(),
                      regime=regime, standard_reshape=baseline)
        for row in actual["rows"]:
            if "decoded_index" in row:
                row["reference_local_indices"] = [row["decoded_index"] % p,
                                                  row["decoded_index"] % q]
        cases.append(actual)
    sources = ["RiemannGaussian/SemiprimeIntervalJet.lean",
               "RiemannGaussian/SemiprimeCentreFreeCover.lean",
               "RiemannGaussian/SemiprimeCartesianCompletion.lean",
               "scripts/CheckSemiprimeIntervalJet.lean",
               "scripts/probe_semiprime_interval_jet.py",
               "scripts/probe_semiprime_centre_free_cover.py",
               "scripts/probe_semiprime_batch_recovery.py",
               "scripts/probe_semiprime_strassen_prefix.py",
               "scripts/probe_semiprime_long_period.py",
               "scripts/probe_semiprime_weighted_batch.py",
               "scripts/probe_semiprime_quadratic_extraction.py",
               "scripts/probe_semiprime_single_extraction.py"]
    statuses = sorted({r["status"] for r in cases})
    return {"seed": SEED, "scope": "blocked geometric interval jets and CRT-index decoding",
            "reference": REFERENCE, "is_bit_complexity_certificate": False,
            "is_complete_semiprime_factorizer": False, "one_sixth_guarantee": "OPEN",
            "source_sha256": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
                              for p in sources},
            "validation": validation, "inputs": cases, "input_count": len(cases),
            "summary": {s: sum(r["status"] == s for r in cases) for s in statuses},
            "limitations": "All setup and both compared algorithms are independently timed. Reference factors are attached afterwards. One row uses O(sqrt(L)) coefficients/points; searching B rows with L=3B squared+1 still uses O(B squared) such inputs in the worst case. The standard reshape retains its B^(3/2) input cost. Fixed-base kernels remain exposed."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"exact_jet_comparisons": result["validation"]["exact_jet_comparisons"],
                      "input_count": result["input_count"], "summary": result["summary"],
                      "one_sixth_guarantee": result["one_sixth_guarantee"]}, indent=2))


if __name__ == "__main__":
    main()
