#!/usr/bin/env python3
"""Optional lazy, colour-diverse point selection; public N only in recovery.

The original four-point pass runs first. Failed inputs then get up to two
opposite-product-colour points per curve, optionally also one same-colour
point. Equal product colour can conceal a change on BOTH unknown fields.
Neither policy guarantees a small separating period for every semiprime.

The private-prime corpus generator is explicitly diagnostic, separate from
run_public. No order/cardinality oracle enters recovery. Outside default CI.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import runpy
import statistics
import time

from sympy import jacobi_symbol, nextprime

ROOT = Path(__file__).resolve().parents[1]
ROTATION = runpy.run_path(str(ROOT / "scripts/probe_semiprime_point_rotation.py"))
API, LONG, SINGLE = ROTATION["API"], ROTATION["LONG"], ROTATION["SINGLE"]
# Recorded outputs of the private generator below, not algorithm inputs.
COHORTS = (
    dict(seed=2026100367, width=80, bits=19, draws=12000, group_bound=2**40,
         checked=8051, primes=(438761, 413951, 479639, 336317, 455527,
                              472411, 439163, 392011, 494041, 357107, 494191)),
    dict(seed=2026100383, width=112, bits=20, draws=24000, group_bound=2**44,
         checked=15766, primes=(949567, 979439, 992429, 933463, 658261,
                               981569, 1002149, 675347, 909529, 966863,
                               842291, 981713, 863897, 623879, 666461, 662693)),
)
AMBIGUITY_CONTROL = 244150615831
FRESH_SEED = 2026100413


def scan_curve(n, template, counters, diverse=False, scan_cap=32):
    """Finite public scan, charging even rejected characters and GCDs."""
    if not template.active:
        return (), None
    original = ROTATION["point_colour_signal"](n, template.a24, template.point)
    counters.data["rhs_gcds"] += 1
    counters.data["twist_colour_tests"] += 1
    g = math.gcd(original, n)
    original_colour = int(jacobi_symbol(original, n))
    if 1 < g < n:
        return (), dict(status="factor", factor=g, stage="colour-scan",
                        certificate_signal=original, sigma=template.sigma, x=None)
    if not original_colour:
        return (), None
    menu, opposite, same = [], 0, 0
    for x in range(2, scan_cap+2):
        signal = ROTATION["point_colour_signal"](n, template.a24, (x, 1))
        counters.data["colour_scanned_points"] += 1
        counters.data["rhs_gcds"] += 1
        counters.data["twist_colour_tests"] += 1
        g = math.gcd(signal, n)
        if 1 < g < n:
            return (), dict(status="factor", factor=g, stage="colour-scan",
                            certificate_signal=signal, sigma=template.sigma, x=x)
        colour = int(jacobi_symbol(signal, n))
        if g == 1 and colour == -original_colour and opposite < 2:
            menu.append((template.sigma, x))
            opposite += 1
        elif g == 1 and diverse and colour == original_colour and same < 1:
            menu.append((template.sigma, x))
            same += 1
        if opposite == 2 and (not diverse or same == 1):
            break
    return tuple(menu), None


def run_public(n, diverse=False, scan_cap=32):
    """Lazy acquisition; no factors, local colours or orders supplied."""
    if n < 4 or scan_cap < 1:
        raise ValueError("N>=4 and positive scan cap required")
    start = time.perf_counter()
    if n % 2 == 0:
        return dict(status="factor", factor=2, stage="even")
    root = math.isqrt(n)
    if root*root == n:
        return dict(status="factor", factor=root, stage="square")
    bound, counters = SINGLE["ceil_root"](n, 6), API["Counters"]()
    counters.data.update(candidate_points=0, rhs_gcds=0, twist_colour_tests=0,
                         colour_scanned_points=0)
    templates, states, menus, colours, history, powers = {}, {}, {}, {}, [], {}

    def finish(result, width=0):
        if result.get("factor"):
            factor = int(result["factor"])
            assert 1 < factor < n and n % factor == 0
            assert math.gcd(n, result["certificate_signal"]) == factor
        return dict(**result, width=width, bound=bound, cost=dict(counters.data),
                    history=history, selected_menu=dict(menus),
                    elapsed_ms=1000*(time.perf_counter()-start))

    for fallback in (False, True):
        for width in API["scales"](bound):
            if width not in powers:
                counters.data["sieve_cells"] += width+1
                powers[width] = SINGLE["projection_powers"](width, n+2*root+3)
            for sigma in API["CURVES"]:
                if sigma not in templates:
                    templates[sigma] = API["Curve"](n, sigma, counters)
                if fallback:
                    if sigma not in menus:
                        menus[sigma], certificate = scan_curve(
                            n, templates[sigma], counters, diverse, scan_cap)
                        if certificate is not None:
                            return finish(certificate)
                    menu = menus[sigma]
                else:
                    menu = ((sigma, None),)
                for key in menu:
                    _, x = key
                    if key not in states:
                        if x is None:
                            state = object.__new__(API["Curve"])
                            state.__dict__ = templates[sigma].__dict__.copy()
                            state.initial = templates[sigma].initial.copy()
                            states[key], colours[key] = state, None
                            counters.data["candidate_points"] += 1
                        else:
                            states[key], colours[key] = ROTATION["point_state"](
                                templates[sigma], x, counters)
                    state = states[key]
                    result = (state.probe(width, powers[width]) if state.active
                              else state.initial.copy())
                    history.append(dict(sigma=sigma, x=x, colour=colours[key],
                                        width=width, status=result["status"],
                                        stage=result.get("stage")))
                    if result["factor"]:
                        return finish(dict(**result, sigma=sigma, x=x,
                                           colour=colours[key]), width)
    return finish(dict(status="point-budget-exhausted", factor=None))


def private_miss_population(cohort):
    """Known-prime generator only; finite-field tests are NOT public signals."""
    rng, seen, found = random.Random(cohort["seed"]), set(), []
    width, bits = cohort["width"], cohort["bits"]
    powers = SINGLE["projection_powers"](width, cohort["group_bound"])
    for _ in range(cohort["draws"]):
        p = int(nextprime(rng.randrange(2**(bits-1), 2**bits)))
        if p >= 2**bits or p in seen:
            continue
        seen.add(p)
        for sigma in API["CURVES"]:
            curve = API["Curve"](p, sigma, API["Counters"]())
            if not curve.active:
                break
            point = curve.point
            for _, exponent in powers:
                point = LONG["montgomery_scale"](point, exponent, curve.a24, p)
                if point[1] == 0:
                    break
            if point[1] == 0:
                break
            baby = LONG["point_progression"](point, width-1, curve.a24, p)
            giant = LONG["point_progression"](
                LONG["montgomery_scale"](point, width, curve.a24, p), width,
                curve.a24, p)
            if any(z == 0 for _, z in baby+giant):
                break
            roots = {x*pow(z, -1, p) % p for x, z in baby}
            if any(x*pow(z, -1, p) % p in roots for x, z in giant):
                break
        else:
            found.append(p)
    assert tuple(found) == cohort["primes"] and len(seen) == cohort["checked"]
    return dict(seed=cohort["seed"], distinct_primes=len(seen), primes=found)


def brief(result):
    fields = ("status", "factor", "sigma", "x", "width", "stage",
              "certificate_signal")
    return {key: result.get(key) for key in fields}


def control_audit():
    from sympy import legendre_symbol
    n, primes = AMBIGUITY_CONTROL, (494041, 494191)
    fixed = ROTATION["run"](n)
    eager = ROTATION["run"](n, colour_flip=True)
    diverse = run_public(n, diverse=True)
    assert eager["factor"] is None and fixed["factor"] in primes
    assert diverse["factor"] in primes
    curve = API["Curve"](n, 11, API["Counters"]())
    colours = []
    for x in (None, 2, 3, 4):
        signal = ROTATION["point_colour_signal"](
            n, curve.a24, curve.point if x is None else (x, 1))
        colours.append(dict(x=x, signal=signal, product=int(jacobi_symbol(signal, n)),
                            private_local=[int(legendre_symbol(signal, p)) for p in primes]))
    # This uses reference factors solely to EXPLAIN the public policy miss.
    assert colours[0]["product"] == colours[2]["product"] == -1
    assert colours[0]["private_local"] == [-1, 1]
    assert colours[2]["private_local"] == [1, -1]
    coverage = runpy.run_path(str(ROOT / "scripts/probe_semiprime_group_coverage.py"))
    return dict(N=n, reference_primes=primes, fixed=fixed, eager=eager,
                diverse=diverse, colour_diagnostic=colours,
                fermat=coverage["fermat"](n),
                scope="Finite selector counterexample; Fermat also solves this near-square input")


def audit(repeats=3, regenerate=False):
    generation = [private_miss_population(c) for c in COHORTS] if regenerate else None
    p1, p2 = (c["primes"] for c in COHORTS)
    corpus = list(itertools.combinations(p1, 2))+list(itertools.combinations(p2, 2))
    corpus += list(itertools.product(p1, p2))
    methods = dict(baseline=API["run"], eager_opposite=lambda n: ROTATION["run"](
        n, colour_flip=True), lazy_opposite=run_public,
        lazy_diverse=lambda n: run_public(n, diverse=True))
    rows, success, costs = [], Counter(), {key: Counter() for key in methods}
    timings = {key: [] for key in methods if key != "baseline"}
    for index, (p, q) in enumerate(corpus):
        n, outputs = p*q, {}
        for key, call in methods.items():
            out = call(n)
            if out["factor"]:
                assert out["factor"] in (p, q)
            success[key] += bool(out["factor"])
            costs[key].update(out.get("cost", {}))
            outputs[key] = out
        assert bool(outputs["eager_opposite"]["factor"]) == bool(outputs["lazy_opposite"]["factor"])
        assert not outputs["eager_opposite"]["factor"] or outputs["lazy_diverse"]["factor"]
        old = outputs["baseline"]
        if old["factor"]:
            for key in ("lazy_opposite", "lazy_diverse"):
                assert old["factor"] == outputs[key]["factor"]
                assert all(outputs[key]["cost"][k] == v for k, v in old["cost"].items())
        rows.append(dict(N=n, reference_primes=(p, q),
                         outcomes={key: brief(out) for key, out in outputs.items()}))
        # First 24 adversarial inputs, rotating order; all failed baseline.
        if index < 24:
            keys = list(methods)[1:]
            samples = {key: [] for key in keys}
            for repeat in range(repeats):
                order = keys[(index+repeat) % 3:]+keys[:(index+repeat) % 3]
                for key in order:
                    start = time.perf_counter()
                    methods[key](n)
                    samples[key].append(1000*(time.perf_counter()-start))
            for key in keys:
                timings[key].append(statistics.median(samples[key]))
    rng, fresh = random.Random(FRESH_SEED), []
    for bits in (12, 16, 20, 24):
        for _ in range(8):
            p = int(nextprime(rng.randrange(2**(bits-1), 2**bits)))
            q = int(nextprime(rng.randrange(2**(bits-1), 2**bits)))
            old, new = API["run"](p*q), run_public(p*q, diverse=True)
            if old["factor"]:
                assert new["factor"] == old["factor"]
                assert all(new["cost"][k] == v for k, v in old["cost"].items())
            fresh.append(dict(N=p*q, reference_primes=(p, q),
                              baseline=brief(old), diverse=brief(new)))
    sources = ("scripts/probe_semiprime_colour_coverage.py",
               "scripts/probe_semiprime_point_rotation.py",
               "scripts/probe_semiprime_group_selection.py",
               "RiemannGaussian/SemiprimeColourCoverage.lean")
    return dict(scope="Adversarial finite coverage and public scheduling; no universal sixth-root guarantee",
                cohorts=COHORTS, regenerated=generation, corpus=rows,
                summary=dict(count=len(rows), successes=dict(success),
                             operation_totals={k: dict(v) for k, v in costs.items()},
                             timing_inputs=24, repeats=repeats,
                             total_median_ms={k: sum(v) for k, v in timings.items()}),
                ambiguity_control=control_audit(), fresh_seed=FRESH_SEED, fresh=fresh,
                source_hashes={s: hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in sources})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("factor", "probe"))
    parser.add_argument("N", nargs="?", type=int)
    parser.add_argument("--diverse", action="store_true")
    parser.add_argument("--regenerate-cohorts", action="store_true")
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--output", default="docs/semiprime-colour-coverage-audit.json")
    args = parser.parse_args()
    if args.command == "factor":
        if args.N is None:
            parser.error("N required")
        print(json.dumps(LONG["safe_json"](run_public(args.N, args.diverse)), indent=2))
    else:
        if args.repeats < 1:
            parser.error("positive repeats required")
        result = audit(args.repeats, args.regenerate_cohorts)
        Path(args.output).write_text(json.dumps(LONG["safe_json"](result), indent=2)+"\n")
        print(json.dumps(result["summary"]))


if __name__ == "__main__":
    main()
