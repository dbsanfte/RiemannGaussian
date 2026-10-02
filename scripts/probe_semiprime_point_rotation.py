#!/usr/bin/env python3
"""Optional public-point rotation on the existing Montgomery curve menu.

Only N enters recovery. Curve setup is shared, while every new point's
smooth projection, collision batch and Jacobi calculation is charged.
Known factors enter only explicitly labelled finite-field diagnostics.
This finite menu does not supply universal one-sixth coverage.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import statistics
import time

from sympy import factorint, jacobi_symbol, nextprime

ROOT = Path(__file__).resolve().parents[1]
API = runpy.run_path(str(ROOT / "scripts/probe_semiprime_group_selection.py"))
LONG, SINGLE = API["LONG"], API["SINGLE"]
# Chosen on the two previously recorded failures, before the fresh corpus.
# The original points remain first at each scale; neither colour is deleted.
POINT_MENU = ((6, None), (11, None), (7, None), (8, None),
              (6, 2), (11, 2), (11, 3))
FRESH_SEED = 2026100323
CONTROLS = ((62108022589, (248909, 249521)),
            (46840800959, (203653, 230003)))


def point_colour_signal(n, a24, point):
    """Homogeneous RHS colour, with no affine-coordinate inversion.

    For unit Z, f(X/Z)*Z^4=X*Z*(X^2+A*X*Z+Z^2).
    Multiplication by a unit fourth power leaves its Jacobi colour intact.
    """
    x, z = point
    a = (4*a24-2) % n
    return x*z*(x*x+a*x*z+z*z) % n


def point_state(template, x, counters):
    """Clone immutable setup; each point has its own projection history."""
    state = object.__new__(API["Curve"])
    state.__dict__ = template.__dict__.copy()
    state.initial = template.initial.copy()
    if not state.active:
        return state, None
    state.point = template.point if x is None else (x % state.n, 1)
    state.last_prime = 1
    counters.data["candidate_points"] += 1
    signal = point_colour_signal(state.n, state.a24, state.point)
    counters.data["rhs_gcds"] += 1
    g = math.gcd(signal, state.n)
    if 1 < g < state.n:
        state.fail(g, "point-rhs", signal)
    counters.data["twist_colour_tests"] += 1
    return state, int(jacobi_symbol(signal, state.n))


def colour_flip_menu(n, templates, counters, scan_cap=32, points_per_curve=2):
    """Cheap public selection after baseline exhaustion, not an order oracle.

    Opposite product colour flips exactly one local curve/twist choice.
    All scanned/rejected points are charged; failure to find a colour in
    the fixed cap remains explicit. It need not produce a useful period.
    """
    menu = []
    for sigma in API["CURVES"]:
        template = templates[sigma]
        if not template.active:
            continue
        original = point_colour_signal(n, template.a24, template.point)
        counters.data["rhs_gcds"] += 1
        counters.data["twist_colour_tests"] += 1
        g = math.gcd(original, n)
        original_colour = int(jacobi_symbol(original, n))
        if original_colour == 0:
            if 1 < g < n:
                return menu, {"status": "factor", "factor": g, "sigma": sigma,
                              "x": None, "stage": "colour-scan", "certificate_signal": original}
            continue
        found = 0
        for x in range(2, scan_cap+2):
            signal = point_colour_signal(n, template.a24, (x, 1))
            counters.data["colour_scanned_points"] += 1
            counters.data["rhs_gcds"] += 1
            counters.data["twist_colour_tests"] += 1
            g = math.gcd(signal, n)
            if 1 < g < n:
                return menu, {"status": "factor", "factor": g, "sigma": sigma,
                              "x": x, "stage": "colour-scan", "certificate_signal": signal}
            if g == 1 and int(jacobi_symbol(signal, n)) == -original_colour:
                menu.append((sigma, x))
                found += 1
                if found == points_per_curve:
                    break
    return tuple(menu), None


def run(n, menu=POINT_MENU, interleaved=False, colour_flip=False):
    """Public search, preserving the original menu before the fallback.

    Interleaving is an explicit diagnostic option: fresh measurements found
    that it adds overhead on easy inputs. No hidden group order is queried.
    """
    if n < 4 or not menu or len(set(menu)) != len(menu):
        raise ValueError("N>=4 and a nonempty distinct point menu required")
    if interleaved and colour_flip:
        raise ValueError("colour-flip is a fallback, not an interleaved policy")
    if colour_flip and tuple(s for s, x in menu if x is None) != API["CURVES"]:
        raise ValueError("colour fallback requires the original four-curve prefix")
    start = time.perf_counter()
    if n % 2 == 0:
        return {"status": "factor", "factor": 2, "stage": "even",
                "elapsed_ms": 1000*(time.perf_counter()-start)}
    root = math.isqrt(n)
    if root*root == n:
        return {"status": "factor", "factor": root, "stage": "square",
                "elapsed_ms": 1000*(time.perf_counter()-start)}
    bound = SINGLE["ceil_root"](n, 6)
    counters = API["Counters"]()
    counters.data.update(candidate_points=0, rhs_gcds=0, twist_colour_tests=0,
                         colour_scanned_points=0)
    templates, states, colours, history = {}, {}, {}, []
    phases = (menu,) if interleaved else (
        tuple(key for key in menu if key[1] is None),
        None if colour_flip else tuple(key for key in menu if key[1] is not None))
    powers_by_width = {}
    for phase in phases:
        if phase is None:
            phase, certificate = colour_flip_menu(n, templates, counters)
            if certificate is not None:
                assert math.gcd(n, certificate["certificate_signal"]) == certificate["factor"]
                return {**certificate, "width": 0, "bound": bound, "history": history,
                        "cost": counters.data,
                        "elapsed_ms": 1000*(time.perf_counter()-start)}
        if not phase:
            continue
        for width in API["scales"](bound):
            if width not in powers_by_width:
                counters.data["sieve_cells"] += width+1
                powers_by_width[width] = SINGLE["projection_powers"](width, n+2*root+3)
            powers = powers_by_width[width]
            for key in phase:
                sigma, x = key
                if key not in states:
                    if sigma not in templates:
                        templates[sigma] = API["Curve"](n, sigma, counters)
                    if x is None:
                        # Preserve the original-point pass: no new RHS or
                        # colour tests before its previous successful probe.
                        state = object.__new__(API["Curve"])
                        state.__dict__ = templates[sigma].__dict__.copy()
                        state.initial = templates[sigma].initial.copy()
                        states[key], colours[key] = state, None
                        counters.data["candidate_points"] += 1
                    else:
                        states[key], colours[key] = point_state(templates[sigma], x, counters)
                state = states[key]
                result = (state.probe(width, powers) if state.active else state.initial.copy())
                history.append({"sigma": sigma, "x": x, "colour": colours[key],
                                "width": width, "status": result["status"],
                                "stage": result.get("stage")})
                if result["factor"]:
                    factor = int(result["factor"])
                    assert 1 < factor < n and n % factor == 0
                    assert math.gcd(n, result["certificate_signal"]) == factor
                    return {**result, "sigma": sigma, "x": x, "colour": colours[key],
                            "width": width, "bound": bound, "history": history,
                            "cost": counters.data,
                            "elapsed_ms": 1000*(time.perf_counter()-start)}
    return {"status": "point-budget-exhausted", "factor": None, "bound": bound,
            "history": history, "cost": counters.data,
            "elapsed_ms": 1000*(time.perf_counter()-start)}


def exact_local_orders(n, primes):
    """Oracle diagnostic only: enumerate curve and twist cardinalities."""
    b = SINGLE["ceil_root"](n, 6)
    exponent = math.prod(e for _, e in SINGLE["projection_powers"](
        b, n+2*math.isqrt(n)+3))
    rows = []
    for p in primes:
        squares = {x*x % p for x in range(1, (p+1)//2)}
        for sigma in API["CURVES"]:
            curve = API["Curve"](p, sigma, API["Counters"]())
            a = (4*curve.a24-2) % p
            chi_sum = 0
            for x in range(p):
                rhs = x*(x*x+a*x+1) % p
                chi_sum += 0 if rhs == 0 else 1 if rhs in squares else -1
            card = p+1+chi_sum
            twist_card = p+1-chi_sum
            assert abs(chi_sum) <= math.isqrt(4*p)
            sx, sz = curve.point
            sx = sx*pow(sz, -1, p) % p
            rhs = sx*(sx*sx+a*sx+1) % p
            rows.append({"p": p, "sigma": sigma, "curve_card": card,
                         "curve_factorization": factorint(card),
                         "curve_quotient": card//math.gcd(card, exponent),
                         "twist_card": twist_card,
                         "twist_factorization": factorint(twist_card),
                         "twist_quotient": twist_card//math.gcd(twist_card, exponent),
                         "original_side": "curve" if rhs in squares else "twist"})
    return rows


def timed(call, n, repeats):
    samples, result = [], None
    for _ in range(repeats):
        start = time.perf_counter()
        result = call(n)
        samples.append(1000*(time.perf_counter()-start))
    return {**result, "median_ms": statistics.median(samples), "repeats": repeats}


def reference_miss_prime(seed, width, lower, upper):
    """Adversarial generator with private prime knowledge, never recovery."""
    rng = random.Random(seed)
    powers = SINGLE["projection_powers"](width, upper**2+2*upper+3)
    seen, counts = set(), [0]*(len(POINT_MENU)+1)
    for _ in range(10000):
        p = int(nextprime(rng.randrange(lower, upper)))
        if p >= upper or p in seen:
            continue
        seen.add(p)
        counts[0] += 1
        templates = {}
        for index, (sigma, x) in enumerate(POINT_MENU):
            if sigma not in templates:
                templates[sigma] = API["Curve"](p, sigma, API["Counters"]())
            curve = templates[sigma]
            if not curve.active:
                break
            point = curve.point if x is None else (x, 1)
            for _, exponent in powers:
                point = LONG["montgomery_scale"](point, exponent, curve.a24, p)
                if point[1] == 0:
                    break
            if point[1] == 0:
                break
            baby = LONG["point_progression"](point, width-1, curve.a24, p)
            giant = LONG["point_progression"](
                LONG["montgomery_scale"](point, width, curve.a24, p), width, curve.a24, p)
            if any(z == 0 for _, z in baby+giant):
                break
            roots = {x*pow(z, -1, p) % p for x, z in baby}
            targets = {x*pow(z, -1, p) % p for x, z in giant}
            if not roots.isdisjoint(targets):
                break
            counts[index+1] += 1
        else:
            return {"scope": "Private-prime adversarial generation only", "seed": seed,
                    "width": width, "interval": [lower, upper], "primes_checked": len(seen),
                    "prefix_survival": counts, "prime": p}
    raise AssertionError("reference search exhausted; never interpreted as a factoring failure")


def public_projective_covers(n):
    """Verify every actual projective cover product on the new menu miss."""
    counters, templates, rows = API["Counters"](), {}, []
    counters.data.update(candidate_points=0, rhs_gcds=0, twist_colour_tests=0)
    for sigma, x in POINT_MENU:
        if sigma not in templates:
            templates[sigma] = API["Curve"](n, sigma, counters)
        curve, _ = point_state(templates[sigma], x, counters)
        for width in API["scales"](SINGLE["ceil_root"](n, 6)):
            result = curve.probe(width, SINGLE["projection_powers"](
                width, n+2*math.isqrt(n)+3))
            assert curve.active and result["factor"] is None
            baby = LONG["point_progression"](curve.point, width-1, curve.a24, n)
            giant = LONG["point_progression"](
                LONG["montgomery_scale"](curve.point, width, curve.a24, n), width, curve.a24, n)
            product = 1
            for bx, bz in baby:
                for gx, gz in giant:
                    product = product*((bx*gz-gx*bz) % n) % n
            coordinate_gcds = sorted({math.gcd(z, n) for _, z in baby+giant})
            assert math.gcd(product, n) == 1 and coordinate_gcds == [1]
            rows.append({"sigma": sigma, "x": x, "width": width, "a24": curve.a24,
                         "projected_point": curve.point, "product": product, "product_gcd": 1,
                         "coordinate_gcds": coordinate_gcds})
    return rows


def adversarial_audit(repeats):
    first = reference_miss_prime(2026100337, 64, 3*64**3//4, 64**3)
    second = reference_miss_prime(2026100351, 72, 64**3, 2*64**3)
    assert first["prime"] == 252983 and second["prime"] == 283573
    n = first["prime"]*second["prime"]
    baseline = timed(API["run"], n, repeats)
    rotated = timed(run, n, repeats)
    interleaved = timed(lambda v: run(v, interleaved=True), n, repeats)
    assert all(v["factor"] is None for v in (baseline, rotated, interleaved))
    coverage = runpy.run_path(str(ROOT / "scripts/probe_semiprime_group_coverage.py"))
    prefix, fermat = coverage["prefix"](n), coverage["fermat"](n)
    assert prefix["factor"] is None and fermat["factor"] is None
    extended = API["run"](n, coverage["EXTENDED_MENU"])
    assert extended["factor"] == 283573 and extended["sigma"] == 9
    coloured = timed(lambda v: run(v, colour_flip=True), n, repeats)
    assert coloured["factor"] == 252983 and coloured["certificate_signal"] == 38765850005
    return {"N": n, "reference_primes": [first["prime"], second["prime"]],
            "generation": [first, second], "baseline": baseline,
            "rotated": rotated, "interleaved": interleaved,
            "colour_flip": coloured,
            "prefix": prefix, "fermat": fermat, "extended_curves": extended,
            "public_projective_covers": public_projective_covers(n),
            "local_orders": exact_local_orders(n, (first["prime"], second["prime"])),
            "scope": "Exact failure of the specified seven-point menu, not a factoring lower bound"}


def audit(repeats=3):
    controls = []
    for n, primes in CONTROLS:
        old = timed(API["run"], n, repeats)
        rotated = timed(run, n, repeats)
        interleaved = timed(lambda v: run(v, interleaved=True), n, repeats)
        coloured = timed(lambda v: run(v, colour_flip=True), n, repeats)
        assert old["factor"] is None and rotated["factor"] in primes
        assert coloured["factor"] in primes
        controls.append({"N": n, "reference_primes": primes, "baseline": old,
                         "rotated": rotated,
                         "interleaved": interleaved,
                         "colour_flip": coloured,
                         "orders_scope": "Known-prime cardinality enumeration; not recovery input",
                         "local_orders": exact_local_orders(n, primes)})
    rng = random.Random(FRESH_SEED)
    fresh = []
    for bits in (12, 16, 20, 24):
        for index in range(8):
            p = int(nextprime(rng.randrange(1 << (bits-1), 1 << bits)))
            q = int(nextprime(rng.randrange(1 << (bits-1), 1 << bits)))
            n = p*q
            # Alternate measurement order to reduce fixed ordering bias.
            if index % 2:
                rotated = timed(run, n, repeats)
                old = timed(API["run"], n, repeats)
            else:
                old = timed(API["run"], n, repeats)
                rotated = timed(run, n, repeats)
            for result in (old, rotated):
                if result["factor"]:
                    assert n % result["factor"] == 0
            if old["factor"]:
                assert rotated["factor"] == old["factor"]
                assert rotated["sigma"] == old["sigma"] and rotated.get("x") is None
                assert rotated["width"] == old["width"]
                assert rotated["cost"]["rhs_gcds"] == 0
                assert rotated["cost"]["twist_colour_tests"] == 0
                for name, value in old["cost"].items():
                    assert rotated["cost"][name] == value
            interleaved = timed(lambda v: run(v, interleaved=True), n, repeats)
            coloured = timed(lambda v: run(v, colour_flip=True), n, repeats)
            if old["factor"]:
                assert coloured["factor"] == old["factor"]
                assert coloured["cost"]["colour_scanned_points"] == 0
                for name, value in old["cost"].items():
                    assert coloured["cost"][name] == value
            fresh.append({"N": n, "input_bits": n.bit_length(),
                          "reference_primes": [p, q], "baseline": old, "rotated": rotated,
                          "interleaved": interleaved, "colour_flip": coloured})
    sources = ("scripts/probe_semiprime_point_rotation.py",
               "scripts/probe_semiprime_group_selection.py",
               "scripts/probe_semiprime_group_coverage.py",
               "RiemannGaussian/SemiprimePointRotation.lean")
    return {"scope": "Public point rotation; no universal or GNFS speed claim",
            "menu": POINT_MENU, "menu_selection": "Two existing failures, before fresh sample generation",
            "seed": FRESH_SEED, "controls": controls, "fresh": fresh,
            "adversarial": adversarial_audit(repeats),
            "summary": {"fresh_count": len(fresh),
                "baseline_successes": sum(bool(r["baseline"]["factor"]) for r in fresh),
                "rotated_successes": sum(bool(r["rotated"]["factor"]) for r in fresh),
                "baseline_total_median_ms": sum(r["baseline"]["median_ms"] for r in fresh),
                "rotated_total_median_ms": sum(r["rotated"]["median_ms"] for r in fresh),
                "interleaved_total_median_ms": sum(r["interleaved"]["median_ms"] for r in fresh),
                "colour_flip_total_median_ms": sum(r["colour_flip"]["median_ms"] for r in fresh),
                "interleaved_new_point_hits": sum(r["interleaved"].get("x") is not None for r in fresh),
                "original_cost_counters_preserved": True},
            "source_hashes": {s: hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in sources}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("factor", "probe"))
    parser.add_argument("N", nargs="?", type=int)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--interleaved", action="store_true",
                        help="diagnostic policy; adds new points at every scale")
    parser.add_argument("--colour-flip", action="store_true",
                        help="choose opposite Jacobi colours only after original-menu exhaustion")
    parser.add_argument("--output", default="docs/semiprime-point-rotation-audit.json")
    args = parser.parse_args()
    if args.command == "factor":
        if args.N is None:
            parser.error("N required")
        print(json.dumps(LONG["safe_json"](run(args.N, interleaved=args.interleaved,
                                             colour_flip=args.colour_flip)), indent=2))
    else:
        if args.repeats < 1:
            parser.error("positive repeats required")
        result = audit(args.repeats)
        Path(args.output).write_text(json.dumps(LONG["safe_json"](result), indent=2)+"\n")
        print(json.dumps(result["summary"]))


if __name__ == "__main__":
    main()
