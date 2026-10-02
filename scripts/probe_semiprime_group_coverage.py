#!/usr/bin/env python3
"""Optional coverage audit and guaranteed small-factor prefix.

Public recovery uses only N and an explicit budget/menu. Hidden primes are
used solely in labelled reference diagnostics and sample generation. This
does not guarantee a useful ECM curve for every semiprime or prove a new
factoring exponent. The additive prefix is classical Strassen batching.
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

from sympy import factorint, nextprime

ROOT = Path(__file__).resolve().parents[1]
API = runpy.run_path(str(ROOT / "scripts/probe_semiprime_group_selection.py"))
LONG, SINGLE = API["LONG"], API["SINGLE"]
CONTROL = 62108022589
REFERENCE_PRIMES = (248909, 249521)
EXTENDED_MENU = (6, 11, 7, 8, 9, 10, 12, 13)
REFERENCE_SEARCH_SEED = 2026100299
FRESH_SEED = 2026100307
SEPARATED_CONTROL = 46840800959
SEPARATED_PRIMES = (203653, 230003)
SEPARATED_SEARCH_SEED = 2026100311


def prefix(n, width=None):
    """Public complete integer cover 1..B², by two polynomial trees.

    It recovers p whenever N=p*q and p<=B²<q. Other inputs may exhaust the
    prefix. No factorial of length B² or prime-factor table is constructed.
    """
    if n < 4:
        raise ValueError("N>=4 required")
    start = time.perf_counter()
    b = SINGLE["ceil_root"](n, 6) if width is None else width
    if b < 1:
        raise ValueError("positive width required")
    roots = list(range(b))
    points = [b*j for j in range(1, b+1)]
    r = LONG["collision_batch"](n, roots, points)
    if r["factor"]:
        f = int(r["factor"])
        signal = r["point"]-r["root"]
        assert 1 < f < n and n % f == 0
        assert 0 < signal <= b*b and math.gcd(n, signal) == f
        r["certificate_signal"] = signal
    return {**r, "algorithm": "classical-additive-prefix", "width": b,
            "covered_integers": b*b, "elapsed_ms": 1000*(time.perf_counter()-start)}


def fermat(n, budget=None):
    """Public bounded near-square test; exhaustion is explicitly allowed."""
    if n < 4:
        raise ValueError("N>=4 required")
    start = time.perf_counter()
    limit = SINGLE["ceil_root"](n, 6) if budget is None else budget
    if limit < 1:
        raise ValueError("positive budget required")
    a = math.isqrt(n)
    a += a*a < n
    for step in range(limit):
        centre = a+step
        square = centre*centre-n
        root = math.isqrt(square)
        if root*root == square:
            factor = math.gcd(n, centre-root)
            if 1 < factor < n:
                return {"status": "factor", "factor": factor, "centre": centre,
                        "certificate_signal": centre-root, "steps": step+1,
                        "elapsed_ms": 1000*(time.perf_counter()-start)}
    return {"status": "near-square-budget-exhausted", "factor": None,
            "steps": limit, "elapsed_ms": 1000*(time.perf_counter()-start)}


def reference_order(p, point, a24):
    """Finite-field diagnostic with the known reference prime, never recovery.

    Find a Hasse-size annihilator by x-coordinate collisions, then strip
    divisors. Group-law correctness is not formalised by this Python audit.
    """
    b = math.isqrt(p)+3
    lookup = {}
    multiple = None
    for i, (x, z) in enumerate(LONG["point_progression"](point, b-1, a24, p), 1):
        if z % p == 0:
            multiple = i
            break
        lookup.setdefault(x*pow(z, -1, p) % p, i)
    if multiple is None:
        step = LONG["montgomery_scale"](point, b, a24, p)
        for j, (x, z) in enumerate(LONG["point_progression"](step, b, a24, p), 1):
            if z % p == 0:
                multiple = j*b
                break
            i = lookup.get(x*pow(z, -1, p) % p)
            if i is not None:
                for candidate in (j*b-i, j*b+i):
                    if candidate > 0 and LONG["montgomery_scale"](point, candidate, a24, p)[1] == 0:
                        multiple = candidate
                        break
                if multiple is not None:
                    break
    if multiple is None:
        raise AssertionError("no reference annihilator")
    for ell in factorint(multiple):
        while multiple % ell == 0 and LONG["montgomery_scale"](point, multiple//ell, a24, p)[1] == 0:
            multiple //= ell
    assert LONG["montgomery_scale"](point, multiple, a24, p)[1] == 0
    assert all(LONG["montgomery_scale"](point, multiple//ell, a24, p)[1] != 0
               for ell in factorint(multiple))
    return multiple


def public_cover_diagnostics(n, sigma):
    """Exact projective leaf products along the actual public probe schedule."""
    curve = API["Curve"](n, sigma, API["Counters"]())
    if not curve.active:
        return [{"setup": curve.initial}]
    rows = []
    bound = SINGLE["ceil_root"](n, 6)
    for b in API["scales"](bound):
        result = curve.probe(b, SINGLE["projection_powers"](b, n+2*math.isqrt(n)+3))
        point = curve.point
        babies = LONG["point_progression"](point, b-1, curve.a24, n)
        step = LONG["montgomery_scale"](point, b, curve.a24, n)
        giants = LONG["point_progression"](step, b, curve.a24, n)
        product = 1
        for x, z in babies:
            for v, wz in giants:
                product = product*((x*wz-v*z) % n) % n
        rows.append({"width": b, "projected_point": list(point), "a24": curve.a24,
                     "projective_product": product, "product_gcd": math.gcd(product, n),
                     "coordinate_gcds": sorted(set(math.gcd(z, n) for x, z in babies+giants)),
                     "probe_status": result["status"]})
        if result["factor"] or not curve.active:
            break
    return rows


def reference_trap_search(separated=False):
    """Reproduce adversarial primes; this search is explicitly an oracle diagnostic."""
    seed = SEPARATED_SEARCH_SEED if separated else REFERENCE_SEARCH_SEED
    rng = random.Random(seed)
    b = 64
    upper = b**3
    powers = SINGLE["projection_powers"](b, upper**2+2*upper+3)
    seen, bad = set(), []
    prefix_counts = [0]*5
    for _ in range(10000):
        p = int(nextprime(rng.randrange(3*upper//4, upper)))
        if p in seen or p >= upper:
            continue
        seen.add(p)
        prefix_counts[0] += 1
        for index, sigma in enumerate(API["CURVES"]):
            c = API["Curve"](p, sigma, API["Counters"]())
            if not c.active:
                break
            point = c.point
            for ell, power in powers:
                point = LONG["montgomery_scale"](point, power, c.a24, p)
                if point[1] == 0:
                    break
            if point[1] == 0:
                break
            babies = LONG["point_progression"](point, b-1, c.a24, p)
            giants = LONG["point_progression"](LONG["montgomery_scale"](point, b, c.a24, p), b, c.a24, p)
            if any(z == 0 for x, z in babies+giants):
                break
            roots = {x*pow(z, -1, p) % p for x, z in babies}
            targets = {x*pow(z, -1, p) % p for x, z in giants}
            if not roots.isdisjoint(targets):
                break
            prefix_counts[index+1] += 1
        else:
            bad.append(p)
            if len(bad) >= 2:
                if not separated or any(fermat(p*q)["factor"] is None for q in bad[:-1]):
                    break
    expected = SEPARATED_PRIMES if separated else REFERENCE_PRIMES
    assert tuple(bad) == expected
    return {"scope": "Known-prime diagnostic, never selector input", "seed": seed,
            "width": b, "primes_checked": len(seen), "prefix_survival": prefix_counts,
            "all_menu_miss_primes": bad}


def audit():
    n = CONTROL
    old = API["run"](n)
    extended = API["run"](n, EXTENDED_MENU)
    assert old["factor"] is None and extended["factor"] in REFERENCE_PRIMES
    assert extended["sigma"] == 13 and extended["width"] == 16
    covers = {str(s): public_cover_diagnostics(n, s) for s in API["CURVES"]+(13,)}
    assert all(row["product_gcd"] == 1 and row["coordinate_gcds"] == [1]
               for s in API["CURVES"] for row in covers[str(s)])
    periods = []
    for p in REFERENCE_PRIMES:
        for sigma in API["CURVES"]:
            c = API["Curve"](p, sigma, API["Counters"]())
            initial = reference_order(p, c.point, c.a24)
            point = c.point
            for ell, power in SINGLE["projection_powers"](old["bound"], n+2*math.isqrt(n)+3):
                point = LONG["montgomery_scale"](point, power, c.a24, p)
            residual = reference_order(p, point, c.a24)
            assert residual > old["bound"]**2+old["bound"]
            periods.append({"scope": "Known-prime group diagnostic", "p": p, "sigma": sigma,
                            "point_order": initial, "order_factorization": factorint(initial),
                            "projected_point_order": residual})
    rng = random.Random(FRESH_SEED)
    small = []
    for factor_bits in (12, 16, 20):
        for _ in range(4):
            p = int(nextprime(rng.randrange(1 << (factor_bits-1), 1 << factor_bits)))
            q = int(nextprime(rng.randrange(p*p, 4*p*p)))
            product = p*q
            result = prefix(product)
            assert p <= result["width"]**2 < q and result["factor"] == p
            small.append({"scope": "Reference primes used only to verify coverage premise",
                          "N": product, "reference_primes": [p, q], "result": result})
    targets = []
    for p in REFERENCE_PRIMES:
        b = old["bound"]
        d = 1 << (b-1).bit_length()
        c = p//d+1
        assert b <= d < 2*b and c <= b*b+1
        assert p+1 <= d*c <= p+1+2*math.isqrt(p)
        targets.append({"scope": "Arithmetic target, not a public curve construction",
                        "p": p, "width": b, "dyadic_divisor": d, "cofactor": c,
                        "candidate_order": d*c, "trace": p+1-d*c})
    sources = ("scripts/probe_semiprime_group_coverage.py", "scripts/probe_semiprime_group_selection.py",
               "RiemannGaussian/SemiprimeGroupCoverage.lean")
    far_curves = API["run"](SEPARATED_CONTROL)
    far_prefix = prefix(SEPARATED_CONTROL)
    far_fermat = fermat(SEPARATED_CONTROL)
    far_extended = API["run"](SEPARATED_CONTROL, EXTENDED_MENU)
    far_covers = {str(s): public_cover_diagnostics(SEPARATED_CONTROL, s) for s in API["CURVES"]}
    assert all(r["factor"] is None for r in (far_curves, far_prefix, far_fermat))
    assert far_extended["factor"] in SEPARATED_PRIMES
    assert all(row["product_gcd"] == 1 and row["coordinate_gcds"] == [1]
               for rows in far_covers.values() for row in rows)
    return {"scope": "Coverage counterexample, useful-order targets and unconditional small-factor prefix; universal one-sixth guarantee open",
            "control": n, "reference_primes": list(REFERENCE_PRIMES),
            "old_menu_result": old, "extended_menu": list(EXTENDED_MENU),
            "extended_menu_result": extended,
            "extended_menu_scope": "Added after inspecting this counterexample; not held-out evidence",
            "public_projective_covers": covers, "reference_periods": periods,
            "reference_trap_search": reference_trap_search(), "hasse_order_targets": targets,
            "small_factor_seed": FRESH_SEED, "small_factor_checks": small,
            "control_prefix": prefix(n), "control_fermat": fermat(n),
            "separated_control": {"N": SEPARATED_CONTROL, "reference_primes": list(SEPARATED_PRIMES),
                "old_menu": far_curves, "prefix": far_prefix, "fermat": far_fermat,
                "extended_menu": far_extended, "public_projective_covers": far_covers,
                "reference_trap_search": reference_trap_search(separated=True)},
            "source_hashes": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("prefix", "fermat", "curve", "probe"))
    parser.add_argument("N", nargs="?", type=int)
    parser.add_argument("--output", default="docs/semiprime-group-coverage-audit.json")
    args = parser.parse_args()
    if args.command == "probe":
        data = audit()
        Path(args.output).write_text(json.dumps(LONG["safe_json"](data), indent=2)+"\n")
        print("saved", args.output, "universal curve guarantee remains open")
    else:
        if args.N is None:
            parser.error("N required")
        data = (prefix(args.N) if args.command == "prefix" else fermat(args.N)
                if args.command == "fermat" else API["run"](args.N, EXTENDED_MENU))
        print(json.dumps(LONG["safe_json"](data), indent=2))


if __name__ == "__main__":
    main()
