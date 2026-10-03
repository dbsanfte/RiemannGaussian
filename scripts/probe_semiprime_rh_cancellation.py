#!/usr/bin/env python3
"""Exact information-preservation audit of RH-style row cancellations.

Each block is constructed from public N, base, weights and offset only.
Reference primes are used afterwards to label the surviving prime-field
collisions and exact weighted hits. This is an identity/coverage diagnostic,
not a factoring algorithm, runtime benchmark or complete weight cover.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random

from sympy import isprime, nextprime, primerange

ROOT = Path(__file__).resolve().parents[1]
SEED = 202610021843
CONTROL = (46337, 65521)
WIDE_CONTROL = (13309, 15767)
RH_SOURCES = {
    "RiemannGaussian/ZetaRieszPrimeFourier.lean":
        "divisorCharacter_eq_primeProduct",
    "RiemannGaussian/ZetaRieszSignedFrequency.lean": "primePair_eq_centered",
    "RiemannGaussian/ZetaRieszShortDivisorCancellation.lean": "signed_block_eq_zero",
    "RiemannGaussian/EtaMoebiusQuotientAbel.lean":
        "pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_abel",
    "RiemannGaussian/ZetaRieszPairMatching.lean": "sum_eq_pairs_add_remainder",
    "RiemannGaussian/ZetaRieszComplexNullFloor.lean": "increment_coherent_zero",
    "RiemannGaussian/ZetaRieszQuantitativeNullStep.lean": "cubicIncrement_coherent_zero",
}


def sixth_width(n):
    lo, hi = 0, 1 << ((n.bit_length()+5)//6)
    while lo+1 < hi:
        mid = (lo+hi)//2
        if mid**6 < n:
            lo = mid
        else:
            hi = mid
    return hi


def ceil_sqrt(n):
    root = math.isqrt(n)
    return root+(root*root < n)


def construct_block(n, g, a, b, i, u=1, v=2):
    """Division and all phase/target construction use only public inputs."""
    if n <= 1 or math.gcd(n, g) != 1:
        raise ValueError("positive composite modulus and unit base required")
    target = pow(g, i, n)
    target_inverse = pow(target, -1, n)
    axis = pow(g, a*n+b, n)
    du, dv = pow(g, u*n, n), pow(g, v, n)
    weights = [(a, b), (a, b+v), (a+u, b), (a+u, b+v)]
    axes = [axis, axis*dv % n, axis*du % n, axis*du*dv % n]
    rows = []
    for (wa, wb), raw in zip(weights, axes):
        centre = ceil_sqrt(4*n*wa*wb)
        centre_phase = pow(g, centre, n)
        anchor = raw*pow(centre_phase, -1, n) % n
        original = (anchor-target) % n
        residual = (raw-target*centre_phase) % n
        atom = anchor*target_inverse % n
        assert residual == centre_phase*original % n
        assert math.gcd(n, residual) == math.gcd(n, original)
        rows.append({"a": wa, "b": wb, "centre": centre,
                     "centre_phase": centre_phase, "axis": raw,
                     "anchor": anchor, "original": original,
                     "residual": residual, "atom": atom,
                     "gcd": math.gcd(n, original)})
    signs = [1, -1, -1, 1]
    axis_product = axis*(du-1)*(dv-1) % n
    centre_companion = sum(s*r["centre_phase"] for s, r in zip(signs, rows)) % n
    mixed = sum(s*r["residual"] for s, r in zip(signs, rows)) % n
    assert mixed == (axis_product-target*centre_companion) % n
    original_product = math.prod(r["original"] for r in rows) % n
    residual_product = math.prod(r["residual"] for r in rows) % n
    euler_product = math.prod(1-r["atom"] for r in rows) % n
    prefix = math.prod(r["centre_phase"] for r in rows) % n
    assert original_product == pow(-target, 4, n)*euler_product % n
    assert residual_product == prefix*original_product % n
    assert math.gcd(n, original_product) == math.gcd(n, residual_product)
    assert math.gcd(n, original_product) == math.gcd(n, euler_product)
    # Check the full RH-style signed subset identity independently.
    subset_sum = 0
    for mask in range(16):
        subset_term = math.prod(rows[j]["atom"] for j in range(4) if mask >> j & 1)
        subset_sum += (-1)**mask.bit_count()*subset_term
    assert subset_sum % n == euler_product
    return {"N": n, "base": g, "offset": i, "u": u, "v": v,
            "rows": rows, "axis_product": axis_product,
            "axis_gcd": math.gcd(n, axis_product),
            "centre_companion": centre_companion, "mixed": mixed,
            "mixed_gcd": math.gcd(n, mixed),
            "original_product": original_product, "product": residual_product,
            "product_gcd": math.gcd(n, residual_product),
            "euler_product": euler_product}


def construct_divisor_orbit(n, g, r, s, i):
    """The four public weight pairs share exactly one product centre."""
    k = r*s
    centre = ceil_sqrt(4*n*k)
    centre_phase = pow(g, centre, n)
    phase_inverse = pow(centre_phase, -1, n)
    target = pow(g, i, n)
    weights = [(1, k), (r, s), (s, r), (k, 1)]
    anchors = [pow(g, a*n+b, n)*phase_inverse % n for a, b in weights]
    ratio = anchors[0]*anchors[3]*pow(anchors[1]*anchors[2] % n, -1, n) % n
    closed = pow(g, (r-1)*(s-1)*(n+1), n)
    assert ratio == closed
    gcds = [math.gcd(n, (anchor-target) % n) for anchor in anchors]
    return {"N": n, "r": r, "s": s, "offset": i,
            "centre": centre, "weights": weights, "anchors": anchors,
            "original_gcds": gcds, "ratio": ratio,
            "closed_ratio": closed, "ratio_signal_gcd": math.gcd(n, (ratio-1) % n)}


def diagnose(p, q, cap):
    """Reference labels never influence construction, weights or offsets."""
    assert isprime(p) and isprime(q)
    n = p*q
    width = sixth_width(n)
    counts = {"primitive_blocks": 0, "tested_offsets": 0,
              "blocks_with_proper_row_gcd": 0,
              "mixed_loses_all_proper_row_hits": 0,
              "axis_loses_all_proper_row_hits": 0,
              "mixed_misses_original_prime_signals": 0,
              "true_weighted_rows": 0,
              "divisor_orbits": 0, "tested_divisor_offsets": 0,
              "divisor_offsets_with_proper_row_gcd": 0,
              "ratio_loses_all_proper_row_hits": 0}
    offsets = sorted({0, 1, width-1})
    for a in range(1, min(cap, width-1)+1):
        for b in range(1, min(cap, width-2)+1):
            weights = [(a, b), (a, b+2), (a+1, b), (a+1, b+2)]
            if any(math.gcd(wa, wb) != 1 for wa, wb in weights):
                continue
            assert all(wa*wb <= width*width for wa, wb in weights)
            counts["primitive_blocks"] += 1
            for i in offsets:
                block = construct_block(n, 2, a, b, i)
                counts["tested_offsets"] += 1
                proper = any(1 < r["gcd"] < n for r in block["rows"])
                counts["blocks_with_proper_row_gcd"] += proper
                counts["mixed_loses_all_proper_row_hits"] += proper and block["mixed_gcd"] == 1
                counts["axis_loses_all_proper_row_hits"] += proper and block["axis_gcd"] == 1
                for ell in set((p, q)):
                    original_hit = any(r["original"] % ell == 0 for r in block["rows"])
                    assert (block["euler_product"] % ell == 0) == original_hit
                    counts["mixed_misses_original_prime_signals"] += (
                        original_hit and block["mixed"] % ell != 0)
                counts["true_weighted_rows"] += sum(
                    (r["a"]*q+r["b"]*p == r["centre"]+i or
                     r["a"]*p+r["b"]*q == r["centre"]+i)
                    for r in block["rows"])
    for r in range(2, min(cap, width)+1):
        for s in range(r+1, min(cap, width)+1):
            if math.gcd(r, s) != 1:
                continue
            counts["divisor_orbits"] += 1
            for i in offsets:
                orbit = construct_divisor_orbit(n, 2, r, s, i)
                assert all(a*b <= width*width and math.gcd(a, b) == 1
                           for a, b in orbit["weights"])
                counts["tested_divisor_offsets"] += 1
                proper = any(1 < d < n for d in orbit["original_gcds"])
                counts["divisor_offsets_with_proper_row_gcd"] += proper
                counts["ratio_loses_all_proper_row_hits"] += proper and orbit["ratio_signal_gcd"] == 1
    return {"N": n, "input_bits": n.bit_length(),
            "reference_p": p, "reference_q": q, "width": width,
            "weight_axis_cap": cap, "counts": counts}


def fresh_pair(bits, rng):
    half = bits//2
    while True:
        p = int(nextprime(rng.randrange(1 << (half-1), (1 << half)-256)))
        q = int(nextprime(rng.randrange(1 << (half-1), (1 << half)-256)))
        if p != q and (p*q).bit_length() == bits:
            return min(p, q), max(p, q)


def probe(cap):
    control = construct_block(3036046577, 2, 12, 17, 0)
    assert all(math.gcd(r["a"], r["b"]) == 1 for r in control["rows"])
    assert control["rows"][0]["gcd"] == control["product_gcd"] == 46337
    assert control["mixed_gcd"] == control["axis_gcd"] == 1
    orbit_control = construct_divisor_orbit(3036046577, 2, 12, 17, 0)
    assert orbit_control["original_gcds"] == [1, 46337, 65521, 1]
    assert orbit_control["ratio_signal_gcd"] == 1
    rng = random.Random(SEED)
    small_primes = list(primerange(3, 68))
    small = [diagnose(p, q, cap) for j, p in enumerate(small_primes)
             for q in small_primes[j:]]
    fresh = [diagnose(*fresh_pair(bits, rng), cap)
             for bits in (32, 40, 48, 64, 80) for _ in range(4)]
    controls = [diagnose(*CONTROL, cap), diagnose(*WIDE_CONTROL, cap)]
    corpus = small+controls+fresh
    totals = {key: sum(item["counts"][key] for item in corpus)
              for key in corpus[0]["counts"]}
    paths = list(RH_SOURCES)+[
        "scripts/probe_semiprime_rh_cancellation.py",
        "RiemannGaussian/SemiprimeRHCancellation.lean",
        "RiemannGaussian/SemiprimeRowStructure.lean",
        "RiemannGaussian/SemiprimeSquareProductCover.lean",
        "scripts/CheckSemiprimeRHCancellation.lean"]
    return {"seed": SEED, "scope": "exact information-preservation diagnostic",
            "is_factor_algorithm": False, "is_bit_complexity_certificate": False,
            "one_sixth_guarantee": "OPEN", "rh_source_declarations": RH_SOURCES,
            "source_sha256": {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
                              for path in paths},
            "control": control, "divisor_orbit_control": orbit_control,
            "small_inputs": small,
            "fresh_inputs": fresh, "coverage_controls": controls,
            "totals": totals, "input_count": len(corpus),
            "limitation": "Capped primitive 2-by-2 blocks and three offsets do not cover the full Lehman family; reference prime labels are diagnostic only."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cap", type=int, default=16)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.cap < 1:
        parser.error("cap must be positive")
    result = probe(args.cap)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"input_count": result["input_count"],
                      "totals": result["totals"],
                      "control_mixed_gcd": result["control"]["mixed_gcd"],
                      "control_product_gcd": result["control"]["product_gcd"],
                      "control_divisor_ratio_gcd": result["divisor_orbit_control"]["ratio_signal_gcd"],
                      "one_sixth_guarantee": result["one_sixth_guarantee"]}, indent=2))


if __name__ == "__main__":
    main()
