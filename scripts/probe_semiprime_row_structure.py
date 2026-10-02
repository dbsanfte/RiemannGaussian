#!/usr/bin/env python3
"""Public-input weighted-row grouping and exact four-corner audit.

This measures anchor construction, not a universal factoring algorithm.
All geometry, centre powers and axis powers are rebuilt in each timed call.
Reference factors are used only to generate inputs and verify returned GCDs.
No lookup survives between inputs. Optional research replay, outside CI.
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

import gmpy2

ROOT = Path(__file__).resolve().parents[1]
WEIGHTED = runpy.run_path(str(ROOT / "scripts/probe_semiprime_weighted_batch.py"))
SEED = 2026100463
METHODS = ("native", "shared_axes", "grouped_products", "existing_vector")
CONTROLS = ((6827, 7187), (2346272483, 3649327547),
            (661911275027, 720957498683), (494041, 494191))


def ceil_root(n, degree):
    root = int(gmpy2.iroot(n, degree)[0])
    return root + (root**degree < n)


def ceil_sqrt(n):
    root = math.isqrt(n)
    return root + (root*root < n)


def public_width(n):
    return 4*ceil_root(n, 5)//5


def axis_powers(base, bound, n):
    values = [1]
    for _ in range(bound):
        values.append(values[-1]*base % n)
    return values


def anchor_batch(n, method="grouped_products"):
    """Recover exactly the existing literal anchors, using N only."""
    if n <= 1 or n % 2 == 0:
        raise ValueError("odd input N>1 required")
    if method not in METHODS:
        raise ValueError("unknown anchor method")
    r = public_width(n)
    pairs = []
    centres = {}
    rows = []
    for a in range(1, math.isqrt(r)+1):
        for b in range(a, min(2*a, r//a)+1):
            if math.gcd(a, b) != 1:
                continue
            k = a*b
            pairs.append((a, b, k))
            if method == "grouped_products":
                if k not in centres:
                    centres[k] = ceil_sqrt(4*n*k)
            else:
                rows.append((a, b, ceil_sqrt(4*n*k)))
    if not pairs:
        return [], {"rows": 0, "unique_products": 0}
    max_a = max(row[0] for row in pairs)
    max_b = max(row[1] for row in pairs)
    if method == "native":
        powers = gmpy2.powmod_exp_list(2, [a*n+b-c for a, b, c in rows], n)
        result = list(map(int, powers))
        metadata = {"centre_roots": len(rows), "centre_powers": 0,
                    "direct_anchor_powers": len(rows), "axis_updates": 0,
                    "join_multiplications": 0}
    elif method == "existing_vector":
        result = WEIGHTED["separated_vector"](n, rows, 8 if len(rows)<32768 else 12)
        metadata = {"centre_roots": len(rows), "centre_powers": len(rows),
                    "direct_anchor_powers": 0, "axis_updates": max_a+max_b,
                    "join_multiplications": 2*len(rows),
                    "vector_method": "existing NumPy Montgomery implementation"}
    else:
        A = int(gmpy2.powmod(2, n, n))
        aa = axis_powers(A, max_a, n)
        bb = axis_powers(2, max_b, n)
        inverse = pow(2, -1, n)
        if method == "shared_axes":
            centre_powers = list(map(int, gmpy2.powmod_exp_list(
                inverse, [c for _, _, c in rows], n)))
            result = [aa[a]*bb[b] % n * h % n
                      for (a, b, _), h in zip(rows, centre_powers)]
            centre_count = len(rows)
        else:
            keys = list(centres)
            powers = gmpy2.powmod_exp_list(inverse, [centres[k] for k in keys], n)
            cache = dict(zip(keys, map(int, powers)))
            result = [aa[a]*bb[b] % n * cache[k] % n for a, b, k in pairs]
            centre_count = len(centres)
        metadata = {"centre_roots": centre_count, "centre_powers": centre_count,
                    "direct_anchor_powers": 0, "axis_updates": max_a+max_b,
                    "join_multiplications": 2*len(pairs),
                    "large_axis_powers": 1}
    metadata.update({"rows": len(pairs), "unique_products": len({k for _, _, k in pairs}),
                     "r": r, "largest_weight": max(max_a, max_b),
                     "charged_output_residues": len(result)})
    return result, metadata


def centre_rank_probe(n, limit=128):
    """Public four-corner tests; no private field, order or factor oracle."""
    if n <= 1 or n % 2 == 0:
        raise ValueError("odd input N>1 required")
    r = public_width(n)
    tested = unit = coherent = 0
    factors = []
    defects = []
    for a in range(max(1, math.isqrt(r)//3), math.isqrt(r)):
        for b in range(a+2, min(2*a-2, r//(a+2)-2)+1):
            corners = ((a, b), (a, b+2), (a+2, b), (a+2, b+2))
            if any(math.gcd(x, y) != 1 for x, y in corners):
                continue
            c00, c01, c10, c11 = [ceil_sqrt(4*n*x*y) for x, y in corners]
            delta = c01+c10-c00-c11
            signal = (int(gmpy2.powmod(2, delta, n))-1) % n
            gcd = math.gcd(signal, n)
            # Independently check the normalized literal four-corner ratio.
            v00, v01, v10, v11 = [int(gmpy2.powmod(2, x*n+y-c, n))
                for (x, y), c in zip(corners, (c00, c01, c10, c11))]
            assert v00*v11 % n * pow(v01*v10 % n, -1, n) % n == (signal+1) % n
            tested += 1
            unit += gcd == 1
            coherent += gcd == n
            if 1 < gcd < n:
                factors.append({"factor": gcd, "signal": signal, "delta": delta,
                                "corners": corners})
            defects.append(delta)
            if tested == limit:
                return {"tested": tested, "unit_defects": unit,
                        "coherent": coherent, "factors": factors,
                        "distinct_defects": len(set(defects)),
                        "defects": defects}
    return {"tested": tested, "unit_defects": unit, "coherent": coherent,
            "factors": factors, "distinct_defects": len(set(defects)),
            "defects": defects}


def swapped_rows_probe(n, width):
    """All normalized row-swap channels for |a-b|<=width, without rows.

    This is an exact shared-prefix collapse to a projected-period test;
    it is not a replacement for the original weighted target-one collision.
    Every setup power, update and GCD is counted. N and width are public.
    """
    if n <= 1 or n % 2 == 0 or width < 0:
        raise ValueError("odd N>1 and nonnegative public width required")
    beta = int(gmpy2.powmod(2, n-1, n))
    value = 1
    signals = []
    for d in range(1, width+1):
        value = value*beta % n
        for sign in (-1, 1):
            signal = (value+sign) % n
            gcd = math.gcd(signal, n)
            if 1 < gcd < n:
                signals.append({"factor": gcd, "signal": signal, "difference": d,
                                "sign": sign})
    return {"width": width, "setup_power_bits": (n-1).bit_length(),
            "modular_updates": width, "gcd_calls": 2*width, "factors": signals}


def exact_swap_regression():
    checked = 0
    for n in range(3, 250, 2):
        for a in range(1, 6):
            for b in range(a+1, 2*a+1):
                centre = ceil_sqrt(4*n*a*b)
                first = pow(2, a*n+b-centre, n)
                second = pow(2, b*n+a-centre, n)
                ratio = pow(2, (a-b)*(n-1), n)
                assert (first-second) % n == second*(ratio-1) % n
                assert (first+second) % n == second*(ratio+1) % n
                # Multiplying by the common prefix is GCD-safe because it is a unit.
                assert math.gcd(first-second, n) == math.gcd(ratio-1, n)
                assert math.gcd(first+second, n) == math.gcd(ratio+1, n)
                # Retaining the target boundary gives the exact paired product.
                target_product = (first-1)*(second-1) % n
                assert target_product == (second*second*ratio-second*(ratio+1)+1) % n
                # Reciprocal folding retains both +/-1 collision channels.
                prefix = first*second % n
                trace_signal = (prefix+pow(prefix, -1, n)-ratio-pow(ratio, -1, n)) % n
                squared_product = (first*first-1)*(second*second-1) % n
                assert squared_product == prefix*trace_signal % n
                assert math.gcd(squared_product, n) == math.gcd(trace_signal, n)
                assert math.gcd(trace_signal, n) % math.gcd(first-1, n) == 0
                assert math.gcd(trace_signal, n) % math.gcd(second-1, n) == 0
                checked += 1
    n, a, b, centre = 77, 1, 2, 25
    first, second = pow(2, a*n+b-centre, n), pow(2, b*n+a-centre, n)
    assert (first, second) == (71, 23)
    assert math.gcd(first-1, n) == 7
    assert math.gcd(first-second, n) == math.gcd(first+second, n) == 1
    return {"exact_swapped_pair_checks": checked,
            "hit_loss_counterexample": {"n": n, "weights": [a, b], "centre": centre,
                "anchors": [first, second], "original_hit": 7,
                "odd_channel_gcd": 1, "even_channel_gcd": 1,
                "second_original_hit": math.gcd(second-1, n),
                "paired_target_product_gcd": math.gcd((first-1)*(second-1), n),
                "paired_trace_gcd": math.gcd((first*first-1)*(second*second-1), n),
                "paired_boundary_note": "both original hits survive; coherent batch requires descent"}}


def labelled_corpus(per_size):
    rng = random.Random(SEED)
    corpus = []
    for bits in (40, 48, 64, 80):
        chosen = set()
        while len(chosen) < per_size:
            p = int(gmpy2.next_prime(rng.randrange(1 << (bits//2-1), 1 << (bits//2))))
            q = int(gmpy2.next_prime(rng.randrange(1 << (bits//2-1), 1 << (bits//2))))
            p, q = sorted((p, q))
            if p != q and (p*q).bit_length() == bits:
                chosen.add((p, q))
        corpus.extend(("fresh", p, q) for p, q in sorted(chosen))
    corpus.extend(("control", p, q) for p, q in CONTROLS)
    return corpus


def replay(per_size=4, repeats=3):
    corpus = labelled_corpus(per_size)
    rng = random.Random(SEED+1)
    # Warm dependency paths before timing; imports are not hidden per-input work.
    for method in METHODS:
        anchor_batch(323, method)
    results = []
    equality_checks = 0
    for kind, p, q in corpus:
        n = p*q
        reference = None
        samples = {method: [] for method in METHODS}
        metrics = {}
        for _ in range(repeats):
            order = list(METHODS)
            rng.shuffle(order)
            for method in order:
                start = time.perf_counter()
                anchors, metadata = anchor_batch(n, method)
                samples[method].append(1000*(time.perf_counter()-start))
                metrics[method] = metadata
                if reference is None:
                    reference = anchors
                assert anchors == reference
                equality_checks += len(anchors)
        rank = centre_rank_probe(n)
        assert all(entry["factor"] in (p, q) for entry in rank["factors"])
        swap = swapped_rows_probe(n, ceil_root(n, 6))
        assert all(entry["factor"] in (p, q) for entry in swap["factors"])
        results.append({"kind": kind, "n": n, "bits": n.bit_length(),
                        "reference_primes": [p, q], "methods": metrics,
                        "elapsed_ms": samples, "centre_rank": rank, "swapped_rows": swap})
    summary = []
    for bits in (40, 48, 64, 80):
        rows = [row for row in results if row["kind"] == "fresh" and row["bits"] == bits]
        if not rows:
            continue
        times = {m: statistics.median(statistics.median(row["elapsed_ms"][m])
                                      for row in rows) for m in METHODS}
        savings = statistics.median(1-row["methods"]["grouped_products"]["unique_products"] /
                                    row["methods"]["grouped_products"]["rows"] for row in rows)
        summary.append({"bits": bits, "inputs": len(rows), "median_ms": times,
                        "median_shared_centre_fraction": savings})
    paths = ("scripts/probe_semiprime_row_structure.py",
             "scripts/probe_semiprime_weighted_batch.py",
             "RiemannGaussian/SemiprimeRowStructure.lean")
    return {"status": "exact anchor batching; universal sixth-root factoring remains unproved",
            "seed": SEED, "fresh_per_size": per_size, "repeats": repeats,
            "timing_scope": "complete anchor construction including geometry and all powers; not factoring",
            "equality_checks": equality_checks, "summary": summary, "inputs": results,
            "swap_regression": exact_swap_regression(),
            "source_sha256": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
            "gmpy2_version": gmpy2.version()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fresh-per-size", type=int, default=4)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.fresh_per_size < 1 or args.repeats < 1:
        parser.error("positive sample and repeat counts required")
    result = replay(args.fresh_per_size, args.repeats)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({key: result[key] for key in ("status", "summary", "equality_checks")}))


if __name__ == "__main__":
    main()
