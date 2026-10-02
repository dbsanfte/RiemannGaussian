#!/usr/bin/env python3
"""Optional public-input tests of two remaining rough-order mechanisms.

Quadratic exponent products can remove one component of a two-factor
local order; a single folded linear cover then sees the remaining order.
Lucas-index maps generate growing-degree Dickson exponents by a cheap
second-order group recurrence. Neither map family has universal coverage.

All input-specific setup, exponent construction, powers, points and
polynomial work are charged. References are used only after extraction
or for explicitly labelled corpus generation/diagnostics. No oracle,
factor-indexed lookup, persistent cache or ordinary-CI execution.
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

import gmpy2

ROOT = Path(__file__).resolve().parents[1]
COMPLEX = runpy.run_path(str(ROOT / "scripts/probe_semiprime_complex_extraction.py"))
LONG = COMPLEX["LONG"]
SINGLE = COMPLEX["SINGLE"]

# Fixed before the fresh corpus is generated. The old reference corpus
# motivated quadratic products; it is not a held-out benchmark.
QUADRATIC_CONSTANTS = (1, -2, -3, -5)
CUBIC_CONSTANTS = (-2, -3, -5, 2)
FRESH_SEED = 2026100273


def exponent_tree(values):
    """Balanced integer product; its complete bit length is charged."""
    if not values or any(value < 1 for value in values):
        raise ValueError("positive nonempty exponent list required")
    nodes = [(gmpy2.mpz(value), None, None) for value in values]
    while len(nodes) > 1:
        following = []
        for i in range(0, len(nodes), 2):
            if i + 1 == len(nodes):
                following.append(nodes[i])
            else:
                left, right = nodes[i:i + 2]
                following.append((left[0] * right[0], left, right))
        nodes = following
    return nodes[0]


def project_power(ring, alpha, exponent, counters):
    """Exact split-colour scalar powering, with exponent bits still charged."""
    if ring.d != 1:
        return ring.power(alpha, int(exponent))
    # The split character re+im is a unit because norm(alpha)=1.
    # Its inverse re-im recovers the second coordinate exactly.
    scalar = (alpha[0] + alpha[1]) % ring.n
    value = int(gmpy2.powmod(scalar, exponent, ring.n))
    inverse = int(gmpy2.invert(value, ring.n))
    counters["native_scalar_powers"] += 1
    counters["native_scalar_exponent_bits"] += int(exponent.bit_length())
    counters["native_scalar_inversions"] += 1
    half = pow(2, -1, ring.n)
    return ((value + inverse) * half % ring.n, (value - inverse) * half % ring.n)


def separate_shared_projection(n, ring, alpha, node, counters=None):
    """Descend a full-modulus annihilation through exponent prefixes.

    The full node is known to close both local legs. If its left prefix
    closes neither, apply it and descend the right. If it closes both,
    descend the left. A proper GCD ends extraction. A single leaf can
    still close both: that is reported, never called a factor.
    """
    if counters is None:
        counters = dict.fromkeys(("native_scalar_powers", "native_scalar_exponent_bits",
                                 "native_scalar_inversions"), 0)
    visited = 0
    while node[1] is not None:
        visited += 1
        left, right = node[1], node[2]
        projected = project_power(ring, alpha, left[0], counters)
        g = math.gcd(projected[0] - 1, n)
        if 1 < g < n:
            return {"status": "factor", "factor": g,
                    "stage": "projection-prefix", "descent_nodes": visited}
        if g == n:
            node = left
        else:
            alpha, node = projected, right
    return {"status": "shared-projection-leaf", "factor": None,
            "stage": "projection-prefix", "descent_nodes": visited,
            "leaf_exponent_decimal": str(node[0])}


def descend_without_global_root(n, node, point):
    """Recover an extra local collision after one globally shared root.

    Roots are globally distinct. Hence every other nonunit leaf supplies
    a proper factor. This descent is used only when the derivative GCD
    is N, guaranteeing an extra collision, and stops at its first factor.
    """
    if node[1] is None:
        signal = (point + node[0][0]) % n
        if signal == 0:
            return None
        g = math.gcd(signal, n)
        return g if 1 < g < n else None
    for child in node[1:]:
        g = math.gcd(LONG["WEIGHTED"]["horner"](child[0], point, n), n)
        if 1 < g < n:
            return g
        if g == n:
            found = descend_without_global_root(n, child, point)
            if found:
                return found
    return None


def oriented_batch(n, ring, batch, baby, target):
    """Keep imaginary orientation when trace folds opposite local channels.

    A full-modulus trace match need not be a global unit match. The
    imaginary difference or sum can still supply a separating GCD.
    Globally identical traces are hashed, with at most four distinct
    norm-one unit representatives for a squarefree odd semiprime. Repeated
    globally coherent aliases therefore do not incur a quadratic scan.
    """
    roots = [2 * value[0] % n for value in baby]
    points = [2 * value[0] % n for value in target]
    by_trace = {}
    for i, root in enumerate(roots):
        by_trace.setdefault(root, {})[baby[i]] = i
    unique_roots = list(by_trace)
    node = batch.tree(unique_roots)
    values = batch.evaluate(node[0], points)
    # Deduplication makes shared roots simple globally. F'(t) removes the
    # one shared factor exactly; all other local collisions remain.
    derivative_values = None
    if any(point in by_trace for point in points):
        derivative = [i * node[0][i] % n for i in range(1, len(node[0]))]
        derivative_values = batch.evaluate(derivative, points)
    shared, orientation_checks, descents = 0, 0, 0
    for j, value in enumerate(values):
        g = math.gcd(value, n)
        if points[j] in by_trace:
            assert g == n and derivative_values is not None
            if g == n:
                # Four follows from two local +/- choices; it is not
                # imposed as an unproved cap on arbitrary composite rings.
                representatives = by_trace.get(points[j], {})
                if len(representatives) > 4:
                    return {"status": "outside-semiprime-representative-bound",
                            "factor": None, "shared_targets": shared,
                            "orientation_checks": orientation_checks}
                for candidate, i in representatives.items():
                    for sign in (-1, 1):
                        orientation_checks += 1
                        signal = (candidate[1] + sign * target[j][1]) % n
                        oriented = math.gcd(signal, n)
                        if 1 < oriented < n:
                            return {"status": "factor", "factor": oriented,
                                    "baby_index": i, "giant_index": j,
                                    "stage": "imaginary-orientation",
                                    "orientation_sign": sign,
                                    "shared_targets": shared,
                                    "orientation_checks": orientation_checks,
                                    "recovery_descents": descents}
            g = math.gcd(derivative_values[j], n)
            if g == n:
                descents += 1
                g = descend_without_global_root(n, node, points[j])
                assert g and 1 < g < n
            if g == 1:
                shared += 1
                continue
        elif g == n:
            descents += 1
            g = LONG["WEIGHTED"]["descend"](node, points[j], n)
            assert g and 1 < g < n
        if 1 < g < n:
            i = next(i for i, root in enumerate(roots)
                     if (points[j] - root) % g == 0 and root != points[j])
            return {"status": "factor", "factor": g, "baby_index": i,
                    "giant_index": j, "stage": "trace-cover",
                    "shared_targets": shared, "orientation_checks": orientation_checks,
                    "recovery_descents": descents}
    return {"status": "no-collision", "factor": None, "shared_targets": shared,
            "orientation_checks": orientation_checks, "recovery_descents": descents}


def linear_cover(n, ring, alpha, width):
    baby, target = [], []
    value = (1, 0)
    for _ in range(width):
        baby.append(value)
        value = ring.mul(value, alpha)
    step = ring.power(alpha, width)
    value = step
    for _ in range(width):
        target.append(value)
        value = ring.mul(value, step)
    batch = LONG["MonicBatch"](n)
    result = oriented_batch(n, ring, batch, baby, target)
    return {**result, **batch.stats(), "baby_count": width, "giant_count": width,
            "linear_closure_bound": width * width}


def factor_linear(n, discriminant=1):
    ring, alpha, info = COMPLEX["prepare"](n, discriminant)
    if ring is None:
        return info
    result = linear_cover(n, ring, alpha, info["bound"])
    return {**info, **result, "algorithm": "oriented-linear",
            "quadratic_multiplications": ring.multiplications}


def projector_terms(width, degree):
    if degree not in (2, 3):
        raise ValueError("the audited families have degree two or three")
    constants = QUADRATIC_CONSTANTS if degree == 2 else CUBIC_CONSTANTS
    return [abs(i ** degree + c) for i in range(1, width + 1) for c in constants]


def factor_projection(n, degree=2, discriminant=1):
    """One common public exponent product, then one linear closure cover.

    Killing one component is useful even when the product does not close
    a complete local order. No order or factorization of a term is read.
    """
    ring, alpha, info = COMPLEX["prepare"](n, discriminant)
    if ring is None:
        return info
    started = time.perf_counter()
    terms = projector_terms(info["bound"], degree)
    node = exponent_tree(terms)
    construction_ms = 1000 * (time.perf_counter() - started)
    before = ring.multiplications
    native = dict.fromkeys(("native_scalar_powers", "native_scalar_exponent_bits",
                           "native_scalar_inversions"), 0)
    projected = project_power(ring, alpha, node[0], native)
    projection_multiplications = ring.multiplications - before
    g = math.gcd(projected[0] - 1, n)
    details = {"algorithm": f"degree-{degree}-projection-plus-linear",
               "projection_terms": len(terms), "max_projection_term": max(terms),
               "projection_exponent_bits": int(node[0].bit_length()),
               "projection_exponent_sha256": hashlib.sha256(
                   node[0].to_bytes((int(node[0].bit_length()) + 7) // 8, "big")).hexdigest(),
               "exponent_construction_ms": construction_ms,
               "projection_multiplications": projection_multiplications}
    if g == n:
        result = separate_shared_projection(n, ring, alpha, node, native)
    elif g > 1:
        result = {"status": "factor", "factor": g, "stage": "polynomial-projection"}
    else:
        result = linear_cover(n, ring, projected, info["bound"])
    return {**info, **details, **result, **native,
            "quadratic_multiplications": ring.multiplications}


def recurrence_points(ring, alpha, seed, count):
    """alpha**D_i(seed,1) without constructing those growing exponents.

    D_0=2, D_1=seed, D_(i+2)=seed*D_(i+1)-D_i. Each group step costs one
    seed power, one conjugation and one multiplication. At a fixed seed
    this is O(1) group work; public N-sized seeds cost O(log N).
    """
    if seed < 3:
        raise ValueError("positive nondegenerate seed >= 3 required")
    previous, current = ring.power(alpha, 2), ring.power(alpha, seed)
    out = []
    for i in range(count):
        out.append(current)
        if i + 1 < count:
            previous, current = current, ring.mul(
                ring.power(current, seed), ring.inverse_one(previous))
    return out


def factor_recurrence(n, seeds=(5, 7), discriminant=1):
    if len(seeds) != 2 or seeds[0] == seeds[1]:
        raise ValueError("two distinct seeds required")
    ring, alpha, info = COMPLEX["prepare"](n, discriminant)
    if ring is None:
        return info
    width = info["bound"]
    baby = recurrence_points(ring, alpha, seeds[0], width)
    target = recurrence_points(ring, alpha, seeds[1], width)
    batch = LONG["MonicBatch"](n)
    result = oriented_batch(n, ring, batch, baby, target)
    return {**info, **result, **batch.stats(), "algorithm": "Lucas-index-orbits",
            "seeds_decimal": [str(seed) for seed in seeds], "baby_count": width,
            "giant_count": width, "recurrence_updates": 2 * max(0, width - 1),
            "quadratic_multiplications": ring.multiplications}


def factor_combined(n, discriminant=1):
    """Fixed, fully charged public portfolio; exhaustion remains explicit.

    Each attempt includes its own setup. There is no secret selection of
    a map or cost-free reuse. Four bounded attempts retain the old linear
    coverage and add both new mechanisms without changing the exponent.
    """
    attempts = []
    costs = dict.fromkeys(("quadratic_multiplications", "native_scalar_powers",
                          "native_scalar_exponent_bits", "native_scalar_inversions",
                          "convolutions", "packed_coefficients", "monic_reductions"), 0)
    methods = (("linear", lambda: factor_linear(n, discriminant)),
               ("quadratic_projection", lambda: factor_projection(n, 2, discriminant)),
               ("Lucas_5_7", lambda: factor_recurrence(n, (5, 7), discriminant)),
               ("cubic_projection", lambda: factor_projection(n, 3, discriminant)))
    for name, method in methods:
        result = method()
        attempts.append({"method": name, "status": result["status"],
                         "stage": result.get("stage"), "factor": result.get("factor")})
        for key in costs:
            costs[key] += result.get(key, 0)
        if result.get("factor"):
            return {"algorithm": "fixed-four-method-portfolio", "status": "factor",
                    "factor": result["factor"], "winning_method": name,
                    "attempts": attempts, "winning_result": result, **costs}
    return {"algorithm": "fixed-four-method-portfolio", "status": "budget-exhausted",
            "factor": None, "attempts": attempts, **costs}


def lift_unit(ring, scalar):
    inverse = pow(scalar, -1, ring.n)
    half = pow(2, -1, ring.n)
    return ((scalar + inverse) * half % ring.n, (scalar - inverse) * half % ring.n)


def validate():
    recurrence_checks = 0
    for n in (35, 77, 143):
        ring = COMPLEX["CountingRing"](n, 1)
        for scalar in (2, 3, 4, 5):
            if math.gcd(scalar, n) != 1:
                continue
            alpha = lift_unit(ring, scalar)
            for seed in (3, 5, 7):
                points = recurrence_points(ring, alpha, seed, 16)
                for i, value in enumerate(points, start=1):
                    exponent = LONG["dickson_integer"](seed, i)
                    assert value == ring.power(alpha, exponent)
                    recurrence_checks += 1
    ring = COMPLEX["CountingRing"](35, 1)
    alpha = lift_unit(ring, 2)
    node = exponent_tree([2, 2, 3])
    assert ring.power(alpha, int(node[0])) == (1, 0)
    separated = separate_shared_projection(35, ring, alpha, node)
    assert separated["factor"] in (5, 7)
    left, right = lift_unit(ring, 2), lift_unit(ring, 32)
    assert left[0] == right[0] and left != right and left != ring.inverse_one(right)
    batch = LONG["MonicBatch"](35)
    oriented = oriented_batch(35, ring, batch, [left], [right])
    assert oriented["factor"] in (5, 7) and oriented["stage"] == "imaginary-orientation"
    # Globally coherent aliases remain uninformative, even if repeated.
    batch = LONG["MonicBatch"](35)
    coherent = oriented_batch(35, ring, batch, [left] * 64, [left] * 64)
    assert (coherent["factor"] is None and coherent["orientation_checks"] == 128
            and coherent["recovery_descents"] == 0)
    # A global coherent root must not hide a different local collision.
    other = lift_unit(ring, 12)  # 12=2 (mod 5), 12 != +/- inverse(2) (mod 7).
    batch = LONG["MonicBatch"](35)
    stripped = oriented_batch(35, ring, batch, [left, other], [left])
    assert stripped["factor"] == 5
    # At a full derivative GCD, another collision exists on each hidden
    # prime; descent omits the global root and still separates a factor.
    more = lift_unit(ring, 9)
    batch = LONG["MonicBatch"](35)
    both = oriented_batch(35, ring, batch, [left, other, more], [left])
    assert both["factor"] in (5, 7)
    return {"recurrence_identity_checks": recurrence_checks,
            "shared_projection_descent_checks": 1, "imaginary_orientation_checks": 1,
            "coherent_representative_linear_cost_checks": 1,
            "shared_trace_root_stripping_checks": 2}


def reference_order(alpha, p, discriminant):
    """Post-extraction/reference only; never called by any factor_* method."""
    import sympy
    ring = COMPLEX["CountingRing"](p, discriminant)
    value = (alpha[0] % p, alpha[1] % p)
    order = p - int(gmpy2.legendre(discriminant, p))
    for prime, multiplicity in sympy.factorint(order).items():
        for _ in range(multiplicity):
            if ring.power(value, order // int(prime)) == (1, 0):
                order //= int(prime)
            else:
                break
    assert ring.power(value, order) == (1, 0)
    return order


def reference_geometry(n, factors):
    import sympy
    ring, alpha, info = COMPLEX["prepare"](n, 1)
    if ring is None:
        return {"scope": "reference only", "early_setup": info}
    width = info["bound"]
    rows = []
    for p in factors:
        order = reference_order(alpha, p, 1)
        projected = order
        hits = []
        for i in range(1, width + 1):
            for c in QUADRATIC_CONSTANTS:
                term = abs(i * i + c)
                common = math.gcd(projected, term)
                if common > 1:
                    hits.append({"index": i, "constant": c, "removed_factor": common})
                    projected //= common
        rows.append({"reference_prime_decimal": str(p), "projected_order_decimal": str(order),
                     "reference_order_factors": [[str(r), int(e)]
                                                 for r, e in sympy.factorint(order).items()],
                     "after_quadratic_product_order_decimal": str(projected),
                     "removed_order_components": hits,
                     "entire_initial_order_outside_linear_trace_cover": order > width * width + width})
    return {"scope": "Private orders reconstructed after public-input extraction, not supplied to it.",
            "B": width, "local_orders": rows}


def reference_recurrence_aliases(n, width, periods):
    """Reference-only enlarged-map audit; its work is not hidden in recovery.

    Identical integer Lucas exponents are removed by their common primitive
    seed/index, rather than repeatedly materializing exponentially large
    integer exponents. No private period controls the factor_* functions.
    """
    seeds = list(range(3, 33)) + [n - 1, n, n + 1]
    canonical = {seed: (seed, 1) for seed in seeds}
    for base in range(3, 33):
        previous, current, index = 2, base, 1
        while current <= max(seeds):
            if current in canonical:
                canonical[current] = min(canonical[current], (base, index))
            previous, current = current, base * current - previous
            index += 1
    rows = []
    for period in periods:
        assert gmpy2.is_prime(period)
        sequences, colours = {}, {}
        for seed in seeds:
            previous, current, sequence = 2, seed % period, []
            for _ in range(width):
                sequence.append(current)
                previous, current = current, (seed * current - previous) % period
            sequences[seed] = sequence
            colours[seed] = int(gmpy2.legendre(seed * seed - 4, period))
        hits, coherent, same_colour = [], 0, 0
        for a_index, a in enumerate(seeds):
            table = {}
            for i, value in enumerate(sequences[a], start=1):
                table.setdefault(value, []).append((i, 1))
                table.setdefault(-value % period, []).append((i, -1))
            for b in seeds[a_index + 1:]:
                same_colour += colours[a] == colours[b]
                found = False
                for j, value in enumerate(sequences[b], start=1):
                    for i, sign in table.get(value, []):
                        ca, wa = canonical[a]
                        cb, wb = canonical[b]
                        if sign == 1 and ca == cb and wa * i == wb * j:
                            coherent += 1
                            continue
                        hits.append({"seeds_decimal": [str(a), str(b)], "baby_index": i,
                                     "giant_index": j, "channel": "equal" if sign == 1 else "inverse",
                                     "nested_lift_colours": [colours[a], colours[b]]})
                        found = True
                        break
                    if found:
                        break
        rows.append({"reference_period_decimal": str(period), "seed_pairs": len(seeds) * (len(seeds) - 1) // 2,
                     "same_nested_colour_pairs": same_colour, "noncoherent_hits": hits,
                     "globally_coherent_aliases_skipped": coherent})
    return {"scope": "Reference-only diagnostic of 528 public seed pairs per private period. "
                     "The implemented default recovery attempts only the fixed pair 5,7; "
                     "this enlarged table is neither input to recovery nor a coverage theorem.",
            "rows": rows}


def safe_prime_after(p):
    t = int(gmpy2.next_prime(3 * p // 4))
    while not gmpy2.is_prime(2 * t + 1):
        t = int(gmpy2.next_prime(t))
    return 2 * t + 1


def structured_corpus():
    """Reference-only generation of declared success classes; not random trials."""
    out = []
    for kind in ("rough-square", "two-rough-factors", "cubic-long-prime"):
        for i in range(10, 1000):
            if kind == "rough-square":
                r, cofactor = i * i + 1, None
                p = 6 * r * r + 1  # 2*r^2+1 is divisible by 3 for r>3.
            elif kind == "two-rough-factors":
                r = i * i + 1
                cofactor = int(gmpy2.next_prime(10 * r))
                p = 2 * r * cofactor + 1
            else:
                r, cofactor = i ** 3 - 2, None
                p = 2 * r + 1
            if not gmpy2.is_prime(r) or not gmpy2.is_prime(p):
                continue
            q = safe_prime_after(p)
            n = p * q
            width = SINGLE["ceil_root"](n, 6)
            if r <= width or (kind == "cubic-long-prime" and r <= width * width):
                continue
            out.append({"N": n, "factors": (p, q), "class": kind,
                        "construction_index": i, "reference_order_factor": r,
                        "reference_second_order_factor": cofactor})
            if sum(row["class"] == kind for row in out) == 3:
                break
    return out


def fresh_corpus():
    rng = random.Random(FRESH_SEED)
    out = []
    for bits in (48, 64, 80):
        while sum(row["requested_bits"] == bits for row in out) < 8:
            p = int(gmpy2.next_prime(rng.randrange(2 ** (bits // 2 - 1), 2 ** (bits // 2))))
            q = int(gmpy2.next_prime(rng.randrange(2 ** (bits // 2 - 1), 2 ** (bits // 2))))
            n = p * q
            if p == q or n.bit_length() != bits:
                continue
            out.append({"N": n, "factors": tuple(sorted((p, q))), "requested_bits": bits})
    return out


def run_case(case, include_cubic=False):
    n, factors = case["N"], case["factors"]
    methods = [("linear", lambda: factor_linear(n)),
               ("quadratic_projection", lambda: factor_projection(n)),
               ("Lucas_5_7", lambda: factor_recurrence(n))]
    if include_cubic:
        methods.append(("cubic_projection", lambda: factor_projection(n, degree=3)))
    methods.append(("combined", lambda: factor_combined(n)))
    tests = {}
    for name, method in methods:
        started = time.perf_counter()
        result = method()
        milliseconds = 1000 * (time.perf_counter() - started)
        factor = result.get("factor")
        assert factor is None or (factor in factors and 1 < factor < n and n % factor == 0)
        tests[name] = {"result": result, "ms": milliseconds}
    return {**{key: value for key, value in case.items() if key not in ("N", "factors")},
            "N_decimal": str(n), "reference_factors_decimal": [str(p) for p in factors],
            "tests": tests, "reference_only_geometry": reference_geometry(n, factors)}


def report():
    started = time.perf_counter()
    benchmark = json.loads((ROOT / "docs/semiprime-long-period-benchmark.json").read_text())
    known = {int(sample["N_decimal"]): tuple(int(p) for p in sample["reference_factors_decimal"])
             for row in benchmark["rows"] for sample in row["samples"]}
    signals = json.loads((ROOT / "docs/semiprime-long-period-signals.json").read_text())
    selected = [{"N": int(row["N_decimal"]), "factors": known[int(row["N_decimal"])],
                 "class": "saved-two-rough-cardinality-envelope"}
                for row in signals["reference_only_rough_order_geometry"]["rows"]
                if any(group["class"] == "two_rough_factors"
                       for group in row["smaller_prime_group_envelopes"])]
    controls = [{"N": p * q, "factors": (p, q), "class": "saved-four-rough-control"}
                for p, q in ((6827, 7187), (2346272483, 3649327547),
                             (661911275027, 720957498683))]
    rows = {}
    for label, corpus in (("structured", structured_corpus()), ("saved_two_factor", selected),
                          ("hard_controls", controls), ("fresh", fresh_corpus())):
        rows[label] = []
        for case in corpus:
            record = run_case(case, include_cubic=label in ("structured", "hard_controls"))
            if label == "hard_controls":
                periods = [(p - 1) // 2 for p in case["factors"]]
                periods += [(p + 1) // 12 for p in case["factors"]]
                record["reference_only_enlarged_recurrence_audit"] = reference_recurrence_aliases(
                    case["N"], SINGLE["ceil_root"](case["N"], 6), periods)
            rows[label].append(record)
            status = {name: test["result"].get("factor") is not None
                      for name, test in record["tests"].items()}
            print(f"{label} {record['N_decimal']}: {status}", flush=True)
    proofs = [ROOT / "RiemannGaussian/SemiprimeRoughProjection.lean"]
    paths = [Path(__file__), ROOT / "scripts/probe_semiprime_complex_extraction.py",
             ROOT / "scripts/probe_semiprime_long_period.py", *proofs]
    return {"checks": validate(), "rows": rows, "fresh_seed": FRESH_SEED,
            "scope": "Guaranteed algebraic extraction on stated structured-order classes only. "
                     "No universal collision coverage or one-sixth factoring theorem. "
                     "The fresh corpus follows parameter selection; saved/structured corpora are not held out.",
            "timing_protocol": "Single full calls with warmed imports, fixed method order; no median "
                               "or tuned classical-algorithm comparison. All setup/exponent work included.",
            "elapsed_seconds": time.perf_counter() - started,
            "source_hashes": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                              for path in paths if path.exists()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("validate")
    replay = sub.add_parser("probe")
    replay.add_argument("--output", type=Path)
    factor = sub.add_parser("factor")
    factor.add_argument("N", type=int)
    factor.add_argument("--algorithm", choices=("combined", "projection", "cubic", "recurrence", "linear"),
                        default="combined")
    factor.add_argument("--discriminant", type=int, default=1)
    factor.add_argument("--seeds", nargs=2, type=int, default=(5, 7))
    args = parser.parse_args()
    if args.command == "validate":
        result = validate()
    elif args.command == "probe":
        result = report()
        encoded = json.dumps(LONG["safe_json"](result), indent=2) + "\n"
        if args.output:
            args.output.write_text(encoded)
        print(encoded, end="")
        return
    else:
        if args.algorithm == "combined":
            result = factor_combined(args.N, args.discriminant)
        elif args.algorithm in ("projection", "cubic"):
            result = factor_projection(args.N, degree=3 if args.algorithm == "cubic" else 2,
                                       discriminant=args.discriminant)
        elif args.algorithm == "recurrence":
            result = factor_recurrence(args.N, seeds=args.seeds, discriminant=args.discriminant)
        else:
            result = factor_linear(args.N, discriminant=args.discriminant)
    print(json.dumps(LONG["safe_json"](result), indent=2))


if __name__ == "__main__":
    main()
