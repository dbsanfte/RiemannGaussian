#!/usr/bin/env python3
"""N-only row derivatives; no explicit pair matrix or private source advice.

The distinct public giant values are roots of one monic polynomial. Its
derivative is evaluated using that same product tree, and one selected row
is inspected if an output saturates N. Every original packet is retained
in its whole-modulus value bucket. Native ledgers are diagnostics, not a
formal machine refinement or an every-run one-sixth bit theorem.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-euclid-family-scaling-audit.json"
REPLAY_ID = 202610033101
FAMILY = runpy.run_path(str(ROOT/"scripts/probe_semiprime_euclid_row_family.py"))
IntegerLedger, ScalarLedger, BATCH = FAMILY["IntegerLedger"], FAMILY["ScalarLedger"], FAMILY["BATCH"]


def derivative_outputs(n, roots, integers, ring, batch, metrics):
    """Monic product, coefficient derivative and reuse of the root tree."""
    tree = batch.tree(roots)
    polynomial = tree[0]
    derivative = [ring.mul(k, polynomial[k]) for k in range(1, len(polynomial))]
    metrics["derivative_coefficient_products"] += len(derivative)
    metrics["root_polynomials"] += 1
    metrics["reused_root_trees"] += 1
    out = []

    def visit(node, remainder):
        remainder = batch.mod(remainder, node[0])
        metrics["visited_evaluation_nodes"] += 1
        if node[1] is None:
            out.append(remainder[0] if remainder else 0)
        else:
            visit(node[1], remainder)
            visit(node[2], remainder)

    if roots:
        visit(tree, derivative)
    return out


def recover_derivatives(n, roots, values, integers, metrics):
    """Full saturation recovery inspects at most one off-diagonal row."""
    for j, value in enumerate(values):
        common = integers.gcd(n, value)
        metrics["derivative_gcd_queries"] += 1
        if common == 1:
            continue
        if 1 < common < n:
            return common, "row-derivative", dict(row_index=j, root=roots[j], derivative=value)
        metrics["selected_row_scans"] += 1
        for k, root in enumerate(roots):
            metrics["selected_row_positions"] += 1
            if k == j:
                continue
            difference = integers.divmod(integers.add(roots[j], -root), n)[1]
            assert 0 < difference < n, "global duplicates must be removed before differentiation"
            common = integers.gcd(n, difference)
            metrics["selected_row_gcd_queries"] += 1
            if 1 < common < n:
                return common, "selected-row-difference", dict(row_index=j,
                    other_row_index=k, root=roots[j], other_root=root,
                    derivative=value, difference=difference)
        raise AssertionError("nonunit off-diagonal product has no proper nonzero difference")
    return None, "exhausted-row-derivatives", None


def row_derivative_source(n, alpha=2, signed=False):
    """N-only source. All setup, row/power construction and recovery timed."""
    if n < 4:
        raise ValueError("composite n>=4 required")
    start = time.perf_counter()
    integers, ring, batch = IntegerLedger(), ScalarLedger(n), BATCH["MonicBatch"](n)
    metrics, buckets, m, values = Counter(), {}, None, []

    def finish(factor, stage, witness=None):
        if witness is not None and "root" in witness:
            witness = dict(witness, root_packet_bucket=buckets[witness["root"]])
            if "other_root" in witness:
                witness["other_root_packet_bucket"] = buckets[witness["other_root"]]
        return dict(N=n, factor=factor, stage=stage, modulus=m,
            includes_inverse_row_axis=signed, distinct_public_roots=len(buckets),
            evaluated_derivatives=len(values), witness=witness,
            milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics, **integers.stats(), **ring.stats(), **batch.stats()),
            constructed_pair_matrix=False, is_complete_semiprime_factorizer=False,
            is_complete_bit_certificate=False)

    root = integers.sqrt(n)
    if integers.mul(root, root) == n and 1 < root < n:
        return finish(root, "public-square")
    common = integers.gcd(alpha, n)
    if 1 < common < n:
        return finish(common, "public-base-gcd")
    if common != 1:
        return finish(None, "inconclusive-base")
    m = FAMILY["first_public_prime"](n, integers, metrics)
    common = integers.gcd(m, n)
    if 1 < common < n:
        return finish(common, "public-modulus-gcd")
    if common != 1:
        return finish(None, "inconclusive-modulus")
    inverse = integers.divmod(integers.inverse(alpha, n), n)[1]
    for packet in FAMILY["public_packets"](n, m, integers, metrics):
        for orientation in ((1, -1) if signed else (1,)):
            exponent = orientation*packet["exponent"]
            integers.charge("integer_sign_orientations", packet["exponent"])
            value = ring.power(alpha if exponent >= 0 else inverse, abs(exponent))
            metrics["public_root_lookup_queries"] += 1
            integers.charge("public_root_lookup_operands", value)
            if value in buckets:
                metrics["whole_modulus_duplicate_packets"] += 1
            buckets.setdefault(value, []).append(dict(packet=packet, sign=orientation))
            metrics["retained_packet_bucket_entries"] += 1
    roots = list(buckets)
    metrics["explicit_input_count"] = 2*len(roots)
    values = derivative_outputs(n, roots, integers, ring, batch, metrics)
    factor, stage, witness = recover_derivatives(n, roots, values, integers, metrics)
    return finish(factor, stage, witness)


def reference_packets(n, m):
    """Fast uncharged reference enumeration only; never used by the source."""
    L, U, V, square, half = math.isqrt(n//2), math.isqrt(n), math.isqrt(2*n), m*m, m//2
    for j in range(1, m):
        if math.gcd(j, m) != 1:
            continue
        inverse = pow(j, -1, m)
        r0, r1, x, y, negative = m, n*inverse*inverse % m, 0, 1, False
        pairs = []
        while r1:
            pairs.append((-r1 if negative else r1, y))
            quotient, remainder = divmod(r0, r1)
            pairs.extend(((r0-k*r1 if negative else -(r0-k*r1)), x+k*y)
                for k in range(1, quotient))
            r0, r1, x, y, negative = r1, remainder, y, x+quotient*y, not negative
        for a, t in pairs:
            d, rem = divmod(n*t-j*j*a, m)
            assert rem == 0
            b = (-inverse*d+half) % m-half
            c, rem = divmod(d+j*b, m)
            assert rem == 0
            v, exponent = b*m-2*a*j, n*t+a+b*m-2*a*j
            for orientation, lo, hi in (
                ("smaller-factor", a*(L if a >= 0 else U)+t*U+v,
                    a*(U if a >= 0 else L)+t*V+v),
                ("larger-factor", t*L+a*(U if a >= 0 else V)+v,
                    t*U+a*(V if a >= 0 else U)+v)):
                shift = (lo+hi+square)//(2*square)
                yield dict(j=j, a=a, b=b-shift*m, c=c-shift*j, t=t,
                    shift=shift, center_orientation=orientation, exponent=exponent-shift*square)


def reference_aliases(p, q, signed=False):
    """Private orders classify the entire public family AFTER source work.

    Not an N-only selection method, runtime sample or Lean order proof.
    A residue modulo lcm(actual orders) represents a whole-modulus bucket.
    """
    from sympy import n_order
    n, integers, metrics = p*q, IntegerLedger(), Counter()
    m = FAMILY["first_public_prime"](n, integers, metrics)
    if math.gcd(m, n) != 1:
        return dict(N=n, reference_p=p, reference_q=q, modulus=m,
            reference_classification="public-modulus-factor")
    dP, dQ = int(n_order(2, p)), int(n_order(2, q))
    period = math.lcm(dP, dQ)
    global_values, p_seen, q_seen, p_hits, q_hits, count = set(), {}, {}, 0, 0, 0
    for packet in reference_packets(n, m):
        for sign in ((1, -1) if signed else (1,)):
            count += 1
            e = sign*packet["exponent"]
            whole = e % period
            if whole in global_values:
                continue
            global_values.add(whole)
            ep, eq = e % dP, e % dQ
            p_hits += ep in p_seen
            q_hits += eq in q_seen
            p_seen[ep], q_seen[eq] = eq, ep
    return dict(N=n, reference_p=p, reference_q=q, modulus=m,
        actual_reference_orders=[dP,dQ], includes_inverse_row_axis=signed,
        public_packet_count=count, distinct_whole_modulus_buckets=len(global_values),
        repeated_p_values=p_hits, repeated_q_values=q_hits,
        reference_classification="local-row-alias" if p_hits+q_hits else "no-local-row-alias",
        is_N_only_source=False, actual_orders_kernel_checked=False)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeRowDerivative.lean",
        "scripts/CheckSemiprimeRowDerivative.lean", "scripts/probe_semiprime_row_derivative.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def validate_batch(rnd):
    """Independent pair and scalar oracles; no private source selection."""
    tested, saturated = 0, 0
    controls = [(35,[1,1,6,6,8,8]), (49,[1,8]), (35,[1,2]), (77,[])]
    controls.extend((rnd.randrange(4,500), [rnd.randrange(500) for _ in range(rnd.randrange(14))])
        for _ in range(128))
    for n, original in controls:
        roots = list(dict.fromkeys(v % n for v in original))
        integers, ring, batch, metrics = IntegerLedger(), ScalarLedger(n), BATCH["MonicBatch"](n), Counter()
        values = derivative_outputs(n, roots, integers, ring, batch, metrics)
        expected = [math.prod((x-y) % n for y in roots if x != y) % n for x in roots]
        assert values == expected
        factor, stage, _ = recover_derivatives(n, roots, values, integers, metrics)
        oracle = any(1 < math.gcd(n,(x-y) % n) < n for x in roots for y in roots if x != y)
        assert (factor is not None) == oracle
        assert factor is None or 1 < factor < n and n % factor == 0
        assert metrics["derivative_gcd_queries"]+metrics["selected_row_gcd_queries"] <= 2*len(roots)
        saturated += stage == "selected-row-difference"
        tested += 1
    return dict(native_derivative_and_pair_oracle_cases=tested,
        native_saturation_recoveries=saturated, complete_machine_refinement=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--reference-bits", type=int, nargs="*", default=[60,72])
    parser.add_argument("--reference-per-band", type=int, default=8)
    args = parser.parse_args()
    sources, rnd = source_inventory(), random.Random(REPLAY_ID)
    validation = validate_batch(rnd)
    parent = json.loads((ROOT/"docs/semiprime-euclid-row-family-audit.json").read_text())
    small_sources, outcomes = [], Counter()
    for previous in parent["small_public_sources"]:
        source = row_derivative_source(previous["N"])
        d = source["factor"]
        assert d is None or 1 < d < source["N"] and source["N"] % d == 0
        outcomes[source["stage"]] += 1
        small_sources.append(source)
    control = row_derivative_source(FAMILY["CONTROL_N"])
    assert control["factor"] in (14799739,24991489)
    print(json.dumps(dict(progress="N-only-row-derivative-control", **control)), flush=True)
    reference = reference_aliases(14799739,24991489)
    assert reference["distinct_whole_modulus_buckets"] == control["distinct_public_roots"]
    assert reference["public_packet_count"] == control["metrics"]["retained_packet_bucket_entries"]
    # Compare the uncharged reference constructor to the actual public source.
    keys = ("j","a","b","c","t","shift","center_orientation","exponent")
    checked_packets = [tuple(w[k] for k in keys) for w in FAMILY["public_packets"](
        FAMILY["CONTROL_N"],269,IntegerLedger(),Counter())]
    assert checked_packets == [tuple(w[k] for k in keys)
        for w in reference_packets(FAMILY["CONTROL_N"],269)]
    from sympy import nextprime, isprime
    reference_cases, exhausted_sources = [], []
    for bits in args.reference_bits:
        for i in range(args.reference_per_band):
            p = int(nextprime(rnd.randrange(2**(bits//2-1),2**(bits//2))))
            q = int(nextprime(rnd.randrange(11*p//10,19*p//10)))
            assert isprime(p) and isprime(q) and p <= q <= 2*p
            audit = reference_aliases(p,q)
            reference_cases.append(audit)
            print(json.dumps(dict(progress="reference-only-full-family-aliases",
                nominal_bits=bits, sample_index=i, **audit)), flush=True)
            if audit["reference_classification"] == "no-local-row-alias" and not exhausted_sources:
                source = row_derivative_source(p*q)
                assert source["stage"] == "exhausted-row-derivatives" and source["factor"] is None
                assert source["distinct_public_roots"] == audit["distinct_whole_modulus_buckets"]
                exhausted_sources.append(source)
                print(json.dumps(dict(progress="N-only-exhausted-derivative-control", **source)), flush=True)
    assert source_inventory() == sources, "source changed during replay"
    report = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="Exact row-derivative compression and complete proper-pair recovery",
        one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False,
        is_bit_complexity_certificate=False, is_formal_machine_refinement=False,
        recovery_and_hit_union_lean=True, original_short_window_control_recovers_lean=True,
        validation=dict(validation, compared_reference_constructor_packets=len(checked_packets),
            small_N_only_sources=len(small_sources), small_outcomes=dict(outcomes)),
        control=control, reference_control=reference, small_public_sources=small_sources,
        reference_cases=reference_cases, exhausted_N_only_sources=exhausted_sources,
        parent_short_window_control=parent["control"],
        limitations="The kernel-checked observable preserves the complete proper row-pair hit union after whole-modulus deduplication and recovers even saturated outputs, for all positive moduli including squares. Lean also proves this public derivative detector recovers on the literal complete-family short-window failure; the proving pair is not an algorithm input. Native full-family construction, every signed power, bucket lookup, product tree, coefficient derivative, reuse of the tree for evaluation, GCD and one-row recovery are timed and have diagnostic ledgers. They are not a formal arithmetic or bit-machine refinement, a polynomial-bit-cost theorem, a proof of total row-count scale, or universal coverage. Private factors and actual orders classify only separate reference samples; their orders are not Lean-certified. Any exhausted N-only source is a native exact modular-arithmetic control for this fixed positive row family, not a Lean-certified universal impossibility, a failure of all signed/base/modulus choices, or a lower bound on all factoring algorithms. The complete arbitrary-ratio, every-run, N-only one-sixth bit theorem remains open.")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources), validation=report["validation"],
        control_factor=control["factor"], control_roots=control["distinct_public_roots"],
        exhausted_controls=len(exhausted_sources), reference_cases=len(reference_cases),
        one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()
