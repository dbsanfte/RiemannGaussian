#!/usr/bin/env python3
"""Charged N-only intermediate-row family and a short-window failure control.

This is an exploratory detector, not a universal factorizer. It constructs
every public intermediate row and both balanced-factor centers. Its prefix
has m+1 baby points and two signed giants per packet. A kernel-checked
semiprime exhausts this family without a factor. Private factors and orders
are used only by the separate reference audit after the source timer.
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
PARENT_AUDIT = "docs/semiprime-quotient-centering-audit.json"
REPLAY_ID = 202610033001
PARENT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_quotient_centering.py"))
ROW = PARENT["PARENT"]
IntegerLedger, ScalarLedger, BATCH = ROW["IntegerLedger"], ROW["ScalarLedger"], ROW["BATCH"]
CONTROL_N = 369867514421371


def first_public_prime(n, integers, metrics):
    candidate = integers.root(n, 6)
    if integers.power(candidate, 6) < n:
        candidate = integers.add(candidate, 1)
    candidate = max(2, candidate)
    while True:
        metrics["public_modulus_candidates"] += 1
        divisor, prime = 2, True
        while integers.mul(divisor, divisor) <= candidate:
            metrics["public_modulus_trial_divisions"] += 1
            if integers.divmod(candidate, divisor)[1] == 0:
                prime = False
                break
            divisor = integers.add(divisor, 1)
        if prime:
            return candidate
        candidate = integers.add(candidate, 1)


def public_pairs(m, u, integers, metrics):
    """Same list and order as Lean's euclidPairs; every emitted row is charged."""
    r0, r1, x, y, negative = m, integers.divmod(u, m)[1], 0, 1, False
    while r1:
        metrics["emitted_intermediate_vectors"] += 1
        yield (-r1 if negative else r1), y
        quotient, remainder = integers.divmod(r0, r1)
        metrics["euclidean_full_divisions"] += 1
        for step in range(1, quotient):
            a = integers.add(r0, -integers.mul(step, r1))
            t = integers.add(x, integers.mul(step, y))
            metrics["emitted_intermediate_vectors"] += 1
            yield (a if negative else -a), t
        r0, r1, x, y = r1, remainder, y, integers.add(x, integers.mul(quotient, y))
        negative = not negative


def public_packets(n, m, integers, metrics):
    low_p, middle, high_q = PARENT["public_box"](n, integers)
    square, half = integers.mul(m, m), integers.divmod(m, 2)[0]
    for j in range(m):
        if integers.gcd(j, m) != 1:
            continue
        metrics["public_unit_residues"] += 1
        inverse, jsquare = integers.inverse(j, m), integers.mul(j, j)
        slope = integers.divmod(integers.mul(n, integers.mul(inverse, inverse)), m)[1]
        for a, t in public_pairs(m, slope, integers, metrics):
            assert a != 0 and t > 0
            d, rem = integers.divmod(integers.add(integers.mul(n, t),
                -integers.mul(jsquare, a)), m)
            assert rem == 0
            b = integers.add(integers.divmod(integers.add(-integers.mul(inverse, d), half), m)[1], -half)
            c, rem = integers.divmod(integers.add(d, integers.mul(j, b)), m)
            assert rem == 0
            offset = integers.add(integers.mul(b, m), -integers.mul(integers.mul(2, a), j))
            exponent = integers.add(integers.add(integers.mul(t, n), a), offset)
            original = dict(j=j, a=a, b=b, c=c, t=t, exponent=exponent)
            metrics["lifted_original_rows"] += 1
            for orientation in ("smaller-factor", "larger-factor"):
                if orientation == "smaller-factor":
                    low = integers.add(integers.add(integers.mul(a, low_p if a >= 0 else middle),
                        integers.mul(t, middle)), offset)
                    high = integers.add(integers.add(integers.mul(a, middle if a >= 0 else low_p),
                        integers.mul(t, high_q)), offset)
                else:
                    low = integers.add(integers.add(integers.mul(t, low_p),
                        integers.mul(a, middle if a >= 0 else high_q)), offset)
                    high = integers.add(integers.add(integers.mul(t, middle),
                        integers.mul(a, high_q if a >= 0 else middle)), offset)
                midpoint = integers.add(integers.add(low, high), square)
                shift = integers.divmod(midpoint, integers.mul(2, square))[0]
                metrics["centered_packets"] += 1
                yield dict(original, source_row=original, shift=shift, center_orientation=orientation,
                    b=integers.add(b, -integers.mul(shift, m)),
                    c=integers.add(c, -integers.mul(shift, j)),
                    exponent=integers.add(exponent, -integers.mul(shift, square)))


def family_source(n, alpha=2):
    """N-only short-window prototype, with all construction inside the timer."""
    start = time.perf_counter()
    integers, ring, batch, metrics = IntegerLedger(), ScalarLedger(n), BATCH["MonicBatch"](n), Counter()
    m, length, points, targets, values = None, None, [], [], []

    def finish(factor, stage, witness=None):
        return dict(N=n, factor=factor, stage=stage, modulus=m, baby_length=length,
            constructed_baby_points=len(points), constructed_signed_giants=len(targets),
            evaluated_points=len(values), witness=witness,
            milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics, **integers.stats(), **ring.stats(), **batch.stats()),
            constructed_pair_matrix=False, is_complete_semiprime_factorizer=False,
            is_complete_bit_certificate=False)

    root = integers.sqrt(n)
    if integers.mul(root, root) == n and 1 < root < n:
        return finish(root, "public-square")
    m = first_public_prime(n, integers, metrics)
    common = integers.gcd(m, n)
    if 1 < common < n:
        return finish(common, "public-modulus-gcd")
    if common != 1:
        return finish(None, "inconclusive-modulus")
    common = integers.gcd(alpha, n)
    if 1 < common < n:
        return finish(common, "public-base-gcd")
    if common != 1:
        return finish(None, "inconclusive-base")
    length = integers.add(m, 1)
    square = integers.mul(m, m)
    gamma = ring.power(alpha, square)
    points.append(1)
    for i in range(1, length):
        points.append(ring.mul(points[-1], gamma))
        common = integers.gcd(points[-1]-1, n)
        metrics["local_period_checks"] += 1
        if 1 < common < n:
            return finish(common, "public-local-period-gcd", dict(index=i))
        if common == n:
            return finish(None, "inconclusive-saturated-local-period", dict(index=i))
    lookup = {v: i for i, v in enumerate(points)}
    assert len(lookup) == length
    inverse = integers.divmod(integers.inverse(alpha, n), n)[1]
    for packet in public_packets(n, m, integers, metrics):
        for orientation in (1, -1):
            exponent = orientation*packet["exponent"]
            integers.charge("integer_sign_orientations", packet["exponent"])
            value = ring.power(alpha if exponent >= 0 else inverse, abs(exponent))
            metrics["giant_lookup_queries"] += 1
            if value in lookup:
                metrics["global_matches"] += 1
                factors = ROW["integer_roots"](n, m, packet, orientation*lookup[value], integers)
                metrics["quadratic_recovery_calls"] += 1
                if factors:
                    return finish(factors[0], "global-quadratic", dict(packet=packet,
                        index=orientation*lookup[value]))
                metrics["removed_global_matches"] += 1
            else:
                targets.append(dict(value=value, packet=packet, orientation=orientation))
    if not targets:
        return finish(None, "inconclusive-empty-giants")
    polynomial = batch.tree([target["value"] for target in targets])[0]
    values = batch.evaluate(polynomial, points)
    metrics["root_polynomials"] += 1
    metrics["point_trees"] += 1
    metrics["explicit_input_count"] = len(targets)+len(points)
    for i, value in enumerate(values):
        common = integers.gcd(value, n)
        metrics["aggregate_gcd_queries"] += 1
        if 1 < common < n:
            return finish(common, "one-axis-product", dict(index=i))
        if common == n:
            for target in targets:
                difference = (points[i]-target["value"]) % n
                common = integers.gcd(difference, n)
                metrics["selected_column_differences"] += 1
                assert common != n
                if 1 < common < n:
                    return finish(common, "selected-column-gcd", dict(index=i,
                        packet=target["packet"], orientation=target["orientation"]))
            raise AssertionError("saturated product retains an individual proper factor")
    return finish(None, "exhausted-family-window")


def reference_control(source):
    """Actual factors and orders appear only after the complete source timer."""
    p, q, m = 14799739, 24991489, source["modulus"]
    n = p*q
    assert source["N"] == n and m == 269
    orders, inverses = {p: 4933246, q: 12495744}, {p: 3615823, q: 5350681}
    factors = {p: (2, 2466623), q: (2, 3, 10847)}
    from sympy import isprime
    assert isprime(p) and isprime(q) and isprime(m)
    for f in (p, q):
        assert pow(2, orders[f], f) == 1
        assert all(pow(2, orders[f]//r, f) != 1 for r in factors[f])
        assert math.gcd(m*m, orders[f]) == 1
        assert m*m*inverses[f] % orders[f] == 1
    fields = {f: {pow(2, m*m*i, f): i for i in range(-m, m+1)} for f in (p, q)}
    packets = list(public_packets(n, m, IntegerLedger(), Counter()))
    minimum_correct = None
    for packet in packets:
        a, b, c, t, j, exponent = (packet[k] for k in ("a", "b", "c", "t", "j", "exponent"))
        assert m*m*c-j*m*b+j*j*a == n*t
        for f, other in ((p, q), (q, p)):
            residue = exponent*inverses[f] % orders[f]
            assert m < residue and residue+m < orders[f]
            assert pow(2, exponent % orders[f], f) not in fields[f]
            if j == f % m:
                value = a*(f//m)**2+b*(f//m)+c
                assert value % f == 0
                index = value//f
                if minimum_correct is None or abs(index) < abs(minimum_correct["index"]):
                    minimum_correct = dict(factor=f, residue=j, a=a, t=t,
                        index=index, center_orientation=packet["center_orientation"])
    assert len(packets) == 14968
    assert minimum_correct["index"] == -306
    assert source["factor"] is None and source["stage"] == "exhausted-family-window"
    assert source["metrics"]["aggregate_gcd_queries"] == m+1
    return dict(reference_p=p, reference_q=q, actual_base_orders=orders,
        actual_baby_orders=orders, stride_inverses=inverses,
        public_packets=len(packets), checked_signed_index_values=2*m+1,
        local_collisions=0, all_timed_aggregate_gcds_one=True,
        minimum_correct_residue_index=minimum_correct)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeEuclidRowFamily.lean",
        "scripts/CheckSemiprimeEuclidRowFamily.lean", "scripts/probe_semiprime_euclid_row_family.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources, rnd = source_inventory(), random.Random(REPLAY_ID)
    relation_cases = emitted = 0
    for m in range(2, 129):
        for u in range(1, m):
            if math.gcd(m, u) != 1:
                continue
            pairs = list(public_pairs(m, u, IntegerLedger(), Counter()))
            assert all(a != 0 and t > 0 and (a-u*t) % m == 0 for a, t in pairs)
            assert len(pairs) <= m
            relation_cases += 1
            emitted += len(pairs)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    cases = rnd.sample(parent["cases"], 32)
    small_sources, outcomes = [], Counter()
    for case in cases:
        source = family_source(case["N"])
        if source["factor"] is not None:
            assert source["factor"] in (case["reference_p"], case["reference_q"])
        outcomes[source["stage"]] += 1
        small_sources.append(source)
    control = family_source(CONTROL_N)
    print(json.dumps(dict(progress="full-public-family-control", factor=control["factor"],
        stage=control["stage"], modulus=control["modulus"],
        signed_giants=control["constructed_signed_giants"], babies=control["baby_length"],
        milliseconds=control["milliseconds"])), flush=True)
    reference = reference_control(control)
    baseline = PARENT["centered_source"](CONTROL_N)
    assert baseline["factor"] in (reference["reference_p"], reference["reference_q"])
    assert source_inventory() == sources, "source changed during replay"
    validation = dict(public_modular_relation_cases=relation_cases,
        emitted_vectors_checked=emitted, small_public_sources=len(small_sources),
        small_public_outcomes=dict(outcomes), full_failure_controls=1,
        private_factors_used_only_as_references=True)
    report = dict(replay_id=REPLAY_ID, source_sha256=sources, validation=validation,
        scope="Complete intermediate-row constructor and fixed short-window coverage counterexample",
        one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False,
        is_bit_complexity_certificate=False, is_formal_machine_refinement=False,
        intermediate_row_validity_lean=True, complete_control_column_gcd_one_lean=True,
        control=control, reference_control=reference, centered_parent_baseline=baseline,
        small_public_sources=small_sources,
        limitations="This source is an exploratory N-only short-window detector, not the universal project factorizer. All modulus-prime search, Euclidean intermediates, lifts, both public centers, signed powers, polynomial construction, evaluation and GCD checks occur inside its timer and native ledgers. The literal semiprime has no local collision in the complete public family for any signed index in [-269,269]; Lean proves every original column product is a unit and has GCD 1. It also checks both actual base and baby orders, so period saturation is not the failure. The smaller tested row families are diagnostic, and the measured row counts are not a proved asymptotic bit bound. This rules out this particular m-window coverage claim on this particular input, not an O(C*m) family for every C, every cancellation construction, other bases/windows/moduli, or all one-sixth factoring algorithms. The prior public centered source still returns a factor on the same N with its different prescribed modulus and longer certified window; its timing is recorded separately and is not an equal-layout speed comparison. All earlier positive proofs and pinned artifacts remain unchanged. The full guaranteed arbitrary-ratio every-run one-sixth bit theorem remains open.")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources), validation=validation, control=control,
        reference_control=reference, centered_parent_baseline=baseline,
        one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()
