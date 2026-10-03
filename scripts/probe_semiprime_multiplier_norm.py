#!/usr/bin/env python3
"""Exact shared multiplier norms, preserving universal proper-hit recovery.

Full blocks and a separately shared tail keep the original interval exact.
Only N enters whole-route timing. Explicit group input counts have B^(3/2)
scale; native polynomial work and the full sixth-root bit theorem are open.
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
PARENT_AUDIT = "docs/semiprime-totient-multipliers-audit.json"
MULT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_totient_multipliers.py"))
BIT, PARENT, BATCH, WINDOW = MULT["BIT"], MULT["PARENT"], MULT["BATCH"], MULT["WINDOW"]
SHARED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_shared_interval_jet.py"))
JET = SHARED["JET"]
REPLAY_ID = 202610032301


class ScalarLedger:
    """Native scalar ledger, without a complete Boolean/machine certificate."""

    def __init__(self, n):
        self.n = n
        self.products = self.reductions = self.powers = self.power_rounds = self.inverses = 0
        self.max_product_bits = 0

    def mul(self, a, b):
        product = int(a)*int(b)
        self.products += 1
        self.reductions += 1
        self.max_product_bits = max(self.max_product_bits, abs(product).bit_length())
        return product % self.n

    def power(self, a, e):
        report = BIT["CONSTRUCTION"]["counted_power"](self.n, a, e)
        self.powers += 1
        self.products += report["multiplications"]
        self.reductions += report["reductions"]
        self.power_rounds += report["halvings"]
        self.max_product_bits = max(self.max_product_bits, report["max_product_bits"])
        return report["value"]

    def inverse(self, a):
        self.inverses += 1
        return pow(a, -1, self.n)

    def stats(self):
        return dict(native_scalar_products=self.products, native_scalar_reductions=self.reductions,
                    native_scalar_powers=self.powers, native_power_rounds=self.power_rounds,
                    native_scalar_inverses=self.inverses, max_scalar_product_bits=self.max_product_bits,
                    is_complete_bit_certificate=False)


def baby_jet(alpha, width, n, batch, ring):
    """One shared polynomial and its logarithmic base derivative."""
    level, y = [], 1
    for u in range(width):
        level.append(([(-y) % n, 1], [(-ring.mul(u % n, y)) % n, 0]))
        y = ring.mul(y, alpha)
    while len(level) > 1:
        new = []
        for i in range(0, len(level)-1, 2):
            a, e = level[i]
            b, f = level[i+1]
            new.append((batch.mul(a, b), JET["add_polynomials"](
                batch.mul(e, b), batch.mul(a, f), n)))
        if len(level) % 2:
            new.append(level[-1])
        level = new
    polynomial, marked = level[0] if level else ([1], [0])
    derivative = [ring.mul(i % n, polynomial[i]) for i in range(1, len(polynomial))]
    return polynomial, derivative, marked


def combine(left, right, ring):
    p, d, e = left
    q, f, g = right
    return (ring.mul(p, q), (ring.mul(d, q)+ring.mul(p, f)) % ring.n,
            (ring.mul(e, q)+ring.mul(p, g)) % ring.n)


def exact_shared_jets(n, alpha, targets, length, width, ring=None, inverse=None):
    """Two shared polynomials, exact full blocks and one exact shared tail."""
    if length < 0 or width <= 0:
        raise ValueError("nonnegative interval and positive width required")
    ring = ScalarLedger(n) if ring is None else ring
    inverse = ring.inverse(alpha) if inverse is None else inverse
    targets = list(targets)
    count = len(targets)
    blocks, tail = divmod(length, width)
    offset = blocks*width
    batch = BATCH["MonicBatch"](n)
    polynomials = baby_jet(alpha, width, n, batch, ring)
    shift = ring.power(inverse, width)
    points = []
    for x in targets:
        z = x
        for j in range(blocks):
            points.append(z)
            if j+1 < blocks:
                z = ring.mul(z, shift)
    values, derivatives, marked = SHARED["evaluate_three"](batch, polynomials, points)
    phase_step = ring.power(alpha, width*width)
    jets = []
    for row, x in enumerate(targets):
        current, phase, shift_power = (1, 0, 0), 1, 1
        for j in range(blocks):
            index = row*blocks+j
            z, p, d, e = points[index], values[index], derivatives[index], marked[index]
            scaled = (ring.mul(phase, p), ring.mul(ring.mul(phase, shift_power), d),
                      ring.mul(phase, (ring.mul((j*width*width) % n, p)+e-
                          ring.mul(ring.mul((j*width) % n, z), d)) % n))
            current = combine(current, scaled, ring)
            if j+1 < blocks:
                phase = ring.mul(phase, phase_step)
                shift_power = ring.mul(shift_power, shift)
        jets.append(current)
    tail_shift = ring.power(inverse, offset)
    tail_points = [ring.mul(x, tail_shift) for x in targets]
    if tail:
        tail_polynomials = baby_jet(alpha, tail, n, batch, ring)
        ps, ds, es = SHARED["evaluate_three"](batch, tail_polynomials, tail_points)
        tail_phase = ring.power(alpha, offset*tail)
        derivative_phase = ring.mul(tail_phase, tail_shift)
        for i, (z, p, d, e) in enumerate(zip(tail_points, ps, ds, es)):
            tail_jet = (ring.mul(tail_phase, p), ring.mul(derivative_phase, d),
                        ring.mul(tail_phase, (ring.mul((offset*tail) % n, p)+e-
                            ring.mul(ring.mul(offset % n, z), d)) % n))
            jets[i] = combine(jets[i], tail_jet, ring)
    inputs = width+len(points)+tail+len(tail_points)
    metrics = dict(row_count=count, interval_length=length, block_width=width, full_blocks=blocks,
                   tail_degree=tail, root_polynomials=1+int(tail > 0),
                   full_point_inputs=len(points), tail_point_inputs=len(tail_points),
                   constructed_point_inputs=len(points)+len(tail_points),
                   evaluated_point_inputs=len(points)+(len(tail_points) if tail else 0),
                   explicit_input_count=inputs, exact_interval=True, padded_interval=False,
                   explicit_interval_targets=0, explicit_pair_grid_products=0,
                   point_trees=int(bool(points))+int(bool(tail_points) and tail > 0), **batch.stats())
    assert len(jets) == count and inputs == width+count*blocks+tail+count
    assert metrics["constructed_point_inputs"] == count*(blocks+1)
    return dict(rows=[dict(x=x, product=p, target_derivative=d, base_derivative=e, length=length)
                      for x, (p, d, e) in zip(targets, jets)], metrics=metrics)


def decode_norm(n, row, index_width, ring):
    """Consume exactly the three computed scalars, with no norm recomputation."""
    divisor = math.gcd(n, row["product"])
    result = dict(factor=None, gcd_calls=1, x=row["x"])
    if 1 < divisor < n:
        result.update(factor=divisor, stage="product")
    elif row["product"] == 0:
        denominator = ring.mul(row["x"], row["target_derivative"])
        result["gcd_calls"] += 1
        if math.gcd(n, denominator) == 1:
            index = ring.mul((-row["base_derivative"]) % n, ring.inverse(denominator))
            recovery = BATCH["recovery"](n, list(range(1, index_width+1)),
                [(index+1-j*index_width) % n for j in range(index_width)])
            result.update(decoded_index=index, index_recovery=recovery)
            result["gcd_calls"] += recovery["metrics"]["gcd_calls"]
            if recovery["factor"] is not None:
                result.update(factor=recovery["factor"], stage="crt-index")
    return result


def build_norm_source(window, adaptive=True):
    n, b, alpha, beta = window["N"], window["width"], window["active_base"], window["target"]
    cap = (2*b)**2
    ring = ScalarLedger(n)
    inverse, beta_inverse = ring.inverse(alpha), ring.inverse(beta)
    centres, positive, negative = [], beta, beta_inverse
    for k in range(1, b+1):
        centres.extend((positive, negative))
        if k < b:
            positive, negative = ring.mul(positive, beta), ring.mul(negative, beta_inverse)
    groups, examined, offset, group_size, factor, successful = [], [], 0, 1, None, None
    while offset < len(centres):
        count = min(group_size, len(centres)-offset) if adaptive else len(centres)
        width = math.isqrt(count*cap)+1
        result = exact_shared_jets(n, alpha, centres[offset:offset+count], cap, width, ring, inverse)
        assert result["metrics"]["explicit_input_count"] <= 4*width
        assert result["metrics"]["explicit_input_count"]**2 <= 32*count*cap+32
        groups.append(dict(first_centre=offset, **result["metrics"]))
        for local, row in enumerate(result["rows"]):
            index = offset+local
            decoded = decode_norm(n, row, 2*b, ring)
            record = dict(multiplier=index//2+1, negative=bool(index % 2),
                          jet=row, decoded=decoded)
            examined.append(record)
            if decoded["factor"] is not None:
                factor, successful = decoded["factor"], record
                break
        if factor is not None:
            break
        offset += count
        group_size *= 2
    assert ring.max_product_bits <= 2*n.bit_length()
    totals = {key: sum(group[key] for group in groups)
              for key in ("full_point_inputs", "tail_point_inputs", "constructed_point_inputs",
                          "evaluated_point_inputs", "explicit_input_count", "root_polynomials",
                          "point_trees", "convolutions", "packed_coefficients", "monic_reductions")}
    totals.update(retained_signed_centres=len(centres), examined_norms=len(examined),
                  evaluated_norms=sum(group["row_count"] for group in groups),
                  norm_gcd_calls=sum(row["decoded"]["gcd_calls"] for row in examined),
                  full_quadratic_stream_points=4*b*b, groups=len(groups),
                  full_shared_input_count=(lambda m: m+2*b*(cap//m)+cap % m+2*b)(math.isqrt(2*b*cap)+1),
                  **ring.stats())
    return dict(N=n, width=b, interval_length=cap, centres=centres, factor=factor,
                groups=groups, examined=examined, successful_norm=successful,
                adaptive=adaptive, metrics=totals)


def public_packet(n):
    """Replace the expanded detector; pay the complete old N-only prefix."""
    start = time.perf_counter()
    parent = BIT["public_packet"](n)
    factor, source = parent["factor"], None
    metrics = dict(new_norm_sources=0, leaf_candidate_gcds=0,
                   transport_order_powers=0, transport_square_roots=0, transport_gcds=0)
    if factor is None:
        window = parent["parent"]["source"]
        assert window is not None and window["factor"] is None
        source = build_norm_source(window)
        metrics["new_norm_sources"] += 1
        if source["factor"] is not None:
            trace = parent["parent"]["parent"]["source"]["trace"]
            factor = WINDOW["PARENT"]["lift_factor"](trace, source["factor"], metrics)
    if factor is not None:
        assert 1 < factor < n and n % factor == 0
    return dict(N=n, width=parent["width"], parent=parent, source=source, factor=factor,
                status="factor" if factor is not None else "failure", metrics=metrics,
                elapsed_ms=1000*(time.perf_counter()-start))


def validate_components():
    rnd = random.Random(REPLAY_ID)
    groups, rows, layouts = 0, 0, 0
    for _ in range(192):
        n = rnd.choice((4, 9, 15, 25, 35, 49, 77, 143, 323))
        units = [a for a in range(1, n) if math.gcd(a, n) == 1]
        alpha = rnd.choice(units)
        targets = [rnd.randrange(n) for _ in range(rnd.randrange(1, 9))]
        length, width = rnd.randrange(65), rnd.randrange(1, 32)
        result = exact_shared_jets(n, alpha, targets, length, width)
        for actual in result["rows"]:
            assert (actual["product"], actual["target_derivative"], actual["base_derivative"]) == \
                JET["direct_jet"](n, alpha, actual["x"], length)
            rows += 1
        assert result["metrics"]["interval_length"] == length
        assert result["metrics"]["explicit_input_count"] == width+len(targets)*(length//width)+length % width+len(targets)
        groups += 1
    for b in range(1, 129):
        cap = (2*b)**2
        for count in sorted(set((1, 2, b, 2*b))):
            width = math.isqrt(count*cap)+1
            inputs = width+count*(cap//width)+cap % width+count
            assert 0 < width <= cap and inputs <= 4*width
            assert inputs**2 <= 32*count*cap+32
            if count == 2*b:
                assert 32*b**3 < inputs**2
            layouts += 1
    n, p, q, alpha, length, index_width = 10403, 101, 103, 2, 16, 4
    controls = []
    for name, left, right in (("saturated-distinct-indices", 3, 9),
                              ("shared-global-index", 3, 3),
                              ("left-only-root", 3, 20), ("right-only-root", 20, 9)):
        xp, xq = pow(alpha, left, p), pow(alpha, right, q)
        x = xp+p*((xq-xp)*pow(p, -1, q) % q)
        ring = ScalarLedger(n)
        row = exact_shared_jets(n, alpha, [x], length, 7, ring)["rows"][0]
        decoded = decode_norm(n, row, index_width, ring)
        assert (decoded["factor"] is None) == (name == "shared-global-index")
        if name == "saturated-distinct-indices":
            assert row["product"] == 0 and decoded["stage"] == "crt-index"
            assert decoded["decoded_index"] % p == left and decoded["decoded_index"] % q == right
        controls.append(dict(name=name, row=row, decoded=decoded))
    return dict(exact_shared_groups=groups, direct_three_channel_rows=rows,
                public_layout_cases=layouts, saturated_and_shared_controls=controls,
                zero_intervals_multiple_local_roots_and_zero_targets_checked=True)


def check_packet(actual, p, q):
    """All private and independent norm acquisition occurs after timing."""
    PARENT["check_packet"](actual["parent"], p, q)
    assert actual["N"] == p*q and actual["factor"] in (p, q)
    source = actual["source"]
    if source is None:
        assert actual["factor"] == actual["parent"]["factor"]
        return
    assert actual["parent"]["factor"] is None
    window = actual["parent"]["parent"]["source"]
    reference = actual["parent"]["residue_reference"]
    assert source["factor"] in (reference["local_p"], reference["local_q"])
    beta, n = window["target"], source["N"]
    assert source["centres"] == [x for k in range(1, source["width"]+1)
                                for x in (pow(beta, k, n), pow(pow(beta, -1, n), k, n))]
    chosen = {group["first_centre"] for group in source["groups"]}
    chosen.add(len(source["examined"])-1)
    for index in sorted(chosen):
        if index >= len(source["examined"]):
            continue
        actual_row = source["examined"][index]["jet"]
        independent = JET["interval_jet"](n, window["active_base"], actual_row["x"], source["interval_length"])
        for key in ("product", "target_derivative", "base_derivative"):
            assert actual_row[key] == independent[key], key
    source["independent_large_jets_checked"] = len(chosen)
    successful = source["successful_norm"]
    assert successful is not None and successful["decoded"]["factor"] == source["factor"]
    if successful["decoded"]["stage"] == "product":
        assert math.gcd(n, successful["jet"]["product"]) == source["factor"]
    source["private_reference"] = dict(local_p=reference["local_p"], local_q=reference["local_q"],
        left_order=reference["left_order"], right_order=reference["right_order"],
        true_offset=reference["true_offset"], acquisition="outside whole-public-route timing")


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeMultiplierNorm.lean",
                  "scripts/CheckSemiprimeMultiplierNorm.lean", "scripts/probe_semiprime_multiplier_norm.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources, components = source_inventory(), validate_components()
    prior = json.loads((ROOT/PARENT_AUDIT).read_text())
    counts, squares = Counter(), 0
    primes = list(primerange(2, 200))
    for i, p in enumerate(primes):
        for q in primes[i:]:
            actual = public_packet(p*q)
            check_packet(actual, p, q)
            counts[actual["status"]] += 1
            squares += int(p == q)
    populations, norm_sources, inherited_successes = {}, [], 0
    for name in ("inputs", "controls", "positive_controls", "negative_controls", "wrapped_controls"):
        population = []
        for previous in prior[name]:
            p, q = previous["reference_p"], previous["reference_q"]
            actual = public_packet(p*q)
            check_packet(actual, p, q)
            assert actual["factor"] == previous["factor"]
            assert (actual["parent"]["factor"], actual["parent"]["status"]) == \
                (previous["parent"]["factor"], previous["parent"]["status"])
            window, old = actual["parent"]["parent"]["source"], previous["parent"]["parent"]["source"]
            if window is not None:
                for key in ("active_base", "centre", "target", "inverse_step", "babies", "giants",
                            "collision", "candidate", "factor", "construction"):
                    assert json.dumps(window[key]) == json.dumps(old[key]), key
            if actual["source"] is None:
                inherited_successes += 1
            else:
                norm_sources.append(dict(original_N=p*q, leaf_N=actual["source"]["N"],
                    factor=actual["factor"], successful_norm=actual["source"]["successful_norm"],
                    **actual["source"]["metrics"]))
            actual.update(reference_p=p, reference_q=q)
            if "regime" in previous:
                actual["regime"] = previous["regime"]
            population.append(actual)
        populations[name] = population
    assert len(norm_sources) == 1
    assert populations["negative_controls"][0]["source"]["successful_norm"]["multiplier"] == 60
    assert source_inventory() == sources, "source changed during replay"
    result = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="Universal exact shared-norm replacement of the expanded signed-multiplier detector",
        one_sixth_guarantee="OPEN", universal_lean_specification=True,
        is_complete_semiprime_factorizer=True, is_bit_complexity_certificate=False,
        is_formal_machine_refinement=False,
        validation=dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
            status_counts=dict(counts), prior_final_factors_preserved=True,
            inherited_successes_preserved=inherited_successes, exact_norm_sources=len(norm_sources), **components),
        norm_sources=norm_sources, **populations,
        timing_protocol="Only N enters the outer timer. It wraps the whole old bit-power/walk and proper-residue public prefix, new public inverses and signed centre recurrences, exact shared full-block and tail polynomial/derivative construction, both point sources, all three-channel monic remainder evaluations, phase/offset corrections and retained triples, each norm GCD and possible unit inverse/ordinary index recovery, scalar-width diagnostics and complete original-input transport. Adaptive groups stop after the first recovered factor. Private factors, periods, offsets, cache comparison and independent large-interval jets are checked afterward. The expanded multiplier detector is not run first.",
        limitations="Lean proves exact norm/derivative algebra, universal list/ring public correctness, recovery of nonshared local roots on either side, exact tails, and explicit shared input upper/lower bounds with B^(3/2) scale. The Python shares each pair of baby/tail polynomials, evaluates three channels, and adapts group widths; all positive widths have the same compiled exact scalar meaning. Its native scalar/polynomial/packing operations, grouping/ordering, concrete machine refinement and whole-pipeline bit clock are not certified. Neither the improved input count nor the finite successful replay proves the requested every-run N^(1/6) rate.")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(validation=result["validation"], source_pins=len(sources),
                          norm_sources=norm_sources, one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()
