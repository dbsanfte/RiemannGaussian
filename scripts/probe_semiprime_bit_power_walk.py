#!/usr/bin/env python3
"""Replay bit-only powers/walks with physical-width primitive clocks.

Intermediate residues are Boolean words throughout both loops. Initial
public-word/template encoding, final row decoding and label assignment
are explicit legacy interfaces, without a complete bit certificate.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-bit-division-audit.json"
DIV = runpy.run_path(str(ROOT/"scripts/probe_semiprime_bit_division.py"))
SQRT, CONSTRUCTION, PARENT = DIV["SQRT"], DIV["CONSTRUCTION"], DIV["PARENT"]
encode_bits, decode_bits = DIV["encode_bits"], DIV["decode_bits"]
bit_length, bit_cost = DIV["bit_length"], DIV["bit_cost"]
divide_bits, mod_mul_bits = DIV["divide_bits"], DIV["mod_mul_bits"]
REPLAY_ID = 202610032101


def unit_template(length):
    result = None
    for _ in range(length):
        result = (None, result)
    return result


def record_division(xs, modulus, events):
    report = divide_bits(xs, modulus)
    if events is not None:
        events.append(dict(kind="div", left=xs, modulus=modulus, report=report))
    return report


def record_product(xs, ys, modulus, events):
    report = mod_mul_bits(xs, ys, modulus)
    if events is not None:
        events.append(dict(kind="mul", left=xs, right=ys, modulus=modulus, report=report))
    return report


def power_bits(modulus, a, exponent, events=None):
    if exponent is None:
        one = record_division((True, None), modulus, events)
        return dict(bits=one["remainder"], clock=one["clock"]+2,
                    multiplications=0, reductions=1, rounds=0)
    child = power_bits(modulus, a, exponent[1], events)
    square = record_product(child["bits"], child["bits"], modulus, events)
    if exponent[0]:
        normal = record_division(a, modulus, events)
        product = record_product(square["division"]["remainder"], normal["remainder"], modulus, events)
        return dict(bits=product["division"]["remainder"],
                    clock=child["clock"]+square["clock"]+normal["clock"]+product["clock"]+3,
                    multiplications=child["multiplications"]+2,
                    reductions=child["reductions"]+3, rounds=child["rounds"]+1)
    return dict(bits=square["division"]["remainder"], clock=child["clock"]+square["clock"]+3,
                multiplications=child["multiplications"]+1,
                reductions=child["reductions"]+1, rounds=child["rounds"]+1)


def walk_bits(modulus, start, step, template, events=None):
    if template is None:
        return dict(residues=None, clock=1, multiplications=0, reductions=0)
    current = record_division(start, modulus, events)
    if template[1] is None:
        return dict(residues=(current["remainder"], None), clock=current["clock"]+3,
                    multiplications=0, reductions=1)
    advance = record_product(current["remainder"], step, modulus, events)
    tail = walk_bits(modulus, advance["division"]["remainder"], step, template[1], events)
    return dict(residues=(current["remainder"], tail["residues"]),
                clock=current["clock"]+advance["clock"]+tail["clock"]+3,
                multiplications=tail["multiplications"]+1, reductions=tail["reductions"]+2)


def rows_values(rows):
    values = []
    while rows is not None:
        values.append(decode_bits(rows[0]))
        rows = rows[1]
    return values


def rows_cells(rows):
    cells = 0
    while rows is not None:
        cells += bit_length(rows[0])
        rows = rows[1]
    return cells


def significant_width(bits):
    # Legacy report instrumentation: scan Boolean cells, without decoding
    # a native product value. These visits have their own retained count.
    position, width = 0, 0
    while bits is not None:
        position += 1
        if bits[0]:
            width = position
        bits = bits[1]
    return width, position


def check_power(modulus, a, exponent, report):
    n, av, e = decode_bits(modulus), decode_bits(a), decode_bits(exponent)
    length = bit_length(exponent)
    assert decode_bits(report["bits"]) == (pow(av, e, n) if n else av**e)
    assert report["rounds"] == length
    assert length <= report["multiplications"] <= 2*length
    assert report["reductions"] <= 3*length+1
    assert report["reductions"]+length == 2*report["multiplications"]+1
    if length == e.bit_length():
        reference = CONSTRUCTION["counted_power"](n, av, e) if n else None
        if reference is not None:
            for key, refkey in (("multiplications", "multiplications"),
                                ("reductions", "reductions"), ("rounds", "halvings")):
                assert report[key] == reference[refkey]
    if n:
        width = max(bit_length(modulus), bit_length(a))
        assert bit_length(report["bits"]) == bit_length(modulus)
        assert report["clock"] <= length*(264*(width+1)**2+7)+72*(width+1)**2+2
        assert report["clock"] <= 272*(length+1)*(width+1)**2


def check_walk(modulus, start, step, template, report):
    n, av, sv = decode_bits(modulus), decode_bits(start), decode_bits(step)
    length = bit_length(template)
    expected = [(av % n)*pow(sv, i, n) % n if n else av*sv**i for i in range(length)]
    assert rows_values(report["residues"]) == expected
    assert report["multiplications"] == max(length-1, 0)
    assert report["reductions"] == length+max(length-1, 0)
    if n:
        width = max(bit_length(modulus), bit_length(start), bit_length(step))
        assert rows_cells(report["residues"]) == length*bit_length(modulus)
        assert report["clock"] <= length*(168*(width+1)**2+5)+1


def validate_primitives():
    powers, walks = 0, 0
    for n in (1, 2, 3, 4, 5, 8, 9, 17, 35, 143):
        for a in range(13):
            for e in range(16):
                for padding in ((0, 0, 0), (1, 2, 1)):
                    modulus, aw, ew = (encode_bits(v, p) for v, p in zip((n, a, e), padding))
                    check_power(modulus, aw, ew, power_bits(modulus, aw, ew))
                    powers += 1
    for a in range(8):
        for e in range(8):
            modulus, aw, ew = encode_bits(0), encode_bits(a), encode_bits(e)
            check_power(modulus, aw, ew, power_bits(modulus, aw, ew))
            powers += 1
    for width in (32, 64, 128, 256):
        n = (1 << width)-159
        for e in (0, 1, 17, 1025):
            modulus, aw, ew = encode_bits(n, 1), encode_bits(n-2), encode_bits(e, 2)
            check_power(modulus, aw, ew, power_bits(modulus, aw, ew))
            powers += 1
    for e, padding in ((0, 256), ((1 << 128)+5, 3)):
        modulus, aw, ew = encode_bits(143), encode_bits(7), encode_bits(e, padding)
        check_power(modulus, aw, ew, power_bits(modulus, aw, ew))
        powers += 1
    for n in (0, 1, 2, 5, 8, 17, 143):
        for start in range(9):
            for step in range(5):
                for length in range(7):
                    for padding in (0, 2):
                        modulus, aw, sw = (encode_bits(v, padding) for v in (n, start, step))
                        template = unit_template(length)
                        check_walk(modulus, aw, sw, template, walk_bits(modulus, aw, sw, template))
                        walks += 1
    return dict(power_cases=powers, walk_cases=walks, largest_modulus_word_bits=257,
                largest_physical_exponent_bits=256, padded_and_zero_moduli_checked=True)


def public_packet(n):
    scope = CONSTRUCTION["build_source"].__globals__
    prior_power, prior_walk = scope["counted_power"], scope["counted_walk"]
    powers, walks, events = [], [], []
    moduli, templates = {}, {}
    boundary = dict(initial_encode_bit_cells=0, exponent_encode_bit_cells=0,
                    final_decode_digit_visits=0, final_decoded_words=0,
                    template_cells=0, report_scan_bit_visits=0)

    def modulus_word(value):
        if value not in moduli:
            moduli[value] = encode_bits(value)
            boundary["initial_encode_bit_cells"] += value.bit_length()
        return moduli[value]

    def maximum_product_width(start):
        maximum = 0
        for event in events[start:]:
            if event["kind"] == "mul":
                width, visits = significant_width(event["report"]["product"]["bits"])
                maximum = max(maximum, width)
                boundary["report_scan_bit_visits"] += visits
        return maximum

    def counted_power(modulus, a, exponent):
        mw, aw, ew = modulus_word(modulus), encode_bits(a), encode_bits(exponent)
        boundary["initial_encode_bit_cells"] += a.bit_length()
        boundary["exponent_encode_bit_cells"] += exponent.bit_length()
        event_start = len(events)
        report = power_bits(mw, aw, ew, events)
        value = decode_bits(report["bits"])
        boundary["final_decode_digit_visits"] += bit_length(report["bits"])
        boundary["final_decoded_words"] += 1
        powers.append(dict(modulus=mw, base=aw, exponent=ew, report=report))
        return dict(value=value, multiplications=report["multiplications"], halvings=report["rounds"],
                    reductions=report["reductions"], max_product_bits=maximum_product_width(event_start))

    def counted_walk(modulus, start, step, length, index=0):
        if length not in templates:
            templates[length] = unit_template(length)
            boundary["template_cells"] += length
        if not walks:
            sw, tw = (True, None), powers[0]["base"]
        else:
            assert len(walks) == 1
            sw, tw = powers[0]["report"]["bits"], powers[1]["report"]["bits"]
        mw, template = modulus_word(modulus), templates[length]
        event_start = len(events)
        report = walk_bits(mw, sw, tw, template, events)
        values = rows_values(report["residues"])
        boundary["final_decode_digit_visits"] += rows_cells(report["residues"])
        boundary["final_decoded_words"] += len(values)
        walks.append(dict(modulus=mw, start=sw, step=tw, template=template, report=report,
                          expected_inputs=(start, step, length, index)))
        return dict(records=[(value, index+i) for i, value in enumerate(values)],
                    multiplications=report["multiplications"], reductions=report["reductions"],
                    max_product_bits=maximum_product_width(event_start))

    scope["counted_power"], scope["counted_walk"] = counted_power, counted_walk
    try:
        actual = SQRT["public_packet"](n)
    finally:
        scope["counted_power"], scope["counted_walk"] = prior_power, prior_walk
    # The inherited timer stops before native references and ledger hashing.
    window = actual["parent"]["source"]
    if window is None:
        assert not powers and not walks and not events
        return actual
    assert len(powers) == len(walks) == 2 and len(moduli) == len(templates) == 1
    width = window["N"].bit_length()
    for power in powers:
        check_power(power["modulus"], power["base"], power["exponent"], power["report"])
    for walk in walks:
        check_walk(walk["modulus"], walk["start"], walk["step"], walk["template"], walk["report"])
        start, step, length, index = walk["expected_inputs"]
        assert decode_bits(walk["start"]) == start and decode_bits(walk["step"]) == step
        assert bit_length(walk["template"]) == length and index == 0
    products, reductions, ledger = 0, 0, []
    for event in events:
        if event["kind"] == "mul":
            xs, ys, mw, report = event["left"], event["right"], event["modulus"], event["report"]
            av, bv, nv = decode_bits(xs), decode_bits(ys), decode_bits(mw)
            assert decode_bits(report["product"]["bits"]) == av*bv
            assert bit_cost(report["product"]) <= 24*(width+1)**2+1
            DIV["check_div"](report["product"]["bits"], mw, report["division"])
            assert decode_bits(report["division"]["remainder"]) == av*bv % nv
            assert max(bit_length(xs), bit_length(ys), bit_length(mw)) <= width
            assert report["clock"] <= 96*(width+1)**2+2
            products += 1
            ledger.append(("mul", av, bv, nv, decode_bits(report["division"]["remainder"])))
        else:
            xs, mw, report = event["left"], event["modulus"], event["report"]
            DIV["check_div"](xs, mw, report)
            assert bit_length(xs) <= width
            assert report["clock"] <= 72*(width+1)**2
            ledger.append(("div", decode_bits(xs), decode_bits(mw), decode_bits(report["remainder"])))
        reductions += 1
    raw = window["construction"]["arithmetic"]
    assert products == raw["multiplications"] and reductions == raw["reductions"]
    centre_bits, block_bits = (bit_length(p["exponent"]) for p in powers)
    rows = bit_length(walks[0]["template"])
    clock = sum(p["report"]["clock"] for p in powers)+sum(w["report"]["clock"] for w in walks)+2
    bound = 272*(centre_bits+block_bits+2)*(width+1)**2+2*rows*(168*(width+1)**2+5)+4
    assert clock <= bound
    summary = dict(input_bits=width, centre_exponent_bits=centre_bits, block_exponent_bits=block_bits,
                   rows_per_axis=rows, products=products, reductions=reductions,
                   power_rounds=centre_bits+block_bits, primitive_clock=clock, primitive_clock_bound=bound,
                   retained_residue_bit_cells=sum(rows_cells(w["report"]["residues"]) for w in walks),
                   intermediate_native_encodes=0, intermediate_native_decodes=0,
                   native_raw_quotient_queries=0, native_raw_remainder_queries=0,
                   operand_result_sha256=hashlib.sha256(json.dumps(ledger).encode()).hexdigest(),
                   legacy_boundary_interface=True, is_complete_bit_certificate=False, **boundary)
    assert summary["retained_residue_bit_cells"] == 2*rows*width
    assert boundary["report_scan_bit_visits"] <= 3*width*products
    window["construction"]["bit_power_walk"] = summary
    return actual


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeBitPowerWalk.lean",
                  "scripts/CheckSemiprimeBitPowerWalk.lean", "scripts/probe_semiprime_bit_power_walk.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources, primitives = source_inventory(), validate_primitives()
    prior = json.loads((ROOT/PARENT_AUDIT).read_text())
    counts, squares = Counter(), 0
    primes = list(primerange(2, 200))
    for i, p in enumerate(primes):
        for q in primes[i:]:
            actual = public_packet(p*q)
            PARENT["check_packet"](actual, p, q)
            counts[actual["status"]] += 1
            squares += int(p == q)
    populations, binary_rows = {}, []
    for name in ("inputs", "controls", "positive_controls", "negative_controls", "wrapped_controls"):
        population = []
        for previous in prior[name]:
            p, q = previous["reference_p"], previous["reference_q"]
            actual = public_packet(p*q)
            PARENT["check_packet"](actual, p, q)
            assert (actual["factor"], actual["status"]) == (previous["factor"], previous["status"])
            window, old_window = actual["parent"]["source"], previous["parent"]["source"]
            if window is not None:
                for key in ("active_base", "centre", "target", "inverse_step", "babies", "giants",
                            "collision", "candidate", "factor"):
                    assert json.dumps(window[key]) == json.dumps(old_window[key]), key
                for key, value in old_window["construction"].items():
                    if key not in ("bit_arithmetic", "bit_division"):
                        assert window["construction"][key] == value, key
                binary_rows.append(dict(original_N=p*q, leaf_N=window["N"], leaf_width=window["width"],
                                        **window["construction"]["bit_power_walk"]))
            actual.update(reference_p=p, reference_q=q)
            if "regime" in previous:
                actual["regime"] = previous["regime"]
            population.append(actual)
        populations[name] = population
    assert len(binary_rows) == 5
    assert source_inventory() == sources, "source changed during the replay"
    result = dict(replay_id=REPLAY_ID, scope="Bit-only raw powering and geometric row walks",
        one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False, is_bit_complexity_certificate=False,
        source_sha256=sources, validation=dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
            status_counts=dict(counts), outcomes_preserved=True, constructed_sources=len(binary_rows), **primitives),
        binary_rows=binary_rows,
        summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
        timing_protocol="The two raw powers and two row walks retain Boolean words throughout. Initial modulus/base/exponent and row-template encoding, final output decoding and legacy label assignment are timed boundary interfaces. Native references, ledger hashing, private factors, periods and source/trace checks are outside the inherited whole-public-route timer. Report width scans are timed and separately retained, outside the compiled primitive-loop clock.",
        limitations="Lean proves literal modular powers, all raw residue values, physical-width invariants, scalar counts and composed gate/cell/test clocks for supplied bit words and templates. Initial public-input encoding/template construction, final natural/label interfaces and report scans have no new complete bit certificate. Concrete machine execution, other pipeline arithmetic, sorting, polynomial work, routing/descent, transport and universal recovery remain required. Frozen outcomes and prior arithmetic/root reports are preserved; old mixed-interface bit diagnostics are replaced by the fresh loop summary. The 61-bit negative survives; no new exponent or software speed claim is made.",
        **populations)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(validation=result["validation"], source_pins=len(sources), binary_rows=binary_rows,
                          surviving_negative=populations["negative_controls"][0]["N"], one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()
