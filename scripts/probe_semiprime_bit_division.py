#!/usr/bin/env python3
"""Check Boolean restoring division and replace raw row residue updates.

All raw row products and general modulus updates use Boolean circuits and
bit-cell primitives. Legacy integer conversions, exponent/label interfaces,
other pipeline arithmetic and universal coverage remain separate obligations.
The charged primitive model is not a machine execution certificate.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-bit-arithmetic-audit.json"
ARITH = runpy.run_path(str(ROOT/"scripts/probe_semiprime_bit_arithmetic.py"))
SQRT = ARITH["SQRT"]
CONSTRUCTION = ARITH["CONSTRUCTION"]
PARENT = ARITH["PARENT"]
REPLAY_ID = 202610032001
encode_bits = ARITH["encode_bits"]
decode_bits = ARITH["decode_bits"]
bit_length = ARITH["bit_length"]
bit_cost = ARITH["bit_cost"]
mul_bits = ARITH["mul_bits"]


def full_subtractor(x, y, borrow):
    parity = x != y
    digit = parity != borrow
    inverted = not x
    either = y or borrow
    underflow = inverted and either
    both = y and borrow
    next_borrow = underflow or both
    return digit, next_borrow


def sub_bits(xs, ys, borrow=False):
    if xs is None and ys is None:
        return dict(result=dict(bits=None, gates=0, reads=0, writes=0, tests=2), borrow=borrow)
    x, xt = xs if xs is not None else (False, None)
    y, yt = ys if ys is not None else (False, None)
    digit, next_borrow = full_subtractor(x, y, borrow)
    tail = sub_bits(xt, yt, next_borrow)
    report = tail["result"]
    return dict(result=dict(bits=(digit, report["bits"]), gates=report["gates"]+7,
                            reads=report["reads"]+int(xs is not None)+int(ys is not None),
                            writes=report["writes"]+1, tests=report["tests"]+2),
                borrow=tail["borrow"])


def fit_bits(xs, template):
    if template is None:
        return dict(bits=None, gates=0, reads=0, writes=0, tests=1)
    x, xt = xs if xs is not None else (False, None)
    tail = fit_bits(xt, template[1])
    return dict(bits=(x, tail["bits"]), gates=tail["gates"],
                reads=tail["reads"]+int(xs is not None), writes=tail["writes"]+1,
                tests=tail["tests"]+2)


def nonzero_bits(bits):
    if bits is None:
        return dict(nonzero=False, clock=1)
    child = nonzero_bits(bits[1])
    return dict(nonzero=bits[0] or child["nonzero"], clock=child["clock"]+3)


def divide_loop(xs, divisor):
    if xs is None:
        zero = fit_bits(None, divisor)
        return dict(quotient=None, remainder=zero["bits"], clock=bit_cost(zero)+1, rounds=0)
    bit, xt = xs
    child = divide_loop(xt, divisor)
    expanded = (bit, child["remainder"])
    difference = sub_bits(expanded, divisor)
    if difference["borrow"]:
        fitted = fit_bits(expanded, divisor)
        quotient_bit = False
    else:
        fitted = fit_bits(difference["result"]["bits"], divisor)
        quotient_bit = True
    return dict(quotient=(quotient_bit, child["quotient"]), remainder=fitted["bits"],
                clock=child["clock"]+bit_cost(difference["result"])+bit_cost(fitted)+5,
                rounds=child["rounds"]+1)


def divide_bits(xs, ys):
    check = nonzero_bits(ys)
    if not check["nonzero"]:
        return dict(quotient=None, remainder=xs, clock=check["clock"]+1, rounds=0)
    report = divide_loop(xs, ys)
    report["clock"] += check["clock"]+1
    return report


def mod_mul_bits(xs, ys, modulus):
    product = mul_bits(xs, ys)
    division = divide_bits(product["bits"], modulus)
    return dict(product=product, division=division,
                clock=bit_cost(product)+division["clock"]+1)


def check_sub(xs, ys, borrow, report):
    a, b = decode_bits(xs), decode_bits(ys)
    m, n = bit_length(xs), bit_length(ys)
    width = max(m, n)
    result = report["result"]
    value = decode_bits(result["bits"])
    assert a+(1 << width)*int(report["borrow"]) == b+int(borrow)+value
    assert report["borrow"] == (a < b+int(borrow))
    assert value == (a-b-int(borrow)) % (1 << width)
    assert result["gates"] == 7*width and result["reads"] == m+n
    assert result["writes"] == bit_length(result["bits"]) == width
    assert result["tests"] == 2*width+2
    assert bit_cost(result) <= 12*width+2


def check_fit(xs, template, report):
    width = bit_length(template)
    assert bit_length(report["bits"]) == width
    assert decode_bits(report["bits"]) == decode_bits(xs) % (1 << width)
    assert report["gates"] == 0 and report["reads"] <= width
    assert report["writes"] == width and report["tests"] == 2*width+1
    assert bit_cost(report) <= 4*width+1


def check_div(xs, ys, report):
    a, b = decode_bits(xs), decode_bits(ys)
    m, n = bit_length(xs), bit_length(ys)
    quotient, remainder = decode_bits(report["quotient"]), decode_bits(report["remainder"])
    assert quotient == (a//b if b else 0)
    assert remainder == (a % b if b else a)
    assert report["clock"] <= m*(16*n+20)+7*n+4
    if b:
        assert bit_length(report["quotient"]) == m
        assert bit_length(report["remainder"]) == n
        assert report["rounds"] == m
        assert b*quotient+remainder == a and remainder < b
    else:
        assert report["quotient"] is None and report["remainder"] is xs
        assert report["rounds"] == 0


def check_mod_mul(xs, ys, modulus, report):
    a, b, n = decode_bits(xs), decode_bits(ys), decode_bits(modulus)
    width = max(bit_length(xs), bit_length(ys), bit_length(modulus))
    ARITH["check_mul"](xs, ys, report["product"])
    check_div(report["product"]["bits"], modulus, report["division"])
    expected = a*b % n if n else a*b
    assert decode_bits(report["division"]["remainder"]) == expected
    assert report["clock"] <= 96*(width+1)**2+2
    if n:
        assert bit_length(report["division"]["remainder"]) == bit_length(modulus)


def validate_primitives():
    subtractions = fits = divisions = modular_products = 0
    for x in (False, True):
        for y in (False, True):
            for borrow in (False, True):
                digit, next_borrow = full_subtractor(x, y, borrow)
                assert int(x)+2*int(next_borrow) == int(y)+int(borrow)+int(digit)
    for a in range(97):
        for b in range(97):
            for px, py in ((0, 0), (2, 3)):
                xs, ys = encode_bits(a, px), encode_bits(b, py)
                for borrow in (False, True):
                    check_sub(xs, ys, borrow, sub_bits(xs, ys, borrow))
                    subtractions += 1
    for a in range(257):
        for width in range(17):
            xs, template = encode_bits(a), encode_bits(0, width)
            check_fit(xs, template, fit_bits(xs, template))
            fits += 1
    for a in range(129):
        for b in range(65):
            for px, py in ((0, 0), (2, 3)):
                xs, ys = encode_bits(a, px), encode_bits(b, py)
                check_div(xs, ys, divide_bits(xs, ys))
                divisions += 1
    for a in range(33):
        for b in range(33):
            for n in (0, 1, 2, 3, 4, 5, 8, 9, 17, 35, 143):
                xs, ys, modulus = encode_bits(a), encode_bits(b, 1), encode_bits(n, 2)
                check_mod_mul(xs, ys, modulus, mod_mul_bits(xs, ys, modulus))
                modular_products += 1
    for width in (16, 32, 64, 128, 256, 512, 1024, 2048):
        a = (1 << width)-1
        for b in (0, 1, (1 << (width//2))+1, (1 << width)+7):
            xs, ys = encode_bits(a, 1), encode_bits(b, 2)
            check_div(xs, ys, divide_bits(xs, ys))
            divisions += 1
    return dict(full_subtractor_cases=8, subtraction_cases=subtractions,
                fitting_cases=fits, division_cases=divisions, modular_product_cases=modular_products,
                largest_dividend_input_bits=2049, padded_inputs_and_zero_divisors_checked=True)


def public_packet(n):
    scope = CONSTRUCTION["build_source"].__globals__
    prior_power, prior_walk = scope["counted_power"], scope["counted_walk"]
    products, divisions, moduli = [], [], {}

    def modulus_word(modulus):
        if modulus not in moduli:
            moduli[modulus] = encode_bits(modulus)
        return moduli[modulus]

    def binary_product(a, b):
        report = mul_bits(encode_bits(a), encode_bits(b))
        value = decode_bits(report["bits"])
        products.append(dict(a=a, b=b, value=value, left_bits=a.bit_length(), right_bits=b.bit_length(),
                             output_bits=bit_length(report["bits"]), gates=report["gates"],
                             reads=report["reads"], writes=report["writes"], tests=report["tests"],
                             clock=bit_cost(report), encode_bit_cells=a.bit_length()+b.bit_length(),
                             decode_digit_visits=bit_length(report["bits"])))
        return value

    def binary_remainder(a, modulus):
        report = divide_bits(encode_bits(a), modulus_word(modulus))
        value = decode_bits(report["remainder"])
        divisions.append(dict(dividend=a, modulus=modulus, remainder=value,
                              dividend_bits=a.bit_length(), divisor_bits=modulus.bit_length(),
                              quotient=report["quotient"], quotient_bits=bit_length(report["quotient"]),
                              remainder_bits=bit_length(report["remainder"]), clock=report["clock"],
                              rounds=report["rounds"], encode_bit_cells=a.bit_length(),
                              decode_digit_visits=bit_length(report["remainder"])))
        return value

    def counted_power(modulus, a, exponent):
        if exponent == 0:
            return dict(value=binary_remainder(1, modulus), multiplications=0, halvings=0,
                        reductions=1, max_product_bits=0)
        child = counted_power(modulus, a, exponent//2)
        square = binary_product(child["value"], child["value"])
        value = binary_remainder(square, modulus)
        extra, reductions = 1, 1
        max_bits = max(child["max_product_bits"], square.bit_length())
        if exponent & 1:
            normal = binary_remainder(a, modulus)
            product = binary_product(value, normal)
            max_bits = max(max_bits, product.bit_length())
            value = binary_remainder(product, modulus)
            extra, reductions = 2, 3
        return dict(value=value, multiplications=child["multiplications"]+extra,
                    halvings=child["halvings"]+1, reductions=child["reductions"]+reductions,
                    max_product_bits=max_bits)

    def counted_walk(modulus, start, step, length, index=0):
        records, multiplications, reductions, max_bits = [], 0, 0, 0
        for offset in range(length):
            current = binary_remainder(start, modulus)
            reductions += 1
            records.append((current, index+offset))
            if offset+1 < length:
                product = binary_product(current, step)
                max_bits = max(max_bits, product.bit_length())
                start = binary_remainder(product, modulus)
                multiplications += 1
                reductions += 1
        return dict(records=records, multiplications=multiplications, reductions=reductions,
                    max_product_bits=max_bits)

    scope["counted_power"], scope["counted_walk"] = counted_power, counted_walk
    try:
        actual = SQRT["public_packet"](n)
    finally:
        scope["counted_power"], scope["counted_walk"] = prior_power, prior_walk
    # The inherited timer ends before all native quotient/product references.
    window = actual["parent"]["source"]
    if window is None:
        assert not products and not divisions
        return actual
    width = window["N"].bit_length()
    for event in products:
        assert event["value"] == event["a"]*event["b"]
        assert max(event["left_bits"], event["right_bits"]) <= width
        assert event["output_bits"] <= 3*width
        assert event["clock"] <= 24*(width+1)**2+1
    for event in divisions:
        assert event["remainder"] == event["dividend"] % event["modulus"]
        assert decode_bits(event["quotient"]) == event["dividend"]//event["modulus"]
        assert event["dividend_bits"] <= 3*width and event["divisor_bits"] <= width
        assert event["remainder_bits"] == event["divisor_bits"]
        assert event["clock"] <= 72*(width+1)**2
    raw = window["construction"]["arithmetic"]
    assert len(products) == raw["multiplications"] and len(divisions) == raw["reductions"]
    product_summary = {key: sum(event[key] for event in products) for key in
                       ("gates", "reads", "writes", "tests", "clock", "encode_bit_cells", "decode_digit_visits")}
    product_summary.update(scalar_products=len(products), input_bits=width,
        largest_operand_bits=max(max(event["left_bits"], event["right_bits"]) for event in products),
        largest_output_bits=max(event["output_bits"] for event in products),
        primitive_clock_bound=len(products)*(24*(width+1)**2+1),
        operand_result_sha256=hashlib.sha256(json.dumps(
            [(event["a"], event["b"], event["value"]) for event in products]).encode()).hexdigest(),
        boolean_product_oracles=0, native_remainder_calls=0, legacy_integer_interface=True,
        is_complete_bit_certificate=False)
    division_summary = dict(remainder_updates=len(divisions),
        clock=sum(event["clock"] for event in divisions),
        rounds=sum(event["rounds"] for event in divisions),
        primitive_clock_bound=len(divisions)*72*(width+1)**2,
        encode_bit_cells=sum(event["encode_bit_cells"] for event in divisions),
        decode_digit_visits=sum(event["decode_digit_visits"] for event in divisions),
        modulus_encoding_cells=sum(value.bit_length() for value in moduli),
        largest_dividend_bits=max(event["dividend_bits"] for event in divisions),
        largest_divisor_bits=max(event["divisor_bits"] for event in divisions),
        native_raw_quotient_queries=0, native_raw_remainder_queries=0,
        operand_result_sha256=hashlib.sha256(json.dumps(
            [(event["dividend"], event["modulus"], event["remainder"]) for event in divisions]).encode()).hexdigest(),
        legacy_integer_interface=True, is_complete_bit_certificate=False)
    assert division_summary["clock"] <= division_summary["primitive_clock_bound"]
    division_summary["combined_product_remainder_clock"] = division_summary["clock"]+product_summary["clock"]
    window["construction"].update(bit_arithmetic=product_summary, bit_division=division_summary)
    return actual


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeBitDivision.lean",
                  "scripts/CheckSemiprimeBitDivision.lean", "scripts/probe_semiprime_bit_division.py"))
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
    populations, division_rows = {}, []
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
                    if key == "bit_arithmetic":
                        for field, old in value.items():
                            if field == "native_remainder_calls":
                                assert window["construction"][key][field] == 0
                            else:
                                assert window["construction"][key][field] == old, field
                    else:
                        assert window["construction"][key] == value, key
                division_rows.append(dict(original_N=p*q, leaf_N=window["N"], leaf_width=window["width"],
                                          **window["construction"]["bit_division"]))
            actual.update(reference_p=p, reference_q=q)
            if "regime" in previous:
                actual["regime"] = previous["regime"]
            population.append(actual)
        populations[name] = population
    assert len(division_rows) == 5
    result = dict(replay_id=REPLAY_ID, scope="Boolean subtraction/division backend and raw residue-update substitution",
        one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False, is_bit_complexity_certificate=False,
        source_sha256=sources, validation=dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
            status_counts=dict(counts), outcomes_preserved=True, constructed_sources=len(division_rows), **primitives),
        division_rows=division_rows,
        summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
        timing_protocol="Only raw powering/walk functions are replaced inside the frozen counted builder. Every raw product and every general modulus-N residue update uses the linked-Boolean backend. The inherited root/decoder adapter times the complete N-only route, bit computations and reports, legacy conversion interfaces, cached residue continuation and transport. Native product, quotient/remainder references, private factors, periods, offsets, trace checks and ledger hashes are outside its timer. Exponent/label and other preceding pipeline interfaces retain their separate obligations.",
        limitations="Lean proves the exact Boolean difference/borrow, paid fixed-width fitting, zero detection, quotient/remainder, modular product and composed primitive clocks. These are not machine-execution or full public factorizer bit-cost certificates. Legacy integer conversion, exponent/label interfaces, other pipeline arithmetic, sorting, polynomial work, routing/descent, transport and universal recovery remain required. No new exponent, unbiased corpus or software speed comparison is established; the 61-bit negative survives.",
        **populations)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(validation=result["validation"], source_pins=len(sources), division_rows=division_rows,
                          surviving_negative=populations["negative_controls"][0]["N"], one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()
