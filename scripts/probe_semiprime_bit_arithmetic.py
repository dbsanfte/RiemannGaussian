#!/usr/bin/env python3
"""Check Boolean-list arithmetic and replay raw row products with it.

The Boolean primitive model charges gates, bit reads/writes and branches.
The existing public route replaces only products in its two raw powers and
walks. Legacy integer conversion and native remainders remain explicit
unproved interfaces; this is not the whole factorizer's bit certificate.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import runpy
import sys

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-window-sqrt-audit.json"
SQRT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_window_sqrt.py"))
CONSTRUCTION = SQRT["CONSTRUCTION"]
PARENT = SQRT["PARENT"]
REPLAY_ID = 202610031901
sys.setrecursionlimit(20000)


def encode_bits(value, padding=0):
    # Integer-interface conversion, not part of the Boolean primitive proof.
    result = None
    for _ in range(padding):
        result = (False, result)
    for index in reversed(range(value.bit_length())):
        result = (bool((value >> index) & 1), result)
    return result


def decode_bits(bits):
    value, weight = 0, 1
    while bits is not None:
        value += int(bits[0])*weight
        weight <<= 1
        bits = bits[1]
    return value


def bit_length(bits):
    length = 0
    while bits is not None:
        length += 1
        bits = bits[1]
    return length


def full_adder(x, y, carry):
    parity = x != y
    digit = parity != carry
    both = x and y
    either = x or y
    propagated = carry and either
    next_carry = both or propagated
    return digit, next_carry


def bit_cost(report):
    return report["gates"]+report["reads"]+report["writes"]+report["tests"]


def add_bits(xs, ys, carry=False):
    if xs is None and ys is None:
        return dict(bits=(True, None) if carry else None,
                    gates=0, reads=0, writes=int(carry), tests=3)
    x, xt = xs if xs is not None else (False, None)
    y, yt = ys if ys is not None else (False, None)
    digit, next_carry = full_adder(x, y, carry)
    tail = add_bits(xt, yt, next_carry)
    return dict(bits=(digit, tail["bits"]), gates=tail["gates"]+6,
                reads=tail["reads"]+int(xs is not None)+int(ys is not None),
                writes=tail["writes"]+1, tests=tail["tests"]+2)


def mul_bits(xs, ys):
    if xs is None:
        return dict(bits=None, gates=0, reads=0, writes=0, tests=1)
    x, xt = xs
    child = mul_bits(xt, ys)
    shifted = (False, child["bits"])
    if x:
        summed = add_bits(ys, shifted)
        return dict(bits=summed["bits"], gates=child["gates"]+summed["gates"],
                    reads=child["reads"]+summed["reads"]+1,
                    writes=child["writes"]+summed["writes"]+1,
                    tests=child["tests"]+summed["tests"]+2)
    return dict(bits=shifted, gates=child["gates"], reads=child["reads"]+1,
                writes=child["writes"]+1, tests=child["tests"]+2)


def check_add(xs, ys, carry, report):
    m, n = bit_length(xs), bit_length(ys)
    width, output = max(m, n), bit_length(report["bits"])
    assert decode_bits(report["bits"]) == decode_bits(xs)+decode_bits(ys)+int(carry)
    assert report["gates"] == 6*width
    assert report["reads"] == m+n
    assert report["writes"] == output <= width+1
    assert report["tests"] == 2*width+3
    assert bit_cost(report) <= 11*width+4


def check_mul(xs, ys, report):
    m, n = bit_length(xs), bit_length(ys)
    assert decode_bits(report["bits"]) == decode_bits(xs)*decode_bits(ys)
    assert bit_length(report["bits"]) <= 2*m+n
    assert bit_cost(report) <= 12*m*(m+n+2)+1
    assert bit_cost(report) <= 24*(max(m, n)+1)**2+1


def validate_primitives():
    additions = products = 0
    for x in (False, True):
        for y in (False, True):
            for carry in (False, True):
                digit, next_carry = full_adder(x, y, carry)
                assert int(digit)+2*int(next_carry) == int(x)+int(y)+int(carry)
    for a in range(65):
        for b in range(65):
            for px, py in ((0, 0), (2, 3)):
                xs, ys = encode_bits(a, px), encode_bits(b, py)
                for carry in (False, True):
                    check_add(xs, ys, carry, add_bits(xs, ys, carry))
                    additions += 1
                check_mul(xs, ys, mul_bits(xs, ys))
                products += 1
    for width in (16, 32, 64, 128, 256, 512, 1024, 2048, 4096):
        a, b = (1 << width)-1, 1
        xs, ys = encode_bits(a), encode_bits(b)
        for carry in (False, True):
            check_add(xs, ys, carry, add_bits(xs, ys, carry))
            additions += 1
    for width in (16, 32, 64, 128, 256):
        for a, b in (((1 << width)-1, (1 << width)-1),
                     ((1 << width)+1, (1 << (width//2))+3)):
            xs, ys = encode_bits(a), encode_bits(b)
            check_mul(xs, ys, mul_bits(xs, ys))
            products += 1
    return dict(full_adder_cases=8, addition_cases=additions,
                multiplication_cases=products, largest_addition_input_bits=4096,
                largest_multiplication_input_bits=257, padded_inputs_checked=True)


def public_packet(n):
    scope = CONSTRUCTION["build_source"].__globals__
    prior_power, prior_walk = scope["counted_power"], scope["counted_walk"]
    events = []

    def binary_product(a, b):
        xs, ys = encode_bits(a), encode_bits(b)
        product = mul_bits(xs, ys)
        result = decode_bits(product["bits"])
        m, k, out = a.bit_length(), b.bit_length(), bit_length(product["bits"])
        events.append(dict(a=a, b=b, value=result, left_bits=m, right_bits=k,
                           output_bits=out, gates=product["gates"], reads=product["reads"],
                           writes=product["writes"], tests=product["tests"], clock=bit_cost(product),
                           encode_bit_cells=m+k, decode_digit_visits=out))
        return result

    def counted_power(modulus, a, exponent):
        if exponent == 0:
            return dict(value=1 % modulus, multiplications=0, halvings=0, reductions=1, max_product_bits=0)
        child = counted_power(modulus, a, exponent//2)
        square = binary_product(child["value"], child["value"])
        value = square % modulus
        extra, reductions = 1, 1
        max_bits = max(child["max_product_bits"], square.bit_length())
        if exponent % 2:
            product = binary_product(value, a % modulus)
            max_bits = max(max_bits, product.bit_length())
            value = product % modulus
            extra, reductions = 2, 3
        return dict(value=value, multiplications=child["multiplications"]+extra,
                    halvings=child["halvings"]+1, reductions=child["reductions"]+reductions,
                    max_product_bits=max_bits)

    def counted_walk(modulus, start, step, length, index=0):
        records, multiplications, reductions, max_bits = [], 0, 0, 0
        for offset in range(length):
            current = start % modulus
            reductions += 1
            records.append((current, index+offset))
            if offset+1 < length:
                product = binary_product(current, step)
                max_bits = max(max_bits, product.bit_length())
                start = product % modulus
                multiplications += 1
                reductions += 1
        return dict(records=records, multiplications=multiplications, reductions=reductions,
                    max_product_bits=max_bits)

    scope["counted_power"], scope["counted_walk"] = counted_power, counted_walk
    try:
        actual = SQRT["public_packet"](n)
    finally:
        scope["counted_power"], scope["counted_walk"] = prior_power, prior_walk
    # Keep the prior pipeline's timer: it includes the new data path and its
    # reports, and stops before all independent native reference validation.
    window = actual["parent"]["source"]
    if window is None:
        assert not events
        return actual
    width = window["N"].bit_length()
    for event in events:
        assert event["value"] == event["a"]*event["b"]
        assert event["left_bits"] <= width and event["right_bits"] <= width
        assert event["output_bits"] <= 2*event["left_bits"]+event["right_bits"] <= 3*width
        assert event["clock"] <= 12*event["left_bits"]*(event["left_bits"]+event["right_bits"]+2)+1
        assert event["clock"] <= 24*(width+1)**2+1
    assert len(events) == window["construction"]["arithmetic"]["multiplications"]
    aggregate = {key: sum(event[key] for event in events) for key in
                 ("gates", "reads", "writes", "tests", "clock", "encode_bit_cells", "decode_digit_visits")}
    assert aggregate["clock"] == sum(aggregate[key] for key in ("gates", "reads", "writes", "tests"))
    aggregate.update(scalar_products=len(events), input_bits=width,
                     largest_operand_bits=max(max(event["left_bits"], event["right_bits"]) for event in events),
                     largest_output_bits=max(event["output_bits"] for event in events),
                     primitive_clock_bound=len(events)*(24*(width+1)**2+1),
                     operand_result_sha256=hashlib.sha256(json.dumps(
                         [(event["a"], event["b"], event["value"]) for event in events]).encode()).hexdigest(),
                     boolean_product_oracles=0, native_remainder_calls=window["construction"]["arithmetic"]["reductions"],
                     legacy_integer_interface=True, is_complete_bit_certificate=False)
    assert aggregate["clock"] <= aggregate["primitive_clock_bound"]
    window["construction"]["bit_arithmetic"] = aggregate
    return actual


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeBitArithmetic.lean",
                  "scripts/CheckSemiprimeBitArithmetic.lean", "scripts/probe_semiprime_bit_arithmetic.py"))
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
                    assert window["construction"][key] == value, key
                binary_rows.append(dict(original_N=p*q, leaf_N=window["N"], leaf_width=window["width"],
                                        **window["construction"]["bit_arithmetic"]))
            actual.update(reference_p=p, reference_q=q)
            if "regime" in previous:
                actual["regime"] = previous["regime"]
            population.append(actual)
        populations[name] = population
    assert len(binary_rows) == 5
    result = dict(replay_id=REPLAY_ID, scope="Boolean primitive backend and raw residue-product substitution",
                  one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False,
                  is_bit_complexity_certificate=False, source_sha256=sources,
                  primitive_cost_model="Boolean gates, persistent bit-cell reads/writes, and list/Boolean branch tests. Report clocks are mathematical instrumentation. The Lean data path uses Boolean lists and does not call integer multiplication or its value specification.",
                  validation=dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
                                  status_counts=dict(counts), outcomes_preserved=True,
                                  constructed_sources=len(binary_rows), **primitives),
                  binary_rows=binary_rows,
                  summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
                  timing_protocol="Scoped replacement only of the two raw powering/walk functions inside the frozen counted builder. Every residue product uses the linked-Boolean-list multiplier. The prior root/decoder adapter times the complete preceding N-only route, new scalar data path and reports, native interface conversion/reductions, residue continuation and transport. Native product references, primitive references, factors, periods, offsets, ledger hashes and source comparisons are checked after that timer stops.",
                  limitations="Lean proves the Boolean arithmetic values, charged primitive clocks and intermediate widths, including batch composition. This model is not a machine-level execution certificate. The replay retains a native integer conversion/remainder interface, while inverse, decoder and preceding arithmetic retain their existing separate backend obligations. No full source bit-cost theorem, universal collision coverage, new exponent, unbiased corpus or software speed comparison is established. The previous 61-bit negative survives.",
                  **populations)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(validation=result["validation"], source_pins=len(sources), binary_rows=binary_rows,
                          surviving_negative=populations["negative_controls"][0]["N"],
                          one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()
