#!/usr/bin/env python3
"""Count the actual binary powers and recurrences in the public window.

The whole prior N-only pipeline is timed with one scoped builder replacement.
Every existing window, residue and transport outcome is preserved. Inverse
acquisition, square roots, sorting, polynomial work and full bit costs remain
separate charges. This is neither new universal coverage nor a bit certificate.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-totient-residues-audit.json"
PARENT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_totient_residues.py"))
WINDOW = PARENT["WINDOW"]
REPLAY_ID = 202610031601


def counted_power(n,a,e):
    if e == 0:
        return dict(value=1 % n,multiplications=0,halvings=0,reductions=1,max_product_bits=0)
    child = counted_power(n,a,e//2)
    square = child["value"]*child["value"]
    assert square < n*n
    value = square % n
    extra,reductions = 1,1
    max_bits = max(child["max_product_bits"],square.bit_length())
    if e % 2:
        product = value*(a % n)
        assert product < n*n
        max_bits = max(max_bits,product.bit_length())
        value = product % n
        extra,reductions = 2,3
    result = dict(value=value,multiplications=child["multiplications"]+extra,
                  halvings=child["halvings"]+1,reductions=child["reductions"]+reductions,
                  max_product_bits=max_bits)
    assert result["multiplications"] <= 2*e.bit_length()
    assert result["reductions"] <= 3*e.bit_length()+1
    assert result["halvings"] == e.bit_length()
    return result


def counted_walk(n,start,step,length,index=0):
    records,multiplications,reductions,max_bits = [],0,0,0
    for offset in range(length):
        current = start % n
        reductions += 1
        records.append((current,index+offset))
        if offset+1 < length:
            product = current*step
            assert product < n*n
            max_bits = max(max_bits,product.bit_length())
            start = product % n
            multiplications += 1
            reductions += 1
    assert multiplications == max(length-1,0)
    assert reductions == length+max(length-1,0)
    return dict(records=records,multiplications=multiplications,reductions=reductions,
                max_product_bits=max_bits)


def build_source(n,alpha,width):
    block = 2*width
    centre = max(n+1-2*math.isqrt(n),0)//4
    inverse = pow(alpha,-1,n)
    target = counted_power(n,alpha,centre)
    step = counted_power(n,inverse,block)
    babies = counted_walk(n,1,alpha,block)
    giants = counted_walk(n,target["value"],step["value"],block)
    arithmetic = dict(multiplications=target["multiplications"]+step["multiplications"]+
                                      babies["multiplications"]+giants["multiplications"],
                      reductions=target["reductions"]+step["reductions"]+
                                 babies["reductions"]+giants["reductions"],
                      halvings=target["halvings"]+step["halvings"],
                      parity_tests=target["halvings"]+step["halvings"],
                      max_product_bits=max(x["max_product_bits"] for x in (target,step,babies,giants)),
                      input_bits=n.bit_length(),inverse_queries=1,centre_square_roots=1)
    assert arithmetic["multiplications"] <= 4*width+4*n.bit_length()+2
    assert arithmetic["reductions"] <= 8*width+6*n.bit_length()+5
    assert arithmetic["halvings"] <= 2*n.bit_length()+1
    assert arithmetic["max_product_bits"] <= 2*n.bit_length()
    metrics = dict(centre_square_roots=1,modular_powers=2,modular_inverses=1,
                   modular_multiplications=babies["multiplications"]+giants["multiplications"],
                   baby_records=block,giant_records=block,sort_comparisons=0,merge_comparisons=0,
                   candidate_square_roots=0,candidate_gcds=0,projection_regeneration_powers=0,
                   explicit_grid_candidates=0)
    ordered_babies = WINDOW["SORTER"](babies["records"],metrics)
    ordered_giants = WINDOW["SORTER"](giants["records"],metrics)
    collision,i,j = None,0,0
    while i < block and j < block:
        metrics["merge_comparisons"] += 1
        if ordered_babies[i][0] == ordered_giants[j][0]:
            collision = dict(baby_index=ordered_babies[i][1],giant_index=ordered_giants[j][1],
                             value=ordered_babies[i][0],offset=block*ordered_giants[j][1]+ordered_babies[i][1])
            break
        if ordered_babies[i][0] < ordered_giants[j][0]:
            i += 1
        else:
            j += 1
    factor,candidate = None,None
    if collision is not None:
        modulus = max(centre-collision["offset"],0)
        signal = (n+1) % modulus if modulus else n+1
        discriminant = max(signal*signal-4*n,0)
        smaller = max(signal-math.isqrt(discriminant),0)//2
        divisor = math.gcd(n,smaller)
        metrics["candidate_square_roots"] += 1
        metrics["candidate_gcds"] += 1
        candidate = dict(modulus=modulus,sum_signal=signal,discriminant=discriminant,
                         smaller_candidate=smaller,gcd=divisor)
        if 1 < divisor < n:
            factor = divisor
    assert metrics["merge_comparisons"] <= 2*block
    assert metrics["sort_comparisons"] <= 2*block*(block-1).bit_length()
    return dict(N=n,width=width,block=block,active_base=alpha,centre=centre,target=target["value"],
                inverse_step=step["value"],babies=ordered_babies,giants=ordered_giants,
                collision=collision,candidate=candidate,factor=factor,metrics=metrics,
                construction=dict(arithmetic=arithmetic,target_power=target,step_power=step,
                                  baby_walk={k:v for k,v in babies.items() if k != "records"},
                                  giant_walk={k:v for k,v in giants.items() if k != "records"}))


def public_packet(n):
    scope = WINDOW["public_packet"].__globals__
    original = scope["build_source"]
    start = time.perf_counter()
    scope["build_source"] = build_source
    try:
        actual = PARENT["public_packet"](n)
    finally:
        scope["build_source"] = original
    actual["elapsed_ms"] = 1000*(time.perf_counter()-start)
    window = actual["parent"]["source"]
    if window is not None:
        counts = window["construction"]["arithmetic"]
        assert counts["multiplications"] <= 4*actual["width"]+4*n.bit_length()+2
        assert counts["reductions"] <= 8*actual["width"]+6*n.bit_length()+5
        assert counts["halvings"] <= 2*n.bit_length()+1
    return actual


def validate_primitives():
    powers,walks = 0,0
    for n in (1,2,3,4,5,8,9,35,49,143):
        for a in range(2*n+1):
            for e in (0,1,2,3,4,7,8,15,16,63,64,127,128):
                actual = counted_power(n,a,e)
                assert actual["value"] == pow(a,e,n)
                assert actual["halvings"] == e.bit_length()
                assert actual["reductions"] <= 3*e.bit_length()+1
                assert actual["multiplications"] <= 2*e.bit_length()
                assert actual["max_product_bits"] <= 2*n.bit_length()
                powers += 1
        for start in range(n):
            for length in (0,1,2,3,8,17):
                step = (3*start+1) % n
                actual = counted_walk(n,start,step,length,7)
                assert actual["records"] == [(start*pow(step,i,n) % n,7+i) for i in range(length)]
                walks += 1
    return dict(binary_power_cases=powers,geometric_walk_cases=walks)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeWindowConstruction.lean",
                  "scripts/CheckSemiprimeWindowConstruction.lean",
                  "scripts/probe_semiprime_window_construction.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    primitives = validate_primitives()
    prior = json.loads((ROOT/PARENT_AUDIT).read_text())
    counts,squares = Counter(),0
    primes = list(primerange(2,200))
    for i,p in enumerate(primes):
        for q in primes[i:]:
            actual = public_packet(p*q)
            PARENT["check_packet"](actual,p,q)
            counts[actual["status"]] += 1
            squares += int(p == q)
    populations,construction_rows = {},[]
    for name in ("inputs","controls","positive_controls","negative_controls","wrapped_controls"):
        population = []
        for previous in prior[name]:
            p,q = previous["reference_p"],previous["reference_q"]
            actual = public_packet(p*q)
            PARENT["check_packet"](actual,p,q)
            assert (actual["factor"],actual["status"]) == (previous["factor"],previous["status"])
            window,old_window = actual["parent"]["source"],previous["parent"]["source"]
            if window is not None:
                for key in ("active_base","centre","target","inverse_step","babies","giants","collision","candidate","factor"):
                    assert json.dumps(window[key]) == json.dumps(old_window[key]),key
                construction_rows.append(dict(original_N=p*q,leaf_N=window["N"],
                                              leaf_width=window["width"],
                                              **window["construction"]["arithmetic"]))
            actual.update(reference_p=p,reference_q=q)
            if "regime" in previous:
                actual["regime"] = previous["regime"]
            population.append(actual)
        populations[name] = population
    assert len(construction_rows) == 5
    result = dict(replay_id=REPLAY_ID,scope="N-only pipeline with counted executable quarter-window construction",
                  one_sixth_guarantee="OPEN",is_complete_semiprime_factorizer=False,
                  is_bit_complexity_certificate=False,source_sha256=sources,
                  validation=dict(semiprime_cases=sum(counts.values()),prime_squares=squares,
                                  status_counts=dict(counts),outcomes_preserved=True,
                                  constructed_sources=len(construction_rows),**primitives),
                  construction_rows=construction_rows,
                  summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
                  timing_protocol="A scoped replacement of the preceding window builder uses the exact counted binary-power and geometric-walk code, restored before returning. The entire preceding route, new builder, retained residue continuation and all transport are timed. Counts include modular normalizations, products, squarings, residue reductions, exponent halvings and parity tests. One actual modular inverse, the centre square root, sorting, lookup, optional decoder and polynomial backend retain their separate existing charges. Independent primitive references, factors, local periods, offsets and source equality validation are outside timing.",
                  limitations="This certifies arithmetic call counts and bounded operands for a source with the same recovery information. It does not certify implemented bit complexity of inverse acquisition, square roots, sorting, all arithmetic primitives, the polynomial backend or preceding descent. No universal offset cover, new factorization exponent, random corpus or tuned baseline comparison is established. The prior 61-bit negative still survives.",
                  **populations)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(validation=result["validation"],source_pins=len(sources),
                          summary=result["summary"],construction_rows=construction_rows,
                          surviving_negative=populations["negative_controls"][0]["N"],
                          one_sixth_guarantee="OPEN"),indent=2))


if __name__ == "__main__":
    main()
