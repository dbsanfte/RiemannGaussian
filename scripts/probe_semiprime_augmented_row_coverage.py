#!/usr/bin/env python3
"""Reference-only coverage of the original and weighted channel union.

Private actual orders classify complete public packet streams. This is
neither an N-only factorizer run nor a Lean order/failure certificate.
All parent sources remain frozen; misses require a new coverage mechanism.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import groupby
import json
import math
from pathlib import Path
import random
import runpy

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-weighted-rows-audit.json"
REPLAY_ID = 202610033206
WEIGHTED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_weighted_rows.py"))
COVERAGE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_combined_row_coverage.py"))


def augmented_exponents(n,m,counts):
    for j,group in groupby(WEIGHTED["DERIVATIVE"]["reference_packets"](n,m),key=lambda w:w["j"]):
        original = list(group)
        for w in original:
            counts["original_packets"] += 1
            yield w["exponent"]
        for w in WEIGHTED["weighted_packets"](original,m):
            counts["weighted_packets"] += 1
            yield w["exponent"]
        counts["public_unit_residues"] += 1
        if m > 10000 and j%5000 == 0:
            print(json.dumps(dict(progress="reference-only-augmented-packets",N=n,j=j,
                modulus=m,counts=dict(counts))),flush=True)


def reference_case(p,q):
    from sympy import n_order
    n,counts,metrics = p*q,Counter(),Counter()
    m = WEIGHTED["FAMILY"]["first_public_prime"](n,WEIGHTED["IntegerLedger"](),metrics)
    if math.gcd(n,m) != 1:
        return dict(N=n,classification="public-modulus-factor",modulus=m)
    dP,dQ = int(n_order(2,p)),int(n_order(2,q))
    classified = COVERAGE["classify_exponents"](augmented_exponents(n,m,counts),dP,dQ)
    assert counts["weighted_packets"] <= 2*counts["original_packets"]
    return dict(N=n,input_bits=n.bit_length(),reference_p=p,reference_q=q,
        reference_actual_orders=[dP,dQ],modulus=m,packet_counts=dict(counts),
        classification="no-augmented-hit" if classified["combined_and_sign_prefix_exhausted"]
            else "augmented-or-endpoint-hit",is_N_only_source=False,
        is_factorization_runtime_measurement=False,orders_kernel_checked=False,**classified)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"scripts/probe_semiprime_augmented_row_coverage.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import nextprime,isprime,n_order
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--bits",type=int,default=90)
    parser.add_argument("--maximum-cases",type=int,default=8)
    args = parser.parse_args()
    sources,rnd,cases,rejected = source_inventory(),random.Random(REPLAY_ID),[],0
    controls = [reference_case(23,89),reference_case(101,103)]
    assert controls[0]["classification"] == "no-augmented-hit"
    assert controls[1]["classification"] == "augmented-or-endpoint-hit"
    checks = 0
    for _ in range(512):
        dP,dQ = rnd.randrange(1,101),rnd.randrange(1,101)
        original = [rnd.randrange(-1000,1001) for _ in range(rnd.randrange(16))]
        weighted = [rnd.randrange(-1000,1001) for _ in range(rnd.randrange(16))]
        result = COVERAGE["classify_exponents"](original+weighted,dP,dQ)
        assert result["combined_signed_hit"] == COVERAGE["explicit_signed_reference"](original+weighted,dP,dQ)
        checks += 1
    for i in range(args.maximum_cases):
        while True:
            p = int(nextprime(rnd.randrange(2**(args.bits//2-1),2**(args.bits//2))))
            if int(n_order(2,p)) == p-1:
                break
            rejected += 1
        while True:
            q = int(nextprime(rnd.randrange(11*p//10,19*p//10)))
            if int(n_order(2,q)) == q-1:
                break
            rejected += 1
        assert isprime(p) and isprime(q) and p<=q<=2*p
        case = reference_case(p,q)
        cases.append(case)
        print(json.dumps(dict(progress="reference-only-augmented-coverage",sample_index=i,**case)),flush=True)
        if case["classification"] == "no-augmented-hit":
            break
    assert source_inventory() == sources,"source changed during replay"
    report = dict(replay_id=REPLAY_ID,source_sha256=sources,nominal_bits=args.bits,
        maximum_reference_cases=args.maximum_cases,rejected_reference_prime_candidates=rejected,
        reference_condition="Base two has full component order on the new balanced corpus",
        scope="Original and adjacent four-center weighted roots, both signed pair channels and raw endpoints",
        signed_union_oracle_checks=checks,small_reference_controls=controls,cases=cases,
        found_long_order_augmented_reference_miss=any(c["classification"]=="no-augmented-hit" for c in cases),
        is_N_only_source=False,is_factorization_runtime_measurement=False,
        kernel_checked_failure_control=False,is_bit_complexity_certificate=False,
        one_sixth_guarantee="OPEN",
        limitations="This exact private-order classifier streams every original packet and all four adjacent center combinations, retaining global inverse classes and both local signed projections. It covers cross-family pairs as well as pairs inside either family. The component orders and primality of larger cases are native reference data, not Lean certificates; no public polynomial source is run or timed. The small matched-order control and any full-order miss concern only this fixed public base/modulus/family and these pair/endpoint observables. They are not asymptotic lower bounds and do not rule out period certificates, other bases, moduli, higher correlations or other algorithms. A full every-run construction-inclusive deterministic sixth-root bit theorem remains open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),reference_cases=len(cases),
        found_long_order_augmented_reference_miss=report["found_long_order_augmented_reference_miss"],
        one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()
