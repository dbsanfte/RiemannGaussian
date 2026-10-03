#!/usr/bin/env python3
"""Reference-only coverage of BOTH ordinary and reciprocal row channels.

Private actual orders classify the complete N-only packet family. This
is not an N-only source, a runtime sample or a Lean failure certificate.
The reference fold is checked against explicit signed-value grouping on
small controls. Full public source replay is a separate later action.
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

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-reciprocal-rows-audit.json"
REPLAY_ID = 202610033201
DERIVATIVE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_row_derivative.py"))


def classify_exponents(es, dP, dQ):
    """Global inverse orbits, folded local residues and sign endpoints."""
    period = math.lcm(dP,dQ)
    orbits,p_seen,q_seen = set(),{},{}
    counts = Counter()
    for e in es:
        counts["original_exponents"] += 1
        whole = e % period
        orbit = min(whole,(-whole) % period)
        if orbit in orbits:
            counts["duplicate_global_inverse_orbits"] += 1
            continue
        orbits.add(orbit)
        ep,eq = e % dP,e % dQ
        fp,fq = min(ep,(-ep) % dP),min(eq,(-eq) % dQ)
        counts["folded_p_aliases"] += fp in p_seen
        counts["folded_q_aliases"] += fq in q_seen
        p_seen[fp],q_seen[fq] = orbit,orbit
        global_self = 2*whole % period == 0
        counts["global_self_inverse_orbits"] += global_self
        counts["local_self_inverse_p_only"] += 2*ep % dP == 0 and not global_self
        counts["local_self_inverse_q_only"] += 2*eq % dQ == 0 and not global_self
        plusP,plusQ = ep==0,eq==0
        minusP,minusQ = dP % 2==0 and 2*ep==dP,dQ % 2==0 and 2*eq==dQ
        counts["proper_plus_one_signs"] += plusP != plusQ
        counts["proper_minus_one_signs"] += minusP != minusQ
    counts["distinct_global_inverse_orbits"] = len(orbits)
    counts["distinct_signed_whole_values"] = 2*len(orbits)-counts["global_self_inverse_orbits"]
    hit = any(counts[k] for k in ("folded_p_aliases","folded_q_aliases",
        "local_self_inverse_p_only","local_self_inverse_q_only"))
    endpoint = counts["proper_plus_one_signs"]+counts["proper_minus_one_signs"] > 0
    return dict(counts,combined_signed_hit=hit,additional_sign_prefix_hit=endpoint,
        combined_and_sign_prefix_exhausted=not hit and not endpoint)


def explicit_signed_reference(es, dP, dQ):
    period = math.lcm(dP,dQ)
    whole = {sign*e % period for e in es for sign in (1,-1)}
    return len({e % dP for e in whole}) < len(whole) or len({e % dQ for e in whole}) < len(whole)


def reference_case(p,q):
    from sympy import n_order
    n,integers,metrics = p*q,DERIVATIVE["IntegerLedger"](),Counter()
    m = DERIVATIVE["FAMILY"]["first_public_prime"](n,integers,metrics)
    if math.gcd(m,n)!=1:
        return dict(N=n,reference_p=p,reference_q=q,modulus=m,classification="modulus-factor")
    dP,dQ = int(n_order(2,p)),int(n_order(2,q))
    result = classify_exponents((w["exponent"] for w in DERIVATIVE["reference_packets"](n,m)),dP,dQ)
    return dict(N=n,input_bits=n.bit_length(),reference_p=p,reference_q=q,modulus=m,
        reference_actual_orders=[dP,dQ],classification="no-combined-alias" if
        result["combined_and_sign_prefix_exhausted"] else "combined-or-sign-alias",
        is_N_only_source=False,orders_kernel_checked=False,**result)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"scripts/probe_semiprime_combined_row_coverage.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import nextprime,isprime,n_order
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--bits",type=int,default=84)
    parser.add_argument("--maximum-cases",type=int,default=16)
    args = parser.parse_args()
    sources,rnd,cases = source_inventory(),random.Random(REPLAY_ID),[]
    checks = 0
    for _ in range(512):
        dP,dQ = rnd.randrange(1,101),rnd.randrange(1,101)
        es = [rnd.randrange(-1000,1001) for _ in range(rnd.randrange(20))]
        folded = classify_exponents(es,dP,dQ)
        assert folded["combined_signed_hit"]==explicit_signed_reference(es,dP,dQ)
        checks += 1
    controls = [reference_case(14799739,24991489),reference_case(39167077933,64308254573)]
    rejected = 0
    for i in range(args.maximum_cases):
        # Actual orders condition the reference corpus only, never a source.
        while True:
            p=int(nextprime(rnd.randrange(2**(args.bits//2-1),2**(args.bits//2))))
            if int(n_order(2,p))==p-1:
                break
            rejected+=1
        while True:
            q=int(nextprime(rnd.randrange(11*p//10,19*p//10)))
            if int(n_order(2,q))==q-1:
                break
            rejected+=1
        assert isprime(p) and isprime(q) and p<=q<=2*p
        case=reference_case(p,q)
        cases.append(case)
        print(json.dumps(dict(progress="reference-only-combined-row-coverage",
            sample_index=i,**case)),flush=True)
        if case["classification"]=="no-combined-alias":
            break
    assert source_inventory()==sources,"source changed during replay"
    report=dict(replay_id=REPLAY_ID,source_sha256=sources,nominal_bits=args.bits,
        maximum_reference_cases=args.maximum_cases,rejected_reference_prime_candidates=rejected,
        reference_condition="base 2 has full component order; reference conditioning only",
        scope="Complete signed-row and extra sign-endpoint coverage reference audit",
        fold_vs_explicit_signed_validation_cases=checks,previous_controls=controls,cases=cases,
        is_N_only_source=False,is_factorization_runtime_measurement=False,
        kernel_checked_failure_control=False,is_bit_complexity_certificate=False,
        one_sixth_guarantee="OPEN",
        limitations="Private actual orders classify the entire public original packet list into global inverse orbits. Injective folded local residues plus no local-only self-inverse values imply the complete signed root union has no non-global local alias, hence neither the ordinary nor reciprocal pair channel has a proper pair hit. Endpoint classifications also test the separate plus/minus-one prefix. The fold is independently validated against explicit signed residue grouping on 512 arbitrary finite lists and orders. Factors, primality and actual orders for new samples are native reference calculations, not Lean certificates. This script does not execute a public factorizer, construct polynomial signals or measure its runtime; source replay must occur separately. These diagnostics concern the fixed public base/modulus/family and do not exclude other cancellation observables or establish an asymptotic lower bound. The universal arbitrary-ratio every-run N-only one-sixth bit theorem remains open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),reference_cases=len(cases),
        found_complete_combined_reference_failure=any(c["classification"]=="no-combined-alias" for c in cases),
        one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()
