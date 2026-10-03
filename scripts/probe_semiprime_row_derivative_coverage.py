#!/usr/bin/env python3
"""Reference search for a fixed positive-row derivative coverage control.

Reference factors and orders select a stress input, never an algorithm
parameter. The selected N is then replayed through the unchanged N-only
source, including all modular powers and polynomial arithmetic. This is
an exact native diagnostic, not a kernel-checked counterexample, a general
factoring lower bound or a complete bit-cost certificate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import random
import runpy

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-row-derivative-audit.json"
REPLAY_ID = 202610033102
DERIVATIVE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_row_derivative.py"))


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"scripts/probe_semiprime_row_derivative_coverage.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import nextprime, n_order, isprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--bits",type=int,default=72)
    parser.add_argument("--maximum-cases",type=int,default=32)
    args = parser.parse_args()
    sources,rnd,cases = source_inventory(),random.Random(REPLAY_ID),[]
    rejected,control,signed_reference = 0,None,None
    for i in range(args.maximum_cases):
        # Private reference conditioning is explicit. The source sees only N.
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
        audit=DERIVATIVE["reference_aliases"](p,q)
        cases.append(audit)
        print(json.dumps(dict(progress="reference-conditioned-positive-row-coverage",
            sample_index=i,**audit)),flush=True)
        if audit["reference_classification"]=="no-local-row-alias":
            signed_reference=DERIVATIVE["reference_aliases"](p,q,signed=True)
            print(json.dumps(dict(progress="reference-only-inverse-axis-comparison",
                **signed_reference)),flush=True)
            control=DERIVATIVE["row_derivative_source"](p*q)
            assert control["factor"] is None and control["stage"]=="exhausted-row-derivatives"
            assert control["distinct_public_roots"]==audit["distinct_whole_modulus_buckets"]
            assert control["evaluated_derivatives"]==control["distinct_public_roots"]
            assert control["metrics"]["derivative_gcd_queries"]==control["distinct_public_roots"]
            assert control["metrics"].get("selected_row_scans",0)==0
            print(json.dumps(dict(progress="complete-N-only-exhausted-row-derivatives",
                **control)),flush=True)
            break
    assert source_inventory()==sources,"source changed during replay"
    report=dict(replay_id=REPLAY_ID,source_sha256=sources,
        scope="Reference-conditioned fixed positive-row coverage stress test",
        nominal_bits=args.bits,maximum_reference_cases=args.maximum_cases,
        rejected_reference_prime_candidates=rejected,
        reference_condition="2 has full p-1 and q-1 order; references only",
        reference_cases=cases,exhausted_N_only_control=control,
        separate_inverse_axis_reference=signed_reference,
        full_public_source_replayed=control is not None,
        private_factors_used_as_source_inputs=False,kernel_checked_failure_control=False,
        is_bit_complexity_certificate=False,one_sixth_guarantee="OPEN",
        limitations="The unchanged source accepts N and public base 2 only; private factors/orders condition the reference stress corpus and verify outputs after its timer. A complete native exhausted source establishes no factor was found by this fixed positive-power, both-center intermediate-row derivative detector on that N. All of its powers, global deduplication, monic product, coefficient derivative, reused-tree evaluation and GCD scans are inside the timer. The native arithmetic implementation is not formally refined, and no literal Lean failure control or complete bit certificate follows from the reference order calculation. An inverse row axis is classified separately and may have additional hits. Different bases, moduli, families or correlated observables are not excluded. The parent module proves exact derivative compression, complete proper-pair recovery and recovery on the earlier short baby-window failure, not universal local-row coverage. All parent pins remain frozen; the arbitrary-ratio every-run N-only one-sixth bit theorem remains open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),reference_cases=len(cases),
        exhausted_N_only_control=control is not None,
        one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()
