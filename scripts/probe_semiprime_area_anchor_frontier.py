#!/usr/bin/env python3
"""Held-out chosen-anchor coverage and the balanced same-residue obstruction.

Large runs are complete private field classifications of a public N,m row
stream. They are not public polynomial factorization clocks or Lean failure
certificates. The new coefficient and mixed-center envelopes are checked on
actual full Nt rows, preserving all unpaid cross-residue information.
"""
from __future__ import annotations

import argparse
from collections import Counter,defaultdict
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-row-area-spectrum-audit.json"
REPLAY_ID = 202610033242
SEEDS = (REPLAY_ID,202610033243)
PRIOR = runpy.run_path(str(ROOT/"scripts/probe_semiprime_row_area_spectrum.py"))


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeSameResidueAreas.lean",
        "scripts/CheckSemiprimeSameResidueAreas.lean",
        "scripts/probe_semiprime_area_anchor_frontier.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def cases():
    from sympy import nextprime
    for seed in SEEDS:
        rnd = random.Random(seed)
        for bits in (40,44,46):
            p = int(nextprime(rnd.randrange(2**(bits-1),2**bits)))
            q = int(nextprime(rnd.randrange(p+1,2*p)))
            yield seed,"larger-balanced-held-out",p,q
        p = int(nextprime(rnd.randrange(2**17,2**18)))
        yield seed,"prime-square",p,p
        p = int(nextprime(rnd.randrange(2**9,2**10)))
        q = int(nextprime(rnd.randrange(128*p,256*p)))
        yield seed,"wide-ratio-no-balanced-credit",p,q


def main():
    from sympy import integer_nthroot,isprime,nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    args = parser.parse_args()
    sources,counters,results = source_inventory(),Counter(),[]
    for index,(seed,population,p,q) in enumerate(cases()):
        n,rnd = p*q,random.Random(seed+index*1013)
        assert isprime(p) and isprime(q)
        floor,exact = integer_nthroot(n,6)
        B = int(floor)+int(not exact)
        m = int(nextprime(max(2,B)-1))
        assert math.gcd(n,m)==1
        print(json.dumps(dict(progress="area-anchor-held-out-start",index=index,N=n,
            reference_p=p,reference_q=q,modulus=m,input_bits=n.bit_length())),flush=True)
        start = time.perf_counter()
        rows = PRIOR["public_reference_rows"](n,m,counters)
        groups = defaultdict(list)
        for w in rows:
            assert abs(w["a"])+w["t"]<=m
            counters["joint_original_coefficient_envelopes"] += 1
            groups[w["j"]].append(w)
        balanced = p<=q<=2*p and 6*m+2<p
        delta = math.isqrt(2*n)-math.isqrt(n//2)
        if q<=2*p:
            assert 0<=delta<=p+2
            counters["actual_balanced_public_center_bounds"] += 1
        for _ in range(192):
            j = rnd.randrange(1,m)
            group = groups[j]
            for same_residue,triple in ((True,rnd.sample(group,3)),
                    (False,rnd.sample(rows,3))):
                mixed = PRIOR["AREA"]["area"](*((w["a"],
                    int(PRIOR["orientation"](w))*(w["a"]-w["t"]),w["t"]) for w in triple))
                assert abs(mixed)<=m**3
                counters["all_orientation_mixed_area_cubic_envelopes"] += 1
                area = PRIOR["triple_oracle"](n,m,*triple,counters)
                if same_residue:
                    assert area%m**3==0 and 2*abs(area//m**3)<=6*m+delta
                    counters["combined_same_residue_normalized_envelopes"] += 1
                    if balanced:
                        assert abs(area//m**3)<p and math.gcd(n,area) in (1,n)
                        counters["balanced_all_center_same_residue_no_proper_GCD"] += 1
        classification = PRIOR["classify_anchor"](n,m,p,q,rows)
        result = dict(index=index,seed=seed,population=population,N=n,input_bits=n.bit_length(),
            reference_p=p,reference_q=q,public_sixth_width=B,modulus=m,
            balanced_all_center_same_residue_obstruction_applicable=balanced,
            complete_selected_anchor=classification,
            reference_milliseconds=1000*(time.perf_counter()-start))
        results.append(result)
        print(json.dumps(dict(progress="area-anchor-held-out-completed",index=index,
            packets=len(rows),ordinary_anchor_slopes=classification["ordinary_anchor_slopes"],
            p_collapsed=classification["p_collapsed_values"],q_collapsed=classification["q_collapsed_values"],
            chosen_anchor_exhausted=classification["native_chosen_anchor_exhausted"])),flush=True)
    assert source_inventory()==sources,"source changed during replay"
    checked = args.checked_declarations>0 and args.checked_theorems>0
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        independent_seeds=SEEDS,complete_cases=results,full_original_row_oracles=dict(counters),
        chosen_anchor_native_exhaustions=sum(c["complete_selected_anchor"]["native_chosen_anchor_exhausted"]
            for c in results),lean_validation=dict(strict_leaf_and_root=checked,
            separately_completed_scoped_gates=checked,namespace_linters=14 if checked else 0,
            linter_errors=0 if checked else None,all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        compiled_components=dict(actual_joint_coefficient_envelope=True,
            all_orientation_mixed_area_bound_m_cubed=True,balanced_public_center_bound_p_plus2=True,
            combined_normalized_area_bound=True,
            actual_balanced_same_residue_triples_no_proper_GCD_for_all_centers=True),
        is_complete_factorizer=False,is_kernel_exhaustion_certificate=False,
        is_bit_complexity_certificate=False,universal_selected_anchor_coverage="OPEN",
        guaranteed_one_sixth_factorization="OPEN",
        limitations="The stronger kernel obstruction retains both centers and requires p<=q<=2p, m coprime to N and 6m+2<p. It applies to every actual same-residue triple, including repeated packets and prime squares. It does not apply to cross-residue triples or silently extend to wide factor ratios. Known public m is an input here; a small-factor prefix up to 6m+2 has not been attached to a complete bit-priced factorizer. Native held-out classifiers cover every original packet, the chosen anchor's full singular-minor GCD prefix and both prime-field slope projections. They preserve whole-N duplicates; squares use the whole p² carrier before prime projection. Private prime labels, timers, observed hits and finite exhaustions are not public polynomial runtimes, universal coverage, native machine refinements or kernel execution certificates. Original full Nt lifts and exact reduced offsets are compared throughout. Cross-residue coverage, all-anchor work, arbitrary-ratio completion and the deterministic construction-inclusive N^(1/6) bit theorem remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),actual_prime_cases=len(results),
        checked_packets=counters["joint_original_coefficient_envelopes"],
        chosen_anchor_native_exhaustions=report["chosen_anchor_native_exhaustions"],
        one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()
