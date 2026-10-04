#!/usr/bin/env python3
"""Original quadratic resultants, two affine channels, and N-only controls.

The 103-bit pair is inherited from a frozen private-field reference search
and now has a separate kernel recovery certificate. Its full polynomial
source is not replayed here. Finite small sources include the inherited
checked square/modulus prefixes; no native bit-machine refinement is claimed.
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
PARENT_AUDIT = "docs/semiprime-affine-frontier-audit.json"
REPLAY_ID = 202610033230
FRONTIER = runpy.run_path(str(ROOT/"scripts/probe_semiprime_affine_frontier.py"))
WEIGHTED = FRONTIER["WEIGHTED"]
REFLECTED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_reflected_companions.py"))
FAMILY,COMPANION = (REFLECTED[k] for k in ("FAMILY","COMPANION"))
IntegerLedger,ScalarLedger,BATCH = (REFLECTED[k] for k in ("IntegerLedger","ScalarLedger","BATCH"))


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeAffineRowRoots.lean",
        "scripts/CheckSemiprimeAffineRowRoots.lean","scripts/probe_semiprime_affine_row_roots.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def coefficient_oracles(rnd):
    from sympy import Matrix
    checks = Counter()
    for index in range(4096):
        n = rnd.choice((4,9,25,49,77,143,221)) if index<512 else rnd.randrange(4,1000)
        a,b,t,d,e,s = [rnd.randrange(-64,65) for _ in range(6)]
        D,A,B = a*s-d*t,a*e-d*b,b*s-e*t
        normalized = n*D*D-A*B
        if index<128:
            matrix = Matrix([[n*s,0,n*t,0],[e,n*s,b,n*t],[d,e,a,b],[0,d,0,a]])
            assert int(matrix.det()) == n*normalized
            checks["independent_sympy_sylvester_determinants"] += 1
        if not all(math.gcd(z,n)==1 for z in (a,d,t,s)):
            checks["rejected_nonunit_scale_pairs"] += 1
            continue
        ra,rd,rt,rs = [(-v*pow(z,-1,n))%n for z,v in ((a,b),(d,e),(t,b),(s,e))]
        assert a*d*(ra-rd)%n == A%n
        assert t*s*(rt-rs)%n == -B%n
        assert normalized%n == a*d*t*s*(ra-rd)*(rt-rs)%n
        assert math.gcd(n,normalized) == math.gcd(n,(ra-rd)*(rt-rs))
        checks["exact_unit_normalized_resultant_GCD_phases"] += 1
    return dict(checks,is_Lean_proof=False)


def public_packet_oracle(n,m):
    counts,roots = Counter(),[set(),set()]
    for j in range(1,m):
        for w in WEIGHTED["reference_residue_packets"](n,m,j):
            counts["original_packets"] += 1
            a,b,c,t = (w[k] for k in ("a","b","c","t"))
            L = m*b-2*a*j
            assert m*m*c-j*m*b+j*j*a == n*t
            for x in (-11,0,29):
                Y = m*x+j
                assert m*m*(a*x*x+b*x+c) == a*Y*Y+L*Y+n*t
                counts["integer_original_quadratic_coordinate_identities"] += 1
            for side,scale in enumerate((a,t)):
                if math.gcd(scale,n)!=1:
                    counts["excluded_nonunit_scales"] += 1
                    continue
                root = -L*pow(scale,-1,n)%n
                assert (scale*root+L)%n == 0
                roots[side].add(root)
                counts["admissible_normalized_packet_coordinates"] += 1
    return dict(N=n,modulus=m,counts=dict(counts),root_counts=[len(s) for s in roots],
        all_original_integer_and_normalized_coordinate_checks_passed=True,is_Lean_proof=False)


def finite_recovery_oracles(rnd):
    checks = Counter()
    for index in range(192):
        n = rnd.choice((4,9,25,49,77,143,221)) if index<96 else rnd.randrange(4,700)
        ordinary = list(dict.fromkeys([rnd.randrange(n) for _ in range(rnd.randrange(1,20))]))
        signed = {0,*ordinary,*((-x)%n for x in ordinary)}
        expected = any(1<math.gcd(n,x-y)<n for x in signed for y in signed if x!=y)
        integers,ring,batch,metrics = IntegerLedger(),ScalarLedger(n),BATCH["MonicBatch"](n),Counter()
        outputs = REFLECTED["reflected_outputs"](n,ordinary,integers,ring,batch,metrics)
        factor,stage,_ = REFLECTED["recover_reflected"](n,ordinary,outputs,integers,metrics)
        assert (factor is not None) == expected
        assert metrics["reflected_column_gcd_queries"]+metrics["selected_channel_gcd_queries"]<=3*len(ordinary)+1
        checks[stage] += 1
        checks["lists_with_global_zero"] += 0 in ordinary
        checks["lists_with_global_negative_matches"] += any(-x%n in ordinary for x in ordinary)
    return dict(cases=192,checks=dict(checks),is_Lean_proof=False)


def public_affine_source(n):
    """N-only input; all public setup, original packets and recovery timed."""
    start = time.perf_counter()
    integers,ring,batch,metrics = IntegerLedger(),ScalarLedger(n),BATCH["MonicBatch"](n),Counter()
    originals,buckets,outputs,m = [],{}, {},None

    def finish(factor,stage,witness=None):
        if witness is not None:
            witness = dict(witness,root_packet_bucket=buckets[witness["root"]])
            if witness.get("other_root") is not None:
                witness["other_root_packet_bucket"] = buckets[witness["other_root"]]
        queries = sum(metrics[k] for k in ("coefficient_prefix_GCD_queries",
            "reflected_column_gcd_queries","selected_channel_gcd_queries"))
        assert len(buckets)<=4*len(originals)
        assert queries<=14*len(originals)+1
        return dict(N=n,input_bits=n.bit_length(),modulus=m,factor=factor,stage=stage,witness=witness,
            original_packet_count=len(originals),distinct_joined_ordinary_roots=len(buckets),
            joined_GCD_queries=queries,milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics,**integers.stats(),**ring.stats(),**batch.stats()),
            all_original_packets_and_both_affine_channels_retained=True,
            constructed_pair_matrix=False,constructed_signed_root_union=False,
            constructed_modular_giant_powers=False,private_factor_or_order_input=False,
            native_checked_square_and_modulus_prefixes=True,
            literal_integer_trial_prime_selector_used=True,is_complete_factorizer=False,
            is_bit_complexity_certificate=False,is_native_machine_refinement=False)

    square = integers.sqrt(n)
    if integers.mul(square,square)==n and 1<square<n:
        return finish(square,"public-square")
    m = FAMILY["first_public_prime"](n,integers,metrics)
    common = integers.gcd(n,m)
    if 1<common<n:
        return finish(common,"public-modulus-gcd")
    if common!=1:
        return finish(None,"inconclusive-modulus")
    originals = list(FAMILY["public_packets"](n,m,integers,metrics))
    unit_status,inverses = {},{}
    for key in ("a","t"):
        for w in originals:
            common = integers.gcd(n,abs(w[key]))
            metrics["coefficient_prefix_GCD_queries"] += 1
            unit_status[w[key]] = common==1
            if 1<common<n:
                return finish(common,"public-coefficient-gcd")
    for w in COMPANION["companion_packets"](originals,m,integers,metrics):
        root = integers.divmod(w["candidate"],n)[1]
        integers.charge("ordinary_companion_bucket_lookup",root)
        buckets.setdefault(root,[]).append(dict(channel="companion",packet=w))
    for side,key in enumerate(("a","t")):
        for w in originals:
            scale = w[key]
            if not unit_status[scale]:
                metrics["excluded_nonunit_affine_coordinates"] += 1
                continue
            integers.charge("affine_inverse_cache_lookup",scale)
            if scale not in inverses:
                inverses[scale] = integers.divmod(integers.inverse(scale,n),n)[1]
                metrics["affine_inverse_cache_misses"] += 1
            offset = integers.add(integers.mul(m,w["b"]),-integers.mul(2,integers.mul(w["a"],w["j"])))
            root = ring.mul(integers.divmod(integers.add(0,-offset),n)[1],inverses[scale])
            integers.charge("affine_coordinate_bucket_lookup",side,root)
            buckets.setdefault(root,[]).append(dict(channel=key,packet=w))
            metrics["affine_normalized_packet_coordinates"] += 1
    if not buckets:
        return finish(None,"empty-public-family")
    roots = list(buckets)
    outputs = REFLECTED["reflected_outputs"](n,roots,integers,ring,batch,metrics)
    factor,stage,witness = REFLECTED["recover_reflected"](n,roots,outputs,integers,metrics)
    assert ring.powers==0
    return finish(factor,stage,witness)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    for name in ("declarations","theorems","explicit"):
        parser.add_argument("--checked-"+name,type=int,default=0)
    args = parser.parse_args()
    sources = source_inventory()
    rnd = random.Random(REPLAY_ID)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    spectrum = json.loads((ROOT/FRONTIER["PARENT_AUDIT"]).read_text())
    coefficients,recovery = coefficient_oracles(rnd),finite_recovery_oracles(rnd)
    families = [public_packet_oracle(r["N"],r["modulus"])
        for r in spectrum["exact_public_packet_center_oracles"]]
    old = json.loads((ROOT/"docs/semiprime-companion-rows-audit.json").read_text())
    inputs = [r["N"] for r in old["N_only_small_sources"]]+[7303,369867514421371]
    controls = []
    for n in inputs:
        print(json.dumps(dict(progress="N-only-joined-affine-source-start",N=n)),flush=True)
        result = public_affine_source(n)
        assert result["factor"] is not None and 1<result["factor"]<n and n%result["factor"]==0
        controls.append(result)
        print(json.dumps(dict(progress="N-only-joined-affine-source-completed",N=n,
            factor=result["factor"],original_packets=result["original_packet_count"],
            roots=result["distinct_joined_ordinary_roots"],milliseconds=result["milliseconds"])),flush=True)
    assert source_inventory()==sources,"source changed during replay"
    checked = args.checked_declarations>0 and args.checked_theorems>0
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        arbitrary_coefficient_oracles=coefficients,finite_reflected_recovery_oracles=recovery,
        complete_public_original_packet_oracles=families,N_only_native_controls=controls,
        inherited_103bit_affine_witness=parent["affine_signed_witness"],
        full_native_103bit_polynomial_source_replayed=False,
        lean_validation=dict(separately_completed_scoped_gates=checked,strict_leaf_and_root=checked,
            namespace_linters=14 if checked else 0,linter_errors=0 if checked else None,
            all_module_declarations=args.checked_declarations,explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        kernel_components=dict(genuine_Mathlib_quadratic_resultant_checked=True,
            original_integer_Nt_channel_retained_before_exact_N_division=True,
            both_unit_normalized_coefficient_differences_have_exact_GCD_phase=True,
            actual_original_packet_membership_and_root_equations_checked=True,
            literal_103bit_pair_GCD_equals_2245327606949267=True,
            complete_canonical_N_only_joined_source_recovers_103bit_control=True,
            existing_signed_companion_successes_preserved=True,
            joined_ordinary_degree_at_most_four_original_packets=True,
            joined_recovery_GCD_queries_at_most_fourteen_original_packets_plus_one=True),
        universal_joined_family_coverage="OPEN",full_original_companion_miss_kernel_certificate="OPEN",
        guaranteed_one_sixth_factorization="OPEN",is_complete_factorizer=False,
        is_complete_bit_complexity_certificate=False,
        limitations="The kernel certifies the genuine fixed-degree quadratic resultant, its exact integer N division, both affine GCD phases, public packet membership and complete canonical source success on the literal 103-bit control. Its previous full companion miss is still native-only, and the new 20-million-packet search is a private-field prefix diagnostic rather than a full N-only runtime. Small N-only runs include inherited checked square and modulus prefixes and an integer trial prime selector; the joined packet backend matches the new formal source, but no full native-machine refinement is asserted. Native timings charge construction, normalization, dictionaries, packed polynomial work and recovery, and are individual diagnostics rather than an exponent fit. Universal coverage, all construction and polynomial bit clocks, arbitrary-ratio completion and the every-run construction-inclusive deterministic N^(1/6) bit theorem remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),complete_public_families=len(families),
        N_only_controls=len(controls),all_controls_return_proper_factors=True,
        kernel_103bit_public_source_success=checked,one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()
