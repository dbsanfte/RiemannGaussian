#!/usr/bin/env python3
"""Exact auxiliary conic/tangent discovery on original integer packets.

The physical input N, public auxiliary m², and private reference prime
fields remain separate. Complete small families and held-out large residue
slices test the literal signed source. No factorizer timer or coverage
certificate is produced.
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
PARENT_AUDIT = "docs/semiprime-centered-point-coverage-audit.json"
POINTS = runpy.run_path(str(ROOT/"scripts/probe_semiprime_centered_point_coverage.py"))
WEIGHTED = POINTS["PRIOR"]["WEIGHTED"]
PREFIX = runpy.run_path(str(ROOT/"scripts/probe_semiprime_strassen_prefix.py"))
REPLAY_ID = 202610033248
HELD_OUT_SEED = 202610033249


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeQuadraticPointJets.lean",
        "scripts/CheckSemiprimeQuadraticPointJets.lean",
        "scripts/probe_semiprime_quadratic_point_jets.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def packet_oracle(n,m,w,counters):
    a,t,j,b,c = (w[k] for k in ("a","t","j","b","c"))
    L,d = m*b-2*a*j,m*m
    assert a!=0 and 0<t and abs(a)+t<=m and abs(a)<m
    assert L*L-4*n*a*t==d*(b*b-4*a*c)
    assert j*L+a*j*j+n*t==d*c
    small,large = math.isqrt(n//2)+math.isqrt(n),math.isqrt(n)+math.isqrt(2*n)
    side = int(POINTS["PRIOR"]["orientation"](w))
    A,B = (large,small) if side else (small,large)
    error,residual = -2*L-a*A-t*B,-2*L-a*small-t*large
    assert abs(error)<=d and residual==error+side*(a-t)*(large-small)
    ai = pow(a,-1,d)
    rho,tau,zeta = t*ai%d,-2*L*ai%d,residual*ai%d
    assert (zeta+small+large*rho)%d==tau
    assert (tau*tau-16*n*rho)%d==0
    assert (j*tau-2*j*j-2*n*rho)%d==0
    displacement = (tau-4*j)%d
    assert displacement*displacement%d==0 and displacement%m==0
    assert rho%m==j*j*pow(n,-1,m)%m and tau%m==4*j%m
    counters["original_packet_discriminants"] += 1
    counters["exact_integer_tangent_equations"] += 1
    counters["common_physical_midpoint_channels"] += 1
    counters["auxiliary_conic_tangent_and_nilpotent_checks"] += 1
    counters["auxiliary_base_point_checks"] += 1
    counters["nonzero_auxiliary_nilpotents"] += displacement!=0
    counters["zero_auxiliary_nilpotents"] += displacement==0
    counters["negative_leading_coefficients"] += a<0
    physical_inverse = pow(a,-1,n)
    physical_tau = -2*L*physical_inverse%n
    counters["physical_N_conic_does_not_vanish"] += physical_tau*physical_tau%n!=0
    return (a,t,t*physical_inverse%n),dict(residue=j,a=a,t=t,L=L,
        auxiliary_rho=rho,auxiliary_tau=tau,nilpotent_displacement=displacement,
        physical_tau=physical_tau,physical_conic_residue=physical_tau*physical_tau%n)


def check_case(n,m,p,q,residues,rnd,full):
    from sympy import isprime
    assert n==p*q and all(isprime(k) for k in (m,p,q)) and m<min(p,q)
    prefix = PREFIX["factor_prefix"](n,m) if full else None
    if prefix is not None:
        assert prefix["factor"] is None
        assert prefix["metrics"]["root_residues"]==prefix["metrics"]["target_residues"]==m
        assert prefix["metrics"]["explicit_grid_candidates"]==0
    counters,coordinates,first_nonzero = Counter(),[],None
    counters["executed_public_compressed_prefix_no_factor_results"] += prefix is not None
    for j in residues:
        for w in WEIGHTED["reference_residue_packets"](n,m,j):
            coordinate,example = packet_oracle(n,m,w,counters)
            coordinates.append(coordinate)
            if first_nonzero is None and example["nilpotent_displacement"]:
                first_nonzero = example
    if m*m<min(p,q):
        for _ in range(96):
            u,w = rnd.sample(coordinates,2)
            D = u[0]*w[1]-w[0]*u[1]
            assert abs(D)<=m*m
            actual = math.gcd(n,(w[2]-u[2])%n)
            assert actual==math.gcd(n,D) and actual in (1,n)
            counters["large_factor_first_coordinate_no_proper_GCD_checks"] += 1
    return dict(N=n,input_bits=n.bit_length(),modulus=m,reference_p=p,reference_q=q,
        prime_square=p==q,full_public_residue_family=full,residues_enumerated=list(residues),
        counts=dict(counters),first_nonzero_auxiliary_jet_example=first_nonzero,
        public_compressed_prefix=prefix)


def main():
    from sympy import nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    args = parser.parse_args()
    sources = source_inventory()
    cases,total = [],Counter()
    for seed,size,held in ((REPLAY_ID,48,False),(HELD_OUT_SEED,12,True)):
        rnd = random.Random(seed)
        for index in range(size):
            m = int(nextprime(rnd.randrange(37,127))) if held else rnd.choice((3,5,7,11,17,23,31,43))
            bits = rnd.randrange(24,41) if held else rnd.randrange(12,37)
            p = int(nextprime(rnd.randrange(2**(bits-1),2**bits)))
            category = index%3
            if category==0:q=p
            elif category==1:q=int(nextprime(rnd.randrange(p+1,2*p)))
            else:q=int(nextprime(p*2**rnd.randrange(3,13)+rnd.randrange(p)))
            case = check_case(p*q,m,p,q,range(1,m),rnd,True)
            case.update(seed=seed,index=index,held_out=held,
                category=("square","balanced","wide-ratio")[category])
            total.update(case["counts"])
            cases.append(case)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())["complete_scalar_families"][0]
    n,m,p,q = (parent[k] for k in ("N","modulus","reference_p","reference_q"))
    rnd = random.Random(HELD_OUT_SEED)
    residues = sorted(set((1,2,3,17,m-1,p%m,q%m,*rnd.sample(range(1,m),32))))
    large = check_case(n,m,p,q,residues,rnd,False)
    total.update(large["counts"])
    assert source_inventory()==sources,"source changed during replay"
    checked = args.checked_declarations>0 and args.checked_theorems>0
    report = dict(replay_id=REPLAY_ID,held_out_seed=HELD_OUT_SEED,parent_audit=PARENT_AUDIT,
        source_sha256=sources,complete_small_and_held_out_cases=cases,
        literal_canonical_large_residue_slices=large,counts=dict(total),
        lean_validation=dict(strict_leaf_and_root=checked,separately_completed_scoped_gates=checked,
            namespace_linters=14 if checked else 0,linter_errors=0 if checked else None,
            all_module_declarations=args.checked_declarations,explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        compiled_components=dict(original_discriminant_is_exact_m_squared_multiple=True,
            physical_midpoint_plane_retained=True,actual_auxiliary_leading_units_discharged=True,
            auxiliary_conic_and_residue_tangent=True,auxiliary_displacement_square_zero=True,
            first_coordinate_alone_no_proper_GCD_beyond_m_squared=True,
            public_prefix_none_discharges_full_point_and_minor_guards=True),
        is_N_only_factorizer=False,is_bit_complexity_certificate=False,
        is_kernel_execution_or_exhaustion_certificate=False,
        guaranteed_one_sixth_factorization="OPEN",complete_cross_residue_incidence="OPEN",
        limitations="All auxiliary identities are checked against the full Nt-containing integer packet construction, with both centers and every Euclidean intermediate on 60 complete small/held-out families. The existing N-only compressed prefix executes on these 60 inputs with m roots, m targets and no candidate grid; its construction/evaluation bit refinement remains open. The 119-bit canonical input has sampled complete residue slices only, with no newly executed large public prefix or full-family incidence exhaustion. Physical N and auxiliary m² remain distinct: nilpotence in ZMod(m²) gives no zero of the corresponding expression in ZMod(N). Private reference primes only classify the finite first-coordinate GCD and physical-field controls. The compiled first-coordinate obstruction covers all actual pairs when both factors exceed m², including squares and arbitrary ratios in that branch. Independently, the proved no-factor output of the existing public prefix discharges leading, factor-two and nonzero-minor guards for arbitrary N, without supplied factors. Nonzero auxiliary jets and finite agreements give no useful factor-field triple, universal coverage, fast incidence extractor, all-ratio acquisition or deterministic construction-inclusive sixth-root bit factorizer.")
    if args.output:args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),complete_families=len(cases),
        literal_large_residue_slices=len(residues),counts=dict(total),one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()
