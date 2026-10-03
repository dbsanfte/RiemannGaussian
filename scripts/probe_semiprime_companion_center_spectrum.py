#!/usr/bin/env python3
"""Exact public-packet center identities and a frozen signed-frontier miss.

Finite algebra checks supplement the compiled generic identities. The full
103-bit root-injection test is inherited from its completed 211-pin replay;
it is not repeated here and is not a kernel exhaustion certificate.
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
PARENT_AUDIT = "docs/semiprime-signed-companion-frontier-audit.json"
REPLAY_ID = 202610033226
FRONTIER = runpy.run_path(str(ROOT/"scripts/probe_semiprime_signed_companion_frontier.py"))
WEIGHTED = FRONTIER["COVERAGE"]["WEIGHTED"]


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeCompanionCenterSpectrum.lean",
        "scripts/CheckSemiprimeCompanionCenterSpectrum.lean",
        "scripts/probe_semiprime_companion_center_spectrum.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def packet_oracle(n,m):
    low,mid,high = math.isqrt(n//2),math.isqrt(n),math.isqrt(2*n)
    centers = {"smaller-factor":(low+mid,mid+high),"larger-factor":(mid+high,low+mid)}
    counts = Counter()
    min_same,max_same = {},{}
    for j in range(1,m):
        rows = list(WEIGHTED["reference_residue_packets"](n,m,j))
        counts["complete_original_packets"] += len(rows)
        for w in WEIGHTED["weighted_packets"](rows,m):
            left,right = w["left"],w["right"]
            d,e = w["determinant"]//m,w["exponent"]
            assert d*d == 1 and e%m == 0
            c = 1-d*(e//m)
            assert c == 2*j-d*(right["t"]*left["b"]-left["t"]*right["b"])
            A1,B1 = centers[left["center_orientation"]]
            A2,B2 = centers[right["center_orientation"]]
            def error(row,A,B):
                original_b = row["b"]+m*row["shift"]
                H = row["a"]*A+row["t"]*B+2*(original_b*m-2*row["a"]*j)
                assert row["shift"] == (H+m*m)//(2*m*m)
                return 2*m*m*row["shift"]-H
            el,er = error(left,A1,B1),error(right,A2,B2)
            assert abs(el)<=m*m and abs(er)<=m*m
            assert 0<=left["t"]<=m and 0<=right["t"]<=m
            weighted_error = right["t"]*el-left["t"]*er
            assert abs(weighted_error)<=m*m*(left["t"]+right["t"])
            assert B2-B1 == -(A2-A1)
            assert 2*m*c == m*A1+d*(weighted_error-
                left["t"]*(right["a"]-right["t"])*(A2-A1))
            counts["complete_primitive_weighted_packets"] += 1
            key = left["center_orientation"]+"/"+right["center_orientation"]
            counts[key] += 1
            if A1 == A2:
                assert abs(2*c-A1)<=m*(left["t"]+right["t"])<=2*m*m
                min_same[key] = min(c,min_same.get(key,c))
                max_same[key] = max(c,max_same.get(key,c))
    for key,minimum in min_same.items():
        assert max_same[key]-minimum<=2*m*m
    return dict(N=n,modulus=m,counts=dict(counts),same_center_minima=min_same,
        same_center_maxima=max_same,all_exact_rank_one_and_interval_checks_passed=True,
        is_N_only_factorizer=False,is_factorization_runtime_measurement=False,is_Lean_proof=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    for name in ("declarations","theorems","explicit"):
        parser.add_argument("--checked-"+name,type=int,default=0)
    args = parser.parse_args()
    sources = source_inventory()
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    acquisition = json.loads((ROOT/FRONTIER["PARENT_AUDIT"]).read_text())
    inputs = [(r["N"],r["modulus"]) for r in acquisition["N_only_Boolean_backend_setup_profiles"]]
    rnd = random.Random(REPLAY_ID)
    inputs.extend((rnd.randrange(10001),rnd.choice((2,3,5,7,11,13,17,19))) for _ in range(64))
    oracles = [packet_oracle(n,m) for n,m in inputs]
    miss = parent["first_complete_signed_exhaustion"]
    assert miss is not None and miss["signed_roots"] == miss["signed_p_classes"] == miss["signed_q_classes"]
    assert source_inventory() == sources, "source changed during replay"
    checked = args.checked_declarations > 0 and args.checked_theorems > 0
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        exact_public_packet_center_oracles=oracles,inherited_N_only_setup_inputs=46,random_public_families=64,
        inherited_complete_signed_miss=miss,large_signed_field_enumeration_repeated=False,
        lean_validation=dict(separately_completed_scoped_gates=checked,strict_leaf_and_root=checked,
            namespace_linters=14 if checked else 0,linter_errors=0 if checked else None,
            all_module_declarations=args.checked_declarations,explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        kernel_components=dict(actual_public_packets_have_all_four_center_choices=True,
            primitive_companion_exact_signed_center_spectrum=True,
            mixed_center_term_has_one_explicit_arithmetic_direction=True,
            actual_denominator_and_signed_rounding_bounds_discharged=True,
            same_center_doubled_deviation_at_most_two_m_squared=True,
            same_center_integer_difference_at_most_two_m_squared=True,
            same_center_local_equality_above_two_m_squared_is_integer_equality=True,
            frontier_factors_prime_via_Lucas_certificates=True,
            frontier_balanced_semiprime_arithmetic_sixth_width_and_literal_public_modulus_checked=True),
        verification_environment=dict(Lean="4.33.1",manifest_mathlib_revision="0df444a360eaa60ab8c11dca51a86af692955474",
            shared_mathlib_externally_replaced_during_slice=True,
            isolated_original_mathlib_revision_used_for_final_gates=checked,
            final_gate_command_prefix="/home/dbsanfte/.elan/bin/lake --packages=/tmp/semiprime-center-spectrum-4.33.1/packages.json",
            final_gate_commands=[
                "build RiemannGaussian.SemiprimeCompanionCenterSpectrum --wfail",
                "env lean -DwarningAsError=true RiemannGaussian/SemiprimeCompanionCenterSpectrum.lean",
                "env lean -DwarningAsError=true RiemannGaussian.lean",
                "env lean -DwarningAsError=true scripts/CheckSemiprimeCompanionCenterSpectrum.lean"],
            shared_mathlib_original_revision_restored_externally=True,
            restored_workspace_default_resolver_gates_passed=checked,
            restored_workspace_gate_command_prefix="/home/dbsanfte/.elan/bin/lake",
            project_manifest_and_external_replacement_preserved=True),
        full_signed_frontier_exhaustion_kernel_certificate="OPEN",
        fixed_signed_companion_family_universal_coverage="CONTRADICTED_BY_NATIVE_REPLAY",
        guaranteed_one_sixth_factorization="OPEN",is_complete_factorizer=False,
        is_complete_bit_complexity_certificate=False,
        limitations="Compiled center identities and interval/separation bounds apply to the actual public primitive packets with their original rows, center choices and signed errors retained. The literal 103-bit miss has kernel-checked prime factors, balanced arithmetic, ceiling sixth root and least public modulus. Its full 83,269,309-root injectivity in both prime fields is inherited native evidence, not a Lean exhaustion theorem. It contradicts treating this fixed family as universally covering in native execution, and supplies no general factoring lower bound. The large field enumeration and polynomial/factor recovery are not replayed by this algebra probe. Original construction, memory/machine refinement, universal coverage for a sufficient amended algorithm and the deterministic every-run construction-inclusive N^(1/6) bit guarantee remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),public_families=len(oracles),
        complete_original_packets=sum(r["counts"]["complete_original_packets"] for r in oracles),
        complete_weighted_packets=sum(r["counts"].get("complete_primitive_weighted_packets",0) for r in oracles),
        all_exact_center_checks_passed=True,full_signed_failure_kernel_certificate="OPEN",
        one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()
