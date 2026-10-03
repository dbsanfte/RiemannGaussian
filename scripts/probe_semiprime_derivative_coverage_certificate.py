#!/usr/bin/env python3
"""Pin the sound Lean checker and actual orders to the frozen native replay.

All public-source construction timings belong to the unchanged parent.
This script rechecks the two reference residue sorts and records the
separate kernel checker. The literal whole-family certificate remains
native-only after the monolithic kernel reduction exceeded the chosen
memory envelope. This is not an N-only runtime measurement.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-row-derivative-coverage-audit.json"
REPLAY_ID = 202610033103
DERIVATIVE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_row_derivative.py"))


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeDerivativeCoverage.lean",
        "scripts/CheckSemiprimeDerivativeCoverage.lean",
        "scripts/probe_semiprime_derivative_coverage_certificate.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources=source_inventory()
    parent=json.loads((ROOT/PARENT_AUDIT).read_text())
    control=parent["exhausted_N_only_control"]
    reference=parent["reference_cases"][-1]
    n,m,p,q=control["N"],control["modulus"],reference["reference_p"],reference["reference_q"]
    assert (n,m,p,q)==(2518766418595894637609,3691,39167077933,64308254573)
    exponents=[w["exponent"] for w in DERIVATIVE["reference_packets"](n,m)]
    assert len(exponents)==control["distinct_public_roots"]==394276
    checks=[]
    for d in (p-1,q-1):
        residues=sorted(e % d for e in exponents)
        assert all(a<b for a,b in zip(residues,residues[1:]))
        checks.append(dict(actual_order=d,residues=len(residues),
            adjacent_comparisons=max(0,len(residues)-1),strictly_increasing=True))
    assert source_inventory()==sources,"source changed during replay"
    report=dict(replay_id=REPLAY_ID,source_sha256=sources,
        scope="Sound kernel certificate checker and actual orders; large failure remains native-only",
        kernel_checked_failure_control=False,reference_sort_checks=checks,
        control=control,reference_control=reference,
        separate_inverse_axis_reference=parent["separate_inverse_axis_reference"],
        compiled_checker_soundness="RiemannGaussian.SemiprimeDerivativeCoverage.checkedResidues_power_injective",
        compiled_conditional_transport="RiemannGaussian.SemiprimeDerivativeCoverage.publicRows_none_of_checked_orders",
        compiled_actual_orders=["control_p_order","control_q_order"],
        compiled_complete_family_certificates=[],
        attempted_monolithic_kernel_certificate="Stopped after memory exceeded 50 GB; no literal failure theorem claimed",
        audit_commands=["lake build RiemannGaussian.SemiprimeDerivativeCoverage --wfail",
            "lake env lean -DwarningAsError=true RiemannGaussian.lean",
            "lake env lean -DwarningAsError=true scripts/CheckSemiprimeDerivativeCoverage.lean"],
        Lean_validation_is_separate_from_this_reference_script=True,
        is_N_only_runtime_measurement=False,is_bit_complexity_certificate=False,
        is_universal_factoring_lower_bound=False,one_sixth_guarantee="OPEN",
        limitations="The compiled module proves that the structural sort preserves the entire input multiset and that a successful adjacent-residue certificate gives full power injectivity at a verified actual order. It also checks both literal component primes and actual base orders. Its full-family exhaustion transport still requires the two full residue certificates. Those certificates are checked here only by native reference sorting: monolithic Lean kernel reduction was stopped after exceeding 50 GB of memory, and no closed literal failure theorem or custom axiom was added. This retains the parent's native-only failure status and frozen complete-source timing. The parent inverse-axis reference has extra local hits, and a separate compiled reciprocal detector recovers on this N. Different bases/moduli/families and all one-sixth factoring algorithms are not excluded. GCD-query and scalar-axis bounds are not a complete bit theorem. Universal arbitrary-ratio every-run N-only one-sixth factorization remains open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),reference_sort_checks=checks,
        kernel_checked_failure_control=False,one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()
