#!/usr/bin/env python3
"""Independent changed integrals and zero controls for the automatic winner."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import flint

from check_shift_ratio_analytic import complete_B, coefficients, real, log, square
from check_compensated_shift_analytic import actual_zeros, residues

BASE = Path(__file__).resolve().parent


def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path): return json.loads(Path(path).read_text())
def write(path, value): Path(path).write_text(json.dumps(value, indent=2) + "\n")
def digest(value): return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family-run-dir", type=Path, required=True)
    args = parser.parse_args()
    family = args.family_run_dir.resolve()
    destination = family / "selected-native"
    sourcepath = destination / "selected_analytic.json"
    source = read(sourcepath)
    protocol = read(destination / "protocol.json")
    assert source["all_passed"] and source["protocol_sha256"] == digest(protocol)
    assert protocol["family_search_sha256"] == sha(family / "family_gap_search.json")
    assert protocol["family_verification_sha256"] == sha(family / "family_gap_verification.json")
    assert protocol["producer_code_sha256"] == sha(BASE / "compensated_selected_analytic.py")
    assert protocol["native_backend_code_sha256"] == sha(BASE / "compensated_shift_analytic.py")
    assert protocol["coefficient_backend_code_sha256"] == sha(BASE / "compensated_shift_grammar.py")
    selected = read(family / "family_gap_search.json")["selected_operator"]["candidate"]
    assert source["selected_candidate"] == protocol["selected_candidate"] == selected
    assert [r["s"] for r in source["actual_zeta_ball_checks"]] == protocol["cases"]
    assert protocol["selection_closed_before_native_cases"] and protocol["evaluation_does_not_reselect_or_adapt"]
    flint.ctx.prec = 512
    flint.ctx.cap = 24
    A = [(Q(w), Q(v)) for w, v in selected["atoms"]]
    fingerprint = {"source_sha256": sha(sourcepath), "checker_code_sha256": sha(Path(__file__)),
                   "independent_native_backend_code_sha256": sha(BASE / "check_shift_ratio_analytic.py"),
                   "independent_zero_backend_code_sha256": sha(BASE / "check_compensated_shift_analytic.py"),
                   "precision": flint.ctx.prec, "series_cap": flint.ctx.cap, "coefficient_cutoff": 768,
                   "comparison_gate": "complete enclosure overlap with bounded radii and a separated altered-prime control",
                   "maximum_native_coordinate_radius": "1/10000000000",
                   "flint_version": flint.__version__}
    cutoff = fingerprint["coefficient_cutoff"]
    B = {v: coefficients(cutoff, v) for w, v in A}
    records = []
    for index, row in enumerate(source["actual_zeta_ball_checks"]):
        path = destination / f"independent_native_group_{index}.json"
        previous = read(path) if path.exists() else {}
        if previous.get("fingerprint") == fingerprint and previous.get("record", {}).get("all_passed"):
            records.append(previous["record"])
            print("Reused post-selection independent group", index, flush=True)
            continue
        sigma, height = map(Q, row["s"])
        s = flint.acb(real(sigma), real(height))
        value = flint.acb(0)
        certificates = []
        for w, v in A:
            atomic, certificate = complete_B(s, sigma, v)
            value += real(w) * atomic
            certificates.append({"weight": str(w), "v": str(v), "certificate": certificate})
        supplied = flint.acb(flint.arb(row["native_real_ball"]), flint.arb(row["native_imag_ball"]))
        assert value.overlaps(supplied)
        partial = sum((sum((real(w) * B[v][n] for w, v in A), flint.arb(0)) * (-s * log(n)).exp()
                       for n in range(2, cutoff + 1)), flint.acb(0))
        tail = real(cutoff) ** real(1 - sigma) / real(sigma - 1)
        difference = (partial - value).abs_upper()
        wrong = (partial + real(Q(1, 17)) * (-s * log(19)).exp() - value).abs_lower()
        overlap = value.overlaps(partial + square(tail))
        radius_cap = real(fingerprint["maximum_native_coordinate_radius"])
        bounded_radius = value.real.rad() < radius_cap and value.imag.rad() < radius_cap
        assert overlap and bounded_radius and wrong > tail
        record = {"s": row["s"], "native_real_ball": value.real.str(35), "native_imag_ball": value.imag.str(35),
                  "source_native_overlap": True, "atomic_integrals_evaluated_separately_after_rescaling": True,
                  "infinite_integral_and_k_tails_retained": True, "atomic_certificates": certificates,
                  "coefficient_cutoff": cutoff, "coefficient_tail_ball": tail.str(35),
                  "rigorous_coefficient_series_enclosure_overlaps_native": overlap,
                  "native_coordinate_radius_cap_passed": bool(bounded_radius),
                  "difference_upper_ball": difference.str(35), "wrong_prime": 19,
                  "wrong_prime_difference_lower_ball": wrong.str(35), "all_passed": True}
        write(path, {"fingerprint": fingerprint, "record": record})
        records.append(record)
        print("Post-selection independent complete native group", index, row["s"], True, flush=True)
    assert len(records) == len(protocol["cases"]) == 2
    signs = residues(A)
    zeros = actual_zeros(source, A)
    checks = {"frozen_automatic_choice_and_fresh_post_selection_cases": True,
              "independent_rescaled_complete_integrals_and_infinite_tails": True,
              "changed_subset_coefficients_precision_cutoff_and_wrong_prime_controls": True,
              "signed_zero_order_and_pole_residues": signs["all_passed"],
              "nested_actual_zero_disks_and_corridor_dependencies": zeros["all_passed"],
              "no_reselection_continuation_estimate_or_historical_novelty_claim": not source["new_RH_estimate_proved"]}
    result = {"all_passed": all(checks.values()), "checks": checks, "fingerprint": fingerprint,
              "source_artifact_sha256": sha(sourcepath), "protocol_sha256": digest(protocol),
              "selected_candidate": selected, "native_complete_signed_B_audit": {"records": records, "all_passed": True},
              "signed_zero_signature_audit": signs, "actual_zero_and_corridor_audit": zeros,
              "mathematical_audit_imports_production_code": False, "new_RH_estimate_proved": False,
              "historical_novelty_established": False, "verified_new_operators": []}
    write(destination / "selected_analytic_verification.json", result)
    print("Independent automatic-winner analytic audit", sum(checks.values()), "/", len(checks), flush=True)


if __name__ == "__main__": main()
