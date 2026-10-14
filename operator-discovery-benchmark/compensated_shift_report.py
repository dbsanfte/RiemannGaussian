#!/usr/bin/env python3
"""Publish the signed family only after independent arithmetic/analytic audits.

The guided family and its automatic estimate certificates remain separate
from the frozen generic-language discovery stage.
"""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

BASE = Path(__file__).resolve().parent
DEST = BASE / "compensated-shift-results"


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()).hexdigest()


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def summary(family_directory):
    family_directory = Path(family_directory).resolve()
    dependencies = {}

    def pin(path, expected=None):
        path = Path(path).resolve()
        actual = sha(path)
        require(expected is None or actual == expected, "signed audit dependency changed: " + str(path))
        dependencies[str(path.relative_to(BASE)) if path.is_relative_to(BASE) else str(path)] = actual
        return actual

    def passed(path):
        value = read(path)
        require(value["all_passed"] is True and bool(value["checks"]) and
                all(v is True for v in value["checks"].values()), "signed audit incomplete: " + str(path))
        require(value["verified_new_operators"] == [], "historical novelty needs a separate audit")
        pin(path)
        return value

    sourcepath = DEST / "compensated_shift_search.json"
    source = read(sourcepath)
    source_sha = pin(sourcepath)
    require(source["all_passed"] and not source["coefficient_operator_uses_prime_or_factor_oracle"],
            "arithmetic source/oracle scope failed")
    pin(BASE / "compensated_shift_search.py", source["producer_code_sha256"])
    pin(BASE / "compensated_shift_grammar.py", source["grammar_code_sha256"])
    pin(BASE / "compensated_shift_proof.txt", source["proof_sha256"])
    arithmetic = passed(DEST / "compensated_shift_verification.json")
    require(arithmetic["source_artifact_sha256"] == source_sha, "arithmetic audit source changed")
    pin(BASE / "check_compensated_shift.py", arithmetic["checker_code_sha256"])
    pin(BASE / "check_shift_ratio.py", arithmetic["independent_subset_backend_code_sha256"])
    pin(BASE / "compensated_operator.py", arithmetic["public_entry_code_sha256"])
    require(not arithmetic["mathematical_audit_imports_production_code"], "arithmetic audit is not independent")

    gap_directory = DEST / "gap-certificates"
    gap = passed(gap_directory / "global_gap_verification.json")
    require(gap["source_arithmetic_sha256"] == source_sha, "global-gap arithmetic source changed")
    pin(gap_directory / "gap_probe.json", gap["source_probe_sha256"])
    pin(BASE / "check_compensated_global_gap.py", gap["checker_code_sha256"])
    pin(BASE / "compensated_global_gap_proof.txt", gap["proof_sha256"])
    require(arithmetic["global_gap_verification_sha256"] == sha(gap_directory / "global_gap_verification.json"),
            "arithmetic audit uses a different global-gap certificate")
    probe = read(gap_directory / "gap_probe.json")
    pin(BASE / "compensated_global_gap_probe.py", probe["fingerprint"]["probe_code_sha256"])
    require(gap["global_all_composite_bound_proved"] and gap["universal_composite_bound"] == "7/110",
            "representative all-integer bound incomplete")

    analytic_path = DEST / "compensated_shift_analytic.json"
    analytic_source = read(analytic_path)
    analytic_sha = pin(analytic_path)
    require(analytic_source["all_passed"] and analytic_source["arithmetic_source_artifact_sha256"] == source_sha,
            "analytic source no longer matches arithmetic")
    pin(BASE / "compensated_shift_analytic.py", analytic_source["fingerprint"]["producer_code_sha256"])
    analytic = passed(DEST / "compensated_shift_analytic_verification.json")
    require(analytic["source_artifact_sha256"] == analytic_sha and
            analytic["fingerprint"]["arithmetic_source_sha256"] == source_sha,
            "analytic audit source changed")
    pin(BASE / "check_compensated_shift_analytic.py", analytic["fingerprint"]["checker_code_sha256"])
    pin(BASE / "check_shift_ratio_analytic.py", analytic["fingerprint"]["independent_backend_code_sha256"])
    require(not analytic["mathematical_audit_imports_production_code"], "analytic audit is not independent")
    zero_dependencies = analytic["actual_zero_and_corridor_audit"]
    pin(BASE / "shift-ratio-results/shift_ratio_analytic_verification.json",
        zero_dependencies["old_independent_zero_verification_sha256"])
    old_zero = read(BASE / "shift-ratio-results/shift_ratio_analytic_verification.json")
    pin(BASE / "shift-ratio-results/shift_ratio_analytic.json", old_zero["source_artifact_sha256"])
    pin(BASE / "fractional-prime-results/fractional_prime_analytic_verification.json",
        zero_dependencies["old_corridor_verification_sha256"])
    old_corridor = read(BASE / "fractional-prime-results/fractional_prime_analytic_verification.json")
    pin(BASE / "fractional-prime-results/fractional_prime_analytic.json", old_corridor["source_artifact_sha256"])
    native = analytic["native_complete_signed_B_audit"]["records"]
    require(len(native) == analytic_source["complete_signed_B_native_comparisons"] and
            all(r["all_passed"] and r["infinite_integral_and_k_tails_retained"] for r in native),
            "complete native-zeta audit incomplete")

    family_path = family_directory / "family_gap_search.json"
    family = read(family_path)
    family_sha = pin(family_path)
    family_audit = passed(family_directory / "family_gap_verification.json")
    require(family_audit["source_artifact_sha256"] == family_sha, "family-gap audit source changed")
    pin(BASE / "check_compensated_gap_family.py", family_audit["checker_code_sha256"])
    pin(BASE / "check_compensated_global_gap.py", family_audit["independent_polynomial_backend_code_sha256"])
    pin(BASE / "compensated_family_gap_proof.txt", family_audit["proof_sha256"])
    pin(family_directory / "protocol.json")
    pin(family_directory / "candidate_batch.json")
    protocol = read(family_directory / "protocol.json")
    batch = read(family_directory / "candidate_batch.json")
    require(family["protocol"] == protocol and protocol["source_sha256"] == source_sha and
            family["fingerprint"]["protocol_sha256"] == digest(protocol) and
            batch["protocol_sha256"] == digest(protocol) and
            family["fingerprint"]["candidate_batch_sha256"] == digest(batch) and
            batch["frozen_before_certificate_outcomes"], "family protocol or frozen batch changed")
    pin(BASE / "compensated_gap_family_search.py", protocol["search_code_sha256"])
    pin(BASE / "compensated_global_gap_probe.py", protocol["polynomial_backend_code_sha256"])
    pin(BASE / "check_shift_ratio.py", protocol["counterexample_backend_code_sha256"])
    require(not family_audit["mathematical_audit_imports_production_code"], "family-gap audit is not independent")

    proved = []
    counterexamples = []
    leads = []
    audited = {(r["left"], r["right"]): r for r in family_audit["records"]}
    for row in family["records"]:
        candidate = row["candidate"]
        key = candidate["left"], candidate["right"]
        require(audited[key]["all_passed"] and audited[key]["status"] == row["status"], "family record not audited")
        entry = {"left": key[0], "right": key[1], "atoms": candidate["atoms"],
                 "proposed_gap": candidate["proposed_gap"], "status": row["status"],
                 "nonzero_leading_signature_at_every_positive_integer_zero_order": candidate["ordinary_zero_all_order_gate"]}
        if row["all_scale_bound_proved"]:
            require(row["status"] == "universal_arithmetic_theorem_proved", "unproved gap cannot be published")
            entry.update({"prime_coefficient": "1", "composite_absolute_bound": candidate["proposed_gap"],
                          "integer_or_prime_size_cutoff": None, "sharp_supremum": True,
                          "proof": "compensated_family_gap_proof.txt", "historical_novelty_established": False})
            proved.append(entry)
        elif row["status"] == "counterexample_found":
            entry["counterexample_index"] = str(row["counterexample_index"])
            counterexamples.append(entry)
        else:
            require(row["status"] == "numerical_lead", "unknown family result status")
            entry["unproved_regions"] = [{k: r[k] for k in ("omega", "g", "repeated_exponent", "status")}
                                          for r in row.get("finite_simplex_regions", [])
                                          if r["status"] not in ("universal_simplex_bound_certified", "exact_two_prime_pair_certificate")]
            leads.append(entry)
    require((len(proved), len(counterexamples), len(leads)) ==
            (family_audit["proved_global_gap_estimates"], family_audit["rigorous_counterexamples"], family_audit["numerical_leads_retained"]),
            "family status counts changed")
    eligible = [r for r in proved if r["nonzero_leading_signature_at_every_positive_integer_zero_order"]]
    best = min(eligible, key=lambda r: Fraction(r["composite_absolute_bound"])) if eligible else None
    if best is not None:
        require(family_audit["selected_parameters"] ==
                {"left": best["left"], "right": best["right"], "gap": best["composite_absolute_bound"]},
                "automatic selection no longer matches the audited result")
    winner_native = {"status": "not_run", "groups": 0}
    selected_directory = family_directory / "selected-native"
    if (selected_directory / "selected_analytic.json").exists():
        selected_source = read(selected_directory / "selected_analytic.json")
        selected_protocol = read(selected_directory / "protocol.json")
        selected_check = passed(selected_directory / "selected_analytic_verification.json")
        require(selected_source["all_passed"] and selected_source["selected_candidate"] ==
                selected_protocol["selected_candidate"] == selected_check["selected_candidate"] ==
                family["selected_operator"]["candidate"], "native audit no longer validates the automatic choice")
        pin(selected_directory / "selected_analytic.json", selected_check["source_artifact_sha256"])
        pin(selected_directory / "protocol.json")
        require(selected_source["protocol_sha256"] == selected_check["protocol_sha256"] == digest(selected_protocol) and
                selected_protocol["family_search_sha256"] == family_sha and
                selected_protocol["family_verification_sha256"] == sha(family_directory / "family_gap_verification.json") and
                selected_protocol["selection_closed_before_native_cases"] and
                selected_protocol["evaluation_does_not_reselect_or_adapt"], "post-selection native protocol changed")
        pin(BASE / "compensated_selected_analytic.py", selected_protocol["producer_code_sha256"])
        pin(BASE / "compensated_shift_analytic.py", selected_protocol["native_backend_code_sha256"])
        pin(BASE / "compensated_shift_grammar.py", selected_protocol["coefficient_backend_code_sha256"])
        pin(BASE / "check_compensated_selected_analytic.py", selected_check["fingerprint"]["checker_code_sha256"])
        pin(BASE / "check_shift_ratio_analytic.py", selected_check["fingerprint"]["independent_native_backend_code_sha256"])
        pin(BASE / "check_compensated_shift_analytic.py", selected_check["fingerprint"]["independent_zero_backend_code_sha256"])
        require(not selected_check["mathematical_audit_imports_production_code"], "winner native audit is not independent")
        selected_records = selected_check["native_complete_signed_B_audit"]["records"]
        require(len(selected_records) == len(selected_protocol["cases"]) and
                [r["s"] for r in selected_records] == selected_protocol["cases"] and
                all(r["all_passed"] and r["infinite_integral_and_k_tails_retained"] and
                    r["rigorous_coefficient_series_enclosure_overlaps_native"] and
                    r["native_coordinate_radius_cap_passed"] for r in selected_records),
                "winner complete native-zeta groups incomplete")
        winner_native = {"status": "independently_verified", "left": best["left"], "right": best["right"],
                         "groups": len(selected_records), "s": selected_protocol["cases"],
                         "simple_zero_signature": selected_source["simple_zero_signature"],
                         "post_selection_fresh_cases": True, "evaluation_does_not_reselect_or_adapt": True,
                         "comparison": "complete enclosure overlap, bounded radii and separated altered-prime controls",
                         "domain": "Re(s)>1, complete integral and Mobius-index tails"}
    representative = source["selected_operator"]
    checks = {"arithmetic": arithmetic["checks"], "analytic": analytic["checks"],
              "representative_global_gap": gap["checks"], "family_global_gaps": family_audit["checks"]}
    if winner_native["status"] != "not_run":
        checks["automatic_winner_analytic"] = selected_check["checks"]
    return {"status": "guided_signed_family_and_automatic_gap_certificates_independently_verified",
            "family_run_directory": str(family_directory), "dependencies": dependencies,
            "discovery_origin": "guided signed family; estimates tested and selected by a frozen automatic certificate protocol",
            "attributed_to_autonomous_generic_grammar": False,
            "coefficient_oracle_access": "none in operator producer; explicit factor/subset evaluator queries for counterexamples",
            "arithmetic_coefficient_checks": arithmetic["coefficient_audit"]["independent_full_prefix_coefficients_checked"],
            "coefficient_cutoff": source["coefficient_cutoff"], "checks": checks,
            "proved_global_estimates": proved, "counterexamples": counterexamples, "numerical_leads": leads,
            "independent_polynomial_certificates_checked": family_audit["independent_polynomial_certificates_checked"],
            "automatically_selected_operator": best,
            "complete_native_zeta_audit": {"left": representative["left"], "right": representative["right"],
                                           "groups": len(native), "parameters_audited": [[representative["left"], representative["right"]]],
                                           "s": [r["s"] for r in native], "domain": "Re(s)>1, complete integral and Mobius-index tails"},
            "automatic_winner_native_zeta_audit": winner_native,
            "all_scale_bound_dependencies": {"upper_bound": "elementary rational/positive-series and concavity identities",
                                              "sharpness_only": "Bertrand's postulate"},
            "ordinary_zeta_status": "all-order leading signatures and a pole-regularized RH-equivalent continuation criterion; the required continuation estimate is unproved",
            "main_registry_counts_changed": False, "new_independent_prime_distribution_estimate_proved": False,
            "new_RH_estimate_proved": False, "historical_novelty_established": False,
            "verified_new_operators": []}


def publish(family_directory):
    result = summary(family_directory)
    best = result["automatically_selected_operator"]
    rows = ["left       right      signed weights        sharp composite bound"]
    rows += [f"{r['left']:10} {r['right']:10} {','.join(a[0] for a in r['atoms']):21} {r['composite_absolute_bound']}"
             for r in result["proved_global_estimates"]]
    checks = {k: f"{sum(v.values())}/{len(v)}" for k, v in result["checks"].items()}
    text = f"""SIGNED OPERATOR FAMILY AND AUTOMATIC GLOBAL ESTIMATE CERTIFICATES

Origin: {result['discovery_origin']}.
This is separate from the frozen generic-language independence pilot. The
guided family was supplied earlier; the certificate search records every pair,
freezes its batch before attempts, and chooses no favored parameter.

All-integer theorem: each certified B below has B(p)=1 for every prime and
|B(n)| no greater than its listed bound for EVERY composite n. Coefficient
production uses no prime/factor oracle. Exact polynomial certificates cover
the residual simplexes; a positive-series/Jensen argument closes unbounded
factor-count and exponent tails. Finite observations do not prove those tails.

{chr(10).join(rows)}

Automatic outcomes: {len(result['proved_global_estimates'])} proved estimates,
{len(result['counterexamples'])} rigorous counterexamples, {len(result['numerical_leads'])} retained unproved leads.
Independent exact polynomial certificates: {result['independent_polynomial_certificates_checked']}.
Independent verification: {json.dumps(checks, sort_keys=True)}.
Complete-prefix coefficient checks: {result['arithmetic_coefficient_checks']}.
Automatic best eligible parameters: {None if best is None else [best['left'], best['right']]}.
Automatic best bound: {None if best is None else best['composite_absolute_bound']}.
The selection rule is smallest proved gap with nonzero leading zero signature
at every positive integer order. Unsupported regions remain numerical leads;
failure of a sufficient proof method is not treated as a counterexample.

Complete native-zeta numerical audit parameters:
{json.dumps(result['complete_native_zeta_audit'], indent=2)}
Automatic-winner post-selection numerical audit:
{json.dumps(result['automatic_winner_native_zeta_audit'], indent=2)}
Each numerical check is attributed only to its displayed parameter pair.
The general integral identities have their own written analytic proof.
The post-selection comparison uses overlapping rigorous enclosures with
declared radius caps and disjoint altered-prime controls. It does not require
one enclosure's entire uncertainty to fit inside the other's tail bound.
The first failed strict-gate attempt, its source and diagnostic are preserved
as spent development evidence in selected-native-attempt-001/. The revised
protocol drew fresh cases after retaining that attempt.

The composite upper bounds use elementary identities. Bertrand's postulate
is imported only to prove that each upper bound is a sharp supremum along
actual prime pairs. Prime counts and signed cancellation do not follow from
small individual composite coefficients.

The signed kernel lies outside the previously admitted positive-mixture cone.
Its ingredients are established arithmetic operations. Exact formula
distinction does not establish publication priority. The ordinary-zeta local
zero signature remains present; RH-equivalent continuation is a target, not
a proved estimate. Historical novelty, new independent prime-distribution
information and a new RH bound are unproved. Verified-new list remains empty.

Proofs: compensated_shift_proof.txt, compensated_global_gap_proof.txt,
compensated_family_gap_proof.txt. Audit and dependency hashes are retained in
summary.json and the independent verification artifacts.
Main ten-family/twenty-consequence/150-native-group totals remain separately
scoped. Run the available audits with --compensated-only; regenerating data
requires a fresh frozen family directory.
"""
    (DEST / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
    (DEST / "report.txt").write_text(text)
    (DEST / "latest.json").write_text(json.dumps({"family_run_directory": result["family_run_directory"],
                                                "summary_sha256": digest(result)}, indent=2) + "\n")
    return result


def load_latest():
    path = DEST / "latest.json"
    if not path.exists():
        return {"status": "not_run", "verified_new_operators": []}
    pointer = read(path)
    result = summary(pointer["family_run_directory"])
    require(digest(result) == pointer["summary_sha256"], "published signed-family summary changed")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family-run-dir", type=Path, default=DEST / "family-gap-run-001")
    args = parser.parse_args()
    result = publish(args.family_run_dir)
    print("Published signed family:", len(result["proved_global_estimates"]), "proved bounds,",
          len(result["counterexamples"]), "counterexamples,", len(result["numerical_leads"]), "leads")
