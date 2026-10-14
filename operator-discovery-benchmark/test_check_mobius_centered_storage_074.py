"""New physical-coefficient grammar tests; no source datasets or scoring."""
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import sys
import time
import unittest

from check_mobius_centered_storage_074 import verify_grammar


ALL_OPERATIONS = 0


def candidate(theta=None, rays=None, q="1"):
    theta = ["1/3", "1/2", "2/3", "4/5"] if theta is None else theta
    return {"schema": "signed-prime-storage-candidate-v1",
        "spec": {"profile": [["8", "10", "1"], ["16", "20", "-1"]], "theta": theta},
        "labels": ["Z", "unit", "omega1", "omega2", "omega3", "omega_ge4"] +
                  ["smooth:" + str(t) for t in theta],
        "q": q, "precision": 12, "rays": [] if rays is None else rays,
        "C": "0", "base_upper": "0", "training_scales": [], "training_upper": "0",
        "uniform_domination_proved": True, "uniform_recurrence_proved": False,
        "uniform_head_bound_proved": False, "RH_proved": False, "search_metadata": {}}


def ray(smooth=None, factors=None, Z="0", unit="0", weight="1"):
    smooth = ["0", "0", "1/4", "-1/4"] if smooth is None else smooth
    factors = ["0"] * 4 if factors is None else factors
    return {"weight": weight, "direction": [Z, unit] + factors + smooth}


class SyntheticGrammarTests(unittest.TestCase):
    def check(self, cert, branch):
        global ALL_OPERATIONS
        result = verify_grammar(cert, branch)
        ALL_OPERATIONS += result["operations"]
        return result

    def assertAdmitted(self, cert, branch):
        result = self.check(cert, branch)
        self.assertTrue(result["verified"], result)
        self.assertEqual(result["status"], "NECESSARY_GRAMMAR_ADMITTED")
        self.assertTrue(result["necessary_filter_only"])
        self.assertTrue(result["ordinary_073_admission_required"])
        self.assertTrue(result["uniform_control_remains_open"])
        for flag in ["uniform_recurrence_proved", "uniform_head_bound_proved", "RH_proved"]:
            self.assertIs(result[flag], False)
        self.assertNotIn("uniform_domination_proved", result)
        return result

    def assertRejected(self, cert, branch):
        result = self.check(cert, branch)
        self.assertFalse(result["verified"], result)
        self.assertEqual(result["status"], "GRAMMAR_REJECTED")
        return result

    def test_empty_rays_baseline_both_branches(self):
        for branch in ["centered_high", "open_mixed"]:
            result = self.assertAdmitted(candidate(), branch)
            self.assertEqual(result["rays_checked"], 0)

    def test_centered_high_exact_balanced_arbitrary_rationals(self):
        cert = candidate(rays=[ray(factors=["-7/19"]*4, Z="11/23", unit="-2/17", weight="5/31")])
        self.assertAdmitted(cert, "centered_high")
        self.assertAdmitted(cert, "open_mixed")

    def test_open_unknown_mixture_keeps_nonzero_known_sum(self):
        cert = candidate(rays=[ray(smooth=["1/17", "0", "2/19", "3/23"])])
        result = self.assertAdmitted(cert, "open_mixed")
        self.assertEqual(result["unknown_mixture_rays"], [0])
        self.assertEqual(result["ray_checks"][0]["unknown_nonzero_labels"], ["smooth:1/3"])
        self.assertNotEqual(result["ray_checks"][0]["registered_smooth_sum"], "0")
        self.assertRejected(cert, "centered_high")

    def test_unknown_only_direction_is_retained_open(self):
        cert = candidate(rays=[ray(smooth=["-1/97", "0", "0", "0"])])
        self.assertAdmitted(cert, "open_mixed")
        self.assertRejected(cert, "centered_high")

    def test_known_pure_high_bulk_rejected_in_both_branches(self):
        cert = candidate(rays=[ray(smooth=["0", "0", "1/4", "-1/8"])])
        for branch in ["centered_high", "open_mixed"]:
            self.assertRejected(cert, branch)

    def test_half_boundary_registered_in_both_branches(self):
        cert = candidate(rays=[ray(smooth=["0", "1", "0", "0"])])
        for branch in ["centered_high", "open_mixed"]:
            result = self.assertRejected(cert, branch)
            self.assertEqual(result["ray_checks"][0]["unknown_nonzero_labels"], [])
        cert = candidate(rays=[ray(smooth=["0", "1/7", "-1/7", "0"])])
        self.assertAdmitted(cert, "centered_high")
        self.assertAdmitted(cert, "open_mixed")

    def test_unknown_mixture_may_cancel_known_boundary(self):
        cert = candidate(rays=[ray(smooth=["1/13", "-1/13", "0", "0"])])
        self.assertAdmitted(cert, "open_mixed")
        self.assertRejected(cert, "centered_high")

    def test_factor_balance_checked_even_for_unknown_mixture(self):
        for index in range(4):
            factors = ["1/5"] * 4
            factors[index] = "2/5"
            cert = candidate(rays=[ray(smooth=["1", "0", "0", "0"], factors=factors)])
            for branch in ["centered_high", "open_mixed"]:
                result = self.assertRejected(cert, branch)
                self.assertIn("unbalanced_factor_sector_bulk", result["violations"][0]["reasons"])

    def test_factor_balance_checked_for_centered_high(self):
        cert = candidate(rays=[ray(factors=["1", "1", "2", "1"])])
        self.assertRejected(cert, "centered_high")

    def test_per_ray_bulk_cannot_cancel_across_positive_squares(self):
        cert = candidate(rays=[ray(smooth=["0", "0", "1", "0"]),
                               ray(smooth=["0", "0", "-1", "0"])])
        for branch in ["centered_high", "open_mixed"]:
            result = self.assertRejected(cert, branch)
            self.assertEqual([r["ray"] for r in result["violations"]], [0, 1])

    def test_unknown_permission_is_per_ray(self):
        cert = candidate(rays=[ray(smooth=["1", "0", "1", "0"]),
                               ray(smooth=["0", "0", "1", "0"])])
        result = self.assertRejected(cert, "open_mixed")
        self.assertTrue(result["ray_checks"][0]["admitted"])
        self.assertFalse(result["ray_checks"][1]["admitted"])
        self.assertEqual(result["unknown_mixture_rays"], [0])

    def test_exact_arbitrary_denominator_cancellation(self):
        a, b = Fraction(1, 17), Fraction(-1, 19)
        cert = candidate(rays=[ray(smooth=["0", str(a), str(b), str(-a-b)])])
        result = self.assertAdmitted(cert, "centered_high")
        self.assertEqual(result["ray_checks"][0]["registered_smooth_sum"], "0")

    def test_tiny_nonzero_unknown_is_not_rounded_away(self):
        cert = candidate(rays=[ray(smooth=["1/100000000000000000000000000000000000039", "0", "1", "0"])])
        self.assertAdmitted(cert, "open_mixed")
        self.assertRejected(cert, "centered_high")

    def test_tiny_nonzero_known_sum_is_rejected(self):
        cert = candidate(rays=[ray(smooth=["0", "0", "1", "-100000000000000000000/100000000000000000001"])])
        for branch in ["centered_high", "open_mixed"]:
            self.assertRejected(cert, branch)

    def test_strict_below_half_classification_uses_integer_rationals(self):
        denominator = 2 * 10**70 + 1
        theta = [str(Fraction(10**70, denominator)), "1/2", "2/3"]
        cert = candidate(theta=theta, rays=[ray(smooth=["1", "0", "1"])])
        result = self.assertAdmitted(cert, "open_mixed")
        self.assertEqual(result["ray_checks"][0]["unknown_nonzero_labels"], ["smooth:" + theta[0]])
        self.assertRejected(cert, "centered_high")

    def test_q2_and_out_of_range_rejected(self):
        for q in ["2", "3/4", "0", "-1", "129/64"]:
            for branch in ["centered_high", "open_mixed"]:
                self.assertRejected(candidate(q=q), branch)

    def test_fixed_q1_and_loss65over64_and_arbitrary_denominator_admitted(self):
        for q in ["1", "65/64", "33/17", "199999999999999999999/100000000000000000000"]:
            self.assertAdmitted(candidate(q=q), "centered_high")

    def test_fixed_original_source_binding(self):
        wrong_profiles = [[['8', '10', '1'], ['16', '20', '1']],
                          [['8', '10', '1'], ['16', '21', '-1']],
                          [['8', '10', '2'], ['16', '20', '-2']],
                          [['16', '20', '-1'], ['8', '10', '1']],
                          [['8/1', '10', '1'], ['16', '20', '-1']]]
        for profile in wrong_profiles:
            cert = candidate()
            cert["spec"]["profile"] = profile
            self.assertRejected(cert, "centered_high")

    def test_complete_label_order_and_binding(self):
        cert = candidate()
        for labels in [cert["labels"][:-1], cert["labels"] + ["extra"],
                       ["unit", "Z"] + cert["labels"][2:]]:
            wrong = deepcopy(cert)
            wrong["labels"] = labels
            self.assertRejected(wrong, "open_mixed")
        cert["labels"][7] = "smooth:2/4"
        self.assertRejected(cert, "open_mixed")

    def test_theta_sorted_finite_canonical_and_open_interval(self):
        for theta in [["1/2", "1/3"], ["1/2", "1/2"], ["0"], ["1"],
                      ["2/4"], [0.5], "1/2"]:
            self.assertRejected(candidate(theta=theta), "centered_high")

    def test_no_smooth_coordinates_and_general_balanced_sector_ray(self):
        cert = candidate(theta=[], rays=[ray(smooth=[], factors=["-13/17"]*4,
                                           Z="19/23", unit="100/29")])
        for branch in ["centered_high", "open_mixed"]:
            self.assertAdmitted(cert, branch)

    def test_zero_direction_positive_weight_admitted(self):
        cert = candidate(rays=[ray(smooth=["0"]*4, weight="3/7")])
        self.assertAdmitted(cert, "centered_high")

    def test_zero_and_negative_weights_must_be_omitted(self):
        for weight in ["0", "-1/17"]:
            self.assertRejected(candidate(rays=[ray(weight=weight)]), "open_mixed")

    def test_full_ray_dimension_and_exact_ray_keys(self):
        for direction in [["0"]*9, ["0"]*11, tuple(["0"]*10)]:
            cert = candidate(rays=[{"weight": "1", "direction": direction}])
            self.assertRejected(cert, "centered_high")
        cert = candidate(rays=[ray()])
        cert["rays"][0]["claimed_centered"] = True
        self.assertRejected(cert, "centered_high")

    def test_rational_format_and_float_tampering(self):
        for value in ["+1", "01", "1/1", "-0", "2/4", "1/0", " 0", 0.0, True]:
            cert = candidate(rays=[ray()])
            cert["rays"][0]["direction"][0] = value
            self.assertRejected(cert, "open_mixed")

    def test_search_metadata_never_overrides_physical_coefficients(self):
        cert = candidate(rays=[ray(smooth=["0", "0", "1", "0"])])
        cert["search_metadata"] = {"branch": "centered_high", "centered": True,
            "factor_balance_verified": True, "smooth_sum": "0", "RH_proved": True}
        self.assertRejected(cert, "centered_high")
        cert["rays"] = [ray(smooth=["1", "0", "1", "0"])]
        self.assertAdmitted(cert, "open_mixed")

    def test_explicit_branch_isolation(self):
        cert = candidate(rays=[ray(smooth=["1", "0", "0", "0"])])
        cert["search_metadata"]["branch"] = "centered_high"
        self.assertAdmitted(cert, "open_mixed")
        cert["search_metadata"]["branch"] = "open_mixed"
        self.assertRejected(cert, "centered_high")

    def test_unknown_branch_rejected(self):
        for branch in ["mixed", "", None, True, ["open_mixed"]]:
            self.assertRejected(candidate(), branch)

    def test_no_false_proof_scope_declarations(self):
        for flag in ["uniform_recurrence_proved", "uniform_head_bound_proved", "RH_proved"]:
            for bad in [True, 0, "false"]:
                cert = candidate()
                cert[flag] = bad
                result = self.assertRejected(cert, "open_mixed")
                for out_flag in ["uniform_recurrence_proved", "uniform_head_bound_proved", "RH_proved"]:
                    self.assertIs(result[out_flag], False)

    def test_domination_declaration_not_certified_by_grammar(self):
        cert = candidate()
        cert["uniform_domination_proved"] = False
        self.assertRejected(cert, "centered_high")
        self.assertAdmitted(candidate(), "centered_high")

    def test_finite_arithmetic_is_explicitly_delegated(self):
        cert = candidate(rays=[ray()])
        cert["precision"] = 0
        cert["C"] = "-1"
        cert["base_upper"] = "unverified"
        cert["training_scales"] = [True]
        result = self.assertAdmitted(cert, "centered_high")
        self.assertTrue(result["ordinary_073_admission_required"])

    def test_input_bit_boundary_and_resource_rejection(self):
        number = str(1 << 4095)
        cert = candidate(rays=[ray(smooth=["0", "0", number, "-" + number])])
        self.assertAdmitted(cert, "centered_high")
        cert["rays"][0]["direction"][8] = str(1 << 4096)
        result = self.assertRejected(cert, "centered_high")
        self.assertEqual(result["error_type"], "ResourceLimit")

    def test_at_most256_positive_rays(self):
        self.assertAdmitted(candidate(rays=[ray() for _ in range(256)]), "centered_high")
        self.assertRejected(candidate(rays=[ray() for _ in range(257)]), "centered_high")

    def test_candidate_keys_and_schema_not_metadata_aliases(self):
        cert = candidate()
        cert["schema"] = "centered-storage-claimed"
        self.assertRejected(cert, "centered_high")
        cert = candidate()
        cert["branch"] = "centered_high"
        self.assertRejected(cert, "centered_high")

    def test_verification_does_not_mutate_candidate(self):
        cert = candidate(rays=[ray(smooth=["1/7", "0", "1/11", "2/13"])])
        before = deepcopy(cert)
        self.assertAdmitted(cert, "open_mixed")
        self.assertRejected(cert, "centered_high")
        self.assertEqual(cert, before)


def run_and_record():
    suite = (unittest.defaultTestLoader.loadTestsFromNames(sys.argv[1:], sys.modules[__name__])
             if len(sys.argv) > 1 else
             unittest.defaultTestLoader.loadTestsFromTestCase(SyntheticGrammarTests))
    def test_names(items):
        names = []
        for item in items:
            names.extend(test_names(item) if isinstance(item, unittest.TestSuite) else [item.id()])
        return names
    names = test_names(suite)
    start = time.perf_counter()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    elapsed = time.perf_counter() - start
    path = Path(__file__).with_name("mobius_centered_storage_checker_074_development.json")
    receipt = json.loads(path.read_text()) if path.exists() else {
        "schema": "independent-grammar-checker-development-074-v1", "runs": []}
    receipt["runs"].append({"tests": len(names), "test_names": names,
        "operations": ALL_OPERATIONS, "elapsed_seconds": elapsed,
        "returncode": 0 if result.wasSuccessful() else 1,
        "failures": [{"test": t.id(), "traceback": trace} for t, trace in result.failures],
        "errors": [{"test": t.id(), "traceback": trace} for t, trace in result.errors]})
    receipt["unique_new_synthetic_tests"] = len({name for r in receipt["runs"] for name in r["test_names"]})
    latest = {}
    for run in receipt["runs"]:
        failed = {entry["test"] for kind in ("failures", "errors") for entry in run[kind]}
        for name in run["test_names"]:
            latest[name] = name not in failed
    receipt["unresolved_test_failures"] = sorted(name for name, passed in latest.items() if not passed)
    receipt["final_status"] = "PASS" if all(latest.values()) else "FAIL"
    receipt["scientific_data_or_outcomes_read"] = False
    receipt["independent_of_producer_learner_and_feedback_analyzer"] = True
    path.write_text(json.dumps(receipt, indent=2) + "\n")
    raise SystemExit(0 if result.wasSuccessful() else 1)


if __name__ == "__main__":
    run_and_record()
