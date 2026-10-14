"""Focused synthetic rate-rule tests; no source, zeta values, or norms."""
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import json
import math
import time
import unittest

from floor_residual_global_rate_guard_046 import Meter, REFUTED, ROUNDING, build_guard

METERS = []


def meter(**kwargs):
    result = Meter(**kwargs); METERS.append(result); return result


def request():
    return {"recipe": {"id": "synthetic_bare_profile", "auxiliary": None,
            "base": {"kind": "drift_mixture", "a": "2/5", "theta": "2/3",
                     "terms": [{"rate": "1/2", "weight": "3/2"}, {"rate": "3/2", "weight": "-1/2"}]}},
            "q": 3, "b": "-1/2", "domain": {"kind": "all_integer", "minimum": 23},
            "rounding": deepcopy(ROUNDING), "bound": {"A": "5/7", "eta": "3/4"}}


class RateGuardTests(unittest.TestCase):
    def test_exact_rate_and_tail_gaps(self):
        cert = build_guard(request(), meter=meter())
        self.assertEqual(cert["status"], REFUTED)
        conditions = cert["exact_conditions"]
        self.assertEqual(conditions["tail_dominance_gap_theta_minus_half"], "1/6")
        self.assertEqual(conditions["beta_power"], "1/3")
        self.assertEqual(conditions["rate_gap_eta_minus_beta_power"], "5/12")
        self.assertEqual(conditions["contraction_margin_q_minus_b_squared"], "11/4")
        self.assertEqual(conditions["sum_abs_weights"], "2")
        self.assertEqual(conditions["sum_abs_weighted_rates"], "3/2")
        self.assertEqual(cert["rate_contradiction"]["constant_A_over_a"], "25/14")

    def test_chain_and_all_integer_domains_bind_full_payload(self):
        req = request(); req["domain"]["kind"] = "geometric_chain"
        cert = build_guard(req, meter=meter())
        self.assertEqual(cert["status"], REFUTED)
        self.assertEqual(cert["request"], req)
        self.assertEqual(cert["rate_contradiction"]["uniform_domain_refuted"], req["domain"])
        req["recipe"]["id"] = "later_mutation"
        self.assertEqual(cert["request"]["recipe"]["id"], "synthetic_bare_profile")

    def test_exact_equality_and_slower_rates_stay_open(self):
        for eta in ("1/3", "1/4"):
            req = request(); req["bound"]["eta"] = eta
            cert = build_guard(req, meter=meter())
            self.assertEqual(cert["status"], "UNSUPPORTED")
            self.assertFalse(cert["advertised_uniform_rate_refuted"])
            self.assertEqual(cert["unpaid_rate_status"], "OPEN")

    def test_tail_threshold_half_and_lower_theta_stay_open(self):
        for theta in ("1/2", "1/3", "1", "0"):
            req = request(); req["recipe"]["base"]["theta"] = theta
            cert = build_guard(req, meter=meter())
            self.assertEqual(cert["status"], "UNSUPPORTED")
            self.assertEqual(cert["norm_convergence_status"], "OPEN")
            self.assertEqual(cert["RH_status"], "OPEN")

    def test_boundary_layer_is_not_removed_by_high_moment_order(self):
        # Literal rational identity F_1(z)=1-z*sum w/(r+z).
        # This is a toy algebraic z, not an evaluated zeta zero/frequency.
        rates = list(range(1, 5))
        weights = [Q((-1)**(j+1)*math.comb(4, j)) for j in rates]
        self.assertEqual(sum(weights), 1)
        self.assertTrue(all(sum(w*r**k for r, w in zip(rates, weights)) == 0 for k in range(1, 4)))
        for z in (Q(0), Q(1, 7), Q(2)):
            F = 1-z*sum(w/(r+z) for r, w in zip(rates, weights))
            self.assertEqual(F, Q(24)/math.prod(z+r for r in rates))
        for d in (1, 2, 5):
            self.assertEqual(1-Q(0)**d*sum(w/Q(r)**d for r, w in zip(rates, weights)), 1)
        req = request()
        req["recipe"]["base"]["terms"] = [{"rate": str(r), "weight": str(w)} for r, w in zip(rates, weights)]
        cert = build_guard(req, meter=meter())
        self.assertEqual(cert["status"], REFUTED)
        self.assertFalse(cert["proof_guards"]["moment_cancellation_required_for_lower_rate"])
        self.assertFalse(cert["RH_true_branch"]["zero_simplicity_assumed"])

    def test_signed_and_single_profiles_and_any_finite_A(self):
        req = request()
        req["recipe"]["base"]["terms"] = [{"rate": "7/5", "weight": "1"}]
        req["bound"]["A"] = "1000000000"
        cert = build_guard(req, meter=meter())
        self.assertEqual(cert["status"], REFUTED)
        self.assertEqual(cert["exact_conditions"]["rmin"], "7/5")
        self.assertFalse(cert["numerical_lower_constant_claimed"])
        self.assertFalse(cert["explicit_failing_support_claimed"])

    def test_bare_source_and_rounding_scope(self):
        for mutation in ("product", "aux", "rounding", "source", "unit"):
            req = request()
            if mutation == "product":
                req["recipe"]["base"] = {"kind": "product", "left": req["recipe"]["base"], "right": {"kind": "unit"}}
            if mutation == "aux": req["recipe"]["auxiliary"] = {"channel": "mu_convolution_mu"}
            if mutation == "rounding": req["rounding"]["drift"] = "round_after_sum"
            if mutation == "source": req["recipe"]["base"]["source"] = "arbitrary_signs"
            if mutation == "unit": req["recipe"]["base"]["terms"][0]["weight"] = "2"
            self.assertEqual(build_guard(req, meter=meter())["status"], "UNSUPPORTED")

    def test_stable_multiplier_domain_and_strict_types(self):
        req = request(); req["q"], req["b"] = 4, "2"
        self.assertEqual(build_guard(req, meter=meter())["status"], "UNSUPPORTED")
        req["b"] = "3/2"
        cert = build_guard(req, meter=meter())
        self.assertEqual(cert["exact_conditions"]["contraction_margin_q_minus_b_squared"], "7/4")
        self.assertEqual(cert["beta_transfer"]["child_level_gap_upper_bound"], 2)
        for key, value in (("q", True), ("b", "-2/4")):
            changed = request(); changed[key] = value
            self.assertEqual(build_guard(changed, meter=meter())["status"], "UNSUPPORTED")
        req = request(); req["domain"]["kind"] = "arbitrary_finite_list"
        self.assertEqual(build_guard(req, meter=meter())["status"], "UNSUPPORTED")

    def test_complete_local_scope_and_imports_explicit(self):
        cert = build_guard(request(), meter=meter())
        self.assertIn("A_(qN)(1)", cert["whole_mellin"]["forcing"])
        self.assertTrue(cert["whole_mellin"]["indicator_and_signed_parent_child_terms_retained"])
        self.assertTrue(cert["RH_true_branch"]["all_crosses_retained"])
        self.assertEqual(cert["RH_true_branch"]["imported_theorem"]["hypothesis"], "RH")
        self.assertFalse(cert["proof_guards"]["global_truncation_energy_paid"])
        self.assertFalse(cert["source_values_evaluated"])
        self.assertFalse(cert["RH_proved"])
        self.assertFalse(cert["RH_refuted"])
        self.assertEqual(cert["norm_convergence_status"], "OPEN")

    def test_resource_failures_are_not_refutation_certificates(self):
        with self.assertRaises(OverflowError): build_guard(request(), meter=meter(cap=0))
        with self.assertRaises(TimeoutError): build_guard(request(), meter=meter(seconds=-1))
        req = request(); req["recipe"]["base"]["a"] = str(Q(1, 2**40+1))
        with self.assertRaises(OverflowError): build_guard(req, meter=meter(max_bits=32))


if __name__ == "__main__":
    path = Path(__file__).with_name("floor_residual_global_rate_guard_046_development_receipt.json")
    if path.exists(): raise SystemExit("completed receipt exists; do not repeat the suite")
    start = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(RateGuardTests))
    receipt = {"module": "test_floor_residual_global_rate_guard_046", "tests_run": result.testsRun,
               "failures": len(result.failures), "errors": len(result.errors), "invocations": 1,
               "metered_proxy_operations": sum(m.operations for m in METERS), "elapsed_seconds": time.monotonic()-start,
               "scope": "synthetic ASTs and rational boundary-layer algebra; no actual source/norm/selected applications"}
    path.write_text(json.dumps(receipt, indent=2)+"\n")
    print("SYNTHETIC_WORK "+json.dumps(receipt, sort_keys=True))
    raise SystemExit(0 if result.wasSuccessful() else 1)
