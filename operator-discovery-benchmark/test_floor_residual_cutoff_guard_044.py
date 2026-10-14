"""Focused toy-only guard regressions. No arithmetic source or norm evaluation."""
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import json
import time
import unittest

from floor_residual_cutoff_guard_044 import (
    Meter, REFUTED, ResourceLimit, ROUNDING, UNSUPPORTED, build_guard, verify_guard,
)


METERS = []


def meter(**kwargs):
    out = Meter(**kwargs)
    METERS.append(out)
    return out


def power(alpha):
    return {"kind": "taper", "coordinate": "cutoff", "alpha": alpha, "gamma": "1"}


def request(mixed=False):
    recipe = {"id": "synthetic_toy", "base": power("1/2"), "auxiliary": None}
    if mixed:
        recipe["auxiliary"] = {"channel": "mu", "coefficient": "1/3",
            "envelope": {"kind": "difference", "left": power("1/2"), "right": power("3/4")}}
    return {"recipe": recipe, "q": 3, "b": "-1", "domain": {"kind": "all_integer", "minimum": 17},
            "rounding": deepcopy(ROUNDING)}


class GuardTests(unittest.TestCase):
    def prove(self, req):
        cert = build_guard(req, meter=meter())
        result = verify_guard(req, cert, meter=meter())
        self.assertTrue(result["verified"])
        self.assertEqual(result["status"], REFUTED)
        self.assertEqual(result["individual_geometric_subsequence_status"], "OPEN")
        return cert

    def test_literal_single_power_kernel(self):
        cert = self.prove(request())
        self.assertEqual(cert["mellin_kernel"]["numerator"], ["1/2"])
        self.assertEqual(cert["mellin_kernel"]["denominator"], ["0", "1/2", "1"])
        self.assertEqual(cert["contraction_margin_q_minus_b_squared"], "2")

    def test_literal_convex_mixture_and_transfer(self):
        cert = self.prove(request(True))
        self.assertEqual(cert["mixture"], [{"alpha": "1/2", "weight": "2/3"},
                                            {"alpha": "3/4", "weight": "1/3"}])
        self.assertEqual(cert["mellin_kernel"]["numerator"], ["3/8", "7/12"])
        self.assertEqual(cert["mellin_kernel"]["denominator"], ["0", "3/8", "5/4", "1"])
        self.assertEqual(cert["integer_real_transfer"]["weighted_sum_lipschitz_constant"], "7/12")
        self.assertEqual(cert["integer_real_transfer"]["scale_difference_lipschitz_constant"], "7/3")

    def test_generic_signed_ast_normalization(self):
        req = request(True)
        aux = req["recipe"]["auxiliary"]
        aux["coefficient"] = "-1/3"
        aux["envelope"]["left"], aux["envelope"]["right"] = aux["envelope"]["right"], aux["envelope"]["left"]
        cert = self.prove(req)
        self.assertEqual(cert["mixture"][0]["weight"], "2/3")

    def test_duplicate_power_exact_cancellation(self):
        req = request(True)
        aux = req["recipe"]["auxiliary"]
        aux["coefficient"] = "7"
        aux["envelope"]["right"] = power("1/2")
        cert = self.prove(req)
        self.assertEqual(cert["mixture"], [{"alpha": "1/2", "weight": "1"}])
        self.assertEqual(cert["rounding"]["constant_T_absolute_error_bound"], "N^-3")

    def test_nonconvex_is_unsupported_not_a_refutation(self):
        req = request(True)
        req["recipe"]["auxiliary"]["coefficient"] = "2"
        cert = build_guard(req, meter=meter())
        self.assertEqual(cert["status"], UNSUPPORTED)
        self.assertFalse(cert["uniform_vanishing_forcing_impossible"])
        with self.assertRaises(ValueError):
            verify_guard(req, cert, meter=meter())

    def test_unsupported_source_coordinate_outer_power(self):
        for path, value in [("channel", "liouville"), ("coordinate", "log"), ("gamma", "1/2")]:
            req = request(True)
            if path == "channel":
                req["recipe"]["auxiliary"][path] = value
            else:
                req["recipe"]["base"][path] = value
            cert = build_guard(req, meter=meter())
            self.assertEqual(cert["status"], UNSUPPORTED)

    def test_geometric_domain_does_not_inherit_proof(self):
        req = request()
        cert = self.prove(req)
        req["domain"]["kind"] = "geometric_subsequence"
        result = build_guard(req, meter=meter())
        self.assertEqual(result["status"], UNSUPPORTED)
        self.assertEqual(result["individual_geometric_subsequence_status"], "OPEN")
        with self.assertRaises(ValueError):
            verify_guard(req, cert, meter=meter())

    def test_exact_strict_boundary_and_rounding_policy(self):
        req = request()
        req["q"], req["b"] = 4, "2"
        self.assertEqual(build_guard(req, meter=meter())["status"], UNSUPPORTED)
        req["b"] = "3/2"
        self.prove(req)
        req["rounding"]["bits_multiplier"] = 3
        self.assertEqual(build_guard(req, meter=meter())["status"], UNSUPPORTED)

    def test_tampered_exact_kernel_and_proof_flags(self):
        req = request(True)
        cert = self.prove(req)
        mutants = []
        altered = deepcopy(cert); altered["mellin_kernel"]["numerator"][0] = "1"; mutants.append(altered)
        altered = deepcopy(cert); altered["mellin_kernel"]["denominator"][1] = "1"; mutants.append(altered)
        altered = deepcopy(cert); altered["mixture"][0]["weight"] = "1"; mutants.append(altered)
        altered = deepcopy(cert); altered["claims_RH"] = True; mutants.append(altered)
        altered = deepcopy(cert); altered["individual_geometric_subsequence_status"] = "REFUTED"; mutants.append(altered)
        altered = deepcopy(cert); altered["integer_real_transfer"]["weighted_sum_lipschitz_constant"] = "0"; mutants.append(altered)
        altered = deepcopy(cert); altered["uniform_vanishing_forcing_impossible"] = 1; mutants.append(altered)
        for mutant in mutants:
            with self.assertRaises(ValueError):
                verify_guard(req, mutant, meter=meter())

    def test_full_payload_identity_and_strict_parameters(self):
        req = request(); cert = self.prove(req)
        req["recipe"]["id"] = "different_ordinal"
        with self.assertRaises(ValueError):
            verify_guard(req, cert, meter=meter())
        for key, value in [("q", True), ("b", "-2/2")]:
            changed = request(); changed[key] = value
            self.assertEqual(build_guard(changed, meter=meter())["status"], UNSUPPORTED)

    def test_resource_failures_propagate_without_proof(self):
        with self.assertRaises(ResourceLimit):
            build_guard(request(), meter=meter(max_operations=0))
        with self.assertRaises(ResourceLimit):
            build_guard(request(), meter=meter(seconds=-1))
        req = request(); req["recipe"]["base"]["alpha"] = str(Q(1, 2**40+1))
        with self.assertRaises(ResourceLimit):
            build_guard(req, meter=meter(max_bits=32))


if __name__ == "__main__":
    receipt_path = Path(__file__).with_name("floor_residual_cutoff_guard_044_development_receipt.json")
    if receipt_path.exists():
        raise SystemExit("development receipt already exists; do not repeat the completed suite")
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(GuardTests))
    receipt = {"module": "test_floor_residual_cutoff_guard_044", "tests_run": result.testsRun,
               "failures": len(result.failures), "errors": len(result.errors),
               "metered_proxy_operations": sum(m.operations for m in METERS),
               "elapsed_seconds": time.monotonic()-started, "invocations": 1,
               "scope": "synthetic ASTs only; no actual selected applications, source tables, or norms"}
    receipt_path.write_text(json.dumps(receipt, indent=2)+"\n")
    print("SYNTHETIC_WORK "+json.dumps(receipt, sort_keys=True))
    raise SystemExit(0 if result.wasSuccessful() else 1)
