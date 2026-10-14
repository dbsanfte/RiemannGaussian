"""Focused source-free exact-algebra tests for 045 argument construction."""
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import json
import time
import unittest

from floor_residual_drift_arguments_045 import (
    Meter, ROUNDING, build_arguments, enumerate_allocations, instantiate_bound, verify_arguments,
)

METERS = []


def meter(**kwargs):
    value = Meter(**kwargs); METERS.append(value); return value


def request():
    drift = {"kind": "drift_mixture", "a": "3/5", "theta": "1/2",
             "terms": [{"rate": "1", "weight": "2"}, {"rate": "2", "weight": "-1"}]}
    return {"recipe": {"id": "synthetic_moving_profile", "base": drift, "auxiliary": None},
            "q": 3, "b": "1/2", "domain": {"kind": "all_integer", "minimum": 19},
            "rounding": deepcopy(ROUNDING)}


def taper(coord, alpha, gamma):
    return {"kind": "taper", "coordinate": coord, "alpha": alpha, "gamma": gamma}


class ArgumentTests(unittest.TestCase):
    def prove_shape(self, req):
        cert = build_arguments(req, meter=meter())
        result = verify_arguments(req, cert, meter=meter())
        self.assertTrue(result["verified"])
        self.assertFalse(result["uniform_forcing_bound_proved"])
        return cert

    def test_literal_maximal_survival_and_harmonic_constant(self):
        cert = self.prove_shape(request())
        self.assertEqual(cert["profile"]["moments"], ["1", "0", "-2"])
        self.assertEqual(cert["profile"]["laplace_numerator_ascending"], ["2", "0"])
        self.assertEqual(cert["profile"]["laplace_denominator_ascending"], ["2", "3", "1"])
        self.assertTrue(cert["profile"]["raw_survival_range_proved"])
        self.assertEqual(cert["paid_harmonic_scalar"]["constant_H"], "144")
        self.assertEqual(cert["paid_harmonic_scalar"]["asymptotic_energy_rate"], "2")
        level = cert["harmonic_level_envelope"]
        self.assertEqual(level["factorial_depths"], {"harmonic_tail": 3, "cutoff": 2, "rounding": 2})
        self.assertEqual(level["constants"]["local_bias"], "9216/25")
        self.assertEqual(level["constants"]["absolute_harmonic_tail"], "55000/9")
        self.assertEqual(level["constants"]["rounding_harmonic"], "12")
        self.assertEqual(level["scalar_constant"], "1460644/225")
        self.assertFalse(level["fixed_domain_budget_proved"])
        self.assertEqual(cert["leaves"][2]["fixed_A_eta_all_N_budget_status"], "UNPAID_FINITE_HEAD_AND_CONSTANT_MATCH")

    def test_nonmaximal_signed_mixture_keeps_conditional_route(self):
        req = request()
        req["recipe"]["base"]["terms"] = [{"rate": "1", "weight": "1/2"}, {"rate": "2", "weight": "1/2"}]
        cert = self.prove_shape(req)
        self.assertEqual(cert["profile"]["order"], 1)
        self.assertFalse(cert["profile"]["raw_survival_range_proved"])
        self.assertEqual(cert["paid_harmonic_scalar"]["constant_H"], "9")

    def test_complete_scalar_mellin_algebra_with_arbitrary_symbols(self):
        # Toy algebraic source/comparison symbols, NOT values of mu or zeta.
        s, Z, child_s, child_one, parent_s, parent_one = Q(2), Q(7, 3), Q(2, 5), Q(-1, 3), Q(3, 7), Q(1, 9)
        b, qmult, Sc, Sp = Q(-1, 2), Q(1, 9), Q(1000), Q(-2000)
        B = (1-Z*Sc)/s - b*qmult*(1-Z*Sp)/s
        T = -Z*(child_s-Sc)/s + b*qmult*Z*(parent_s-Sp)/s
        H = Z*child_one/s - b*qmult*Z*parent_one/s
        full = (1-b*qmult-Z*(child_s-child_one-b*qmult*(parent_s-parent_one)))/s
        self.assertEqual(B+T+H, full)
        self.assertEqual(full*full, B*B+T*T+H*H+2*(B*T+B*H+T*H))
        self.assertGreater(B*B+T*T+H*H, 1000*full*full)

    def test_cutoff_and_log_rounding_holders(self):
        req = request()
        drift = req["recipe"]["base"]
        req["recipe"]["base"] = {"kind": "product", "left": drift, "right": taper("cutoff", "1/2", "1/3")}
        cert = self.prove_shape(req)
        self.assertEqual(cert["rounding"]["d"], "1/3")
        self.assertEqual(cert["rounding"]["Cround"], "9")
        self.assertEqual(cert["rounding"]["norm_exponent"], "5/3")
        self.assertEqual(cert["paid_harmonic_scalar"]["cutoff_extra"]["constant"], "15")
        req["recipe"]["base"]["right"]["coordinate"] = "log"
        cert = self.prove_shape(req)
        self.assertEqual(cert["rounding"]["d"], "1/6")
        self.assertEqual(cert["rounding"]["Cround"], "12")
        self.assertEqual(cert["paid_harmonic_scalar"]["asymptotic_energy_rate"], None)
        self.assertEqual(cert["leaves"][2]["status"], "OPEN_TAPER_HARMONIC_DISCREPANCY")

    def test_small_outer_powers_do_not_receive_free_norm_decay(self):
        req = request(); drift = req["recipe"]["base"]
        req["recipe"]["base"] = {"kind": "product", "left": taper("log", "1/10", "1/10"), "right": drift}
        cert = self.prove_shape(req)
        self.assertEqual(cert["rounding"]["norm_exponent"], "-23/25")
        self.assertIn("(q+|b|)^2", cert["rounding"]["forcing_error_squared_norm"])
        self.assertTrue(cert["rounding"]["included_inside_discrepancy"])

    def test_exact_young_budget_and_open_leaf_status(self):
        cert = self.prove_shape(request())
        route = instantiate_bound(cert, "2/5", "1", ["1/2", "1/3", "1/6"], meter=meter())
        self.assertEqual([p["energy_upper_constant"] for p in route["premises"]], ["1/10", "2/45", "1/90"])
        self.assertEqual(route["constant_recomposition"], "2/5")
        self.assertTrue(route["harmonic_rate_can_pay_eventually"])
        self.assertTrue(route["eventual_is_not_fixed_domain"])
        self.assertFalse(route["uniform_forcing_bound_proved"])
        self.assertEqual(route["harmonic_explicit_budget_reduction"]["energy_exponent_minus_eta"], "1")
        self.assertTrue(all(p["status"] == "OPEN_ALL_DOMAIN_BUDGET" for p in route["premises"]))
        for alloc in ([], ["1/2", "1/2", "0"], ["1/2", "1/2", "1/2"]):
            with self.assertRaises(ValueError):
                instantiate_bound(cert, "1", "1/2", alloc, meter=meter())

    def test_generic_allocation_enumeration(self):
        allocations = enumerate_allocations(5)
        self.assertIn(["1/3", "1/3", "1/3"], allocations)
        self.assertIn(["1/5", "1/5", "3/5"], allocations)
        self.assertEqual(len(allocations), len({tuple(a) for a in allocations}))
        self.assertTrue(all(sum(Q(x) for x in a) == 1 and all(Q(x) > 0 for x in a) for a in allocations))

    def test_bounded_factorial_depth_does_not_claim_fixed_domain_payment(self):
        req = request(); req["recipe"]["base"]["theta"] = "1/1000"
        cert = self.prove_shape(req)
        self.assertEqual(cert["harmonic_level_envelope"]["status"], "UNSUPPORTED_FACTORIAL_DEPTH")
        self.assertFalse(cert["harmonic_level_envelope"]["fixed_domain_budget_proved"])
        route = instantiate_bound(cert, "1", "1", meter=meter())
        self.assertEqual(route["harmonic_explicit_budget_reduction"], None)
        self.assertFalse(route["uniform_forcing_bound_proved"])

    def test_domain_and_child_parameters_retained(self):
        req = request(); req["domain"]["kind"] = "geometric_chain"
        cert = self.prove_shape(req)
        self.assertEqual(cert["request"]["domain"]["kind"], "geometric_chain")
        self.assertTrue(cert["joint_components"]["bias"]["child_level_beta_cutoff_precision_recomputed"])
        self.assertFalse(cert["proof_guards"]["uniform_RH_or_Mertens_companion_assumed"])

    def test_exact_tampering_rejected(self):
        req = request(); cert = self.prove_shape(req)
        mutants = []
        c = deepcopy(cert); c["profile"]["laplace_numerator_ascending"][0] = "3"; mutants.append(c)
        c = deepcopy(cert); c["profile"]["moments"][1] = "1"; mutants.append(c)
        c = deepcopy(cert); c["paid_harmonic_scalar"]["constant_H"] = "1"; mutants.append(c)
        c = deepcopy(cert); c["uniform_forcing_bound_proved"] = True; mutants.append(c)
        c = deepcopy(cert); c["proof_guards"]["uniform_RH_or_Mertens_companion_assumed"] = True; mutants.append(c)
        c = deepcopy(cert); c["joint_components"]["bias"]["child_level_beta_cutoff_precision_recomputed"] = False; mutants.append(c)
        for mutant in mutants:
            with self.assertRaises(ValueError):
                verify_arguments(req, mutant, meter=meter())

    def test_unsupported_and_strict_source_parameters(self):
        for mutation in ("legacy", "unit", "theta", "aux", "rounding", "boundary", "boolean"):
            req = request()
            if mutation == "legacy": req["recipe"]["base"] = taper("cutoff", "1/2", "1")
            if mutation == "unit": req["recipe"]["base"]["terms"][0]["weight"] = "3"
            if mutation == "theta": req["recipe"]["base"]["theta"] = "1"
            if mutation == "aux": req["recipe"]["auxiliary"] = {}
            if mutation == "rounding": req["rounding"]["drift"] = "round_after_sum"
            if mutation == "boundary": req["q"], req["b"] = 4, "2"
            if mutation == "boolean": req["q"] = True
            cert = build_arguments(req, meter=meter())
            self.assertEqual(cert["status"], "UNSUPPORTED")
            self.assertFalse(cert["uniform_forcing_bound_proved"])
            with self.assertRaises(ValueError):
                verify_arguments(req, cert, meter=meter())

    def test_resource_limits_propagate(self):
        with self.assertRaises(OverflowError): build_arguments(request(), meter=meter(cap=0))
        with self.assertRaises(TimeoutError): build_arguments(request(), meter=meter(seconds=-1))
        req = request(); req["recipe"]["base"]["a"] = str(Q(1, 2**40+1))
        with self.assertRaises(OverflowError): build_arguments(req, meter=meter(max_bits=32))


if __name__ == "__main__":
    path = Path(__file__).with_name("floor_residual_drift_arguments_045_development_receipt.json")
    if path.exists(): raise SystemExit("completed development receipt exists; do not repeat the suite")
    start = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(ArgumentTests))
    receipt = {"module": "test_floor_residual_drift_arguments_045", "tests_run": result.testsRun,
               "failures": len(result.failures), "errors": len(result.errors), "invocations": 1,
               "metered_proxy_operations": sum(m.operations for m in METERS), "elapsed_seconds": time.monotonic()-start,
               "scope": "synthetic exact-algebra ASTs/symbols; no mu/zeta values, norms, selected applications or source sweeps"}
    path.write_text(json.dumps(receipt, indent=2)+"\n")
    print("SYNTHETIC_WORK "+json.dumps(receipt, sort_keys=True))
    raise SystemExit(0 if result.wasSuccessful() else 1)
