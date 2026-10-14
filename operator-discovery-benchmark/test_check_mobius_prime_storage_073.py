"""New synthetic tests only; no scientific datasets or candidate outcomes read."""
from copy import deepcopy
from fractions import Fraction
from math import gcd
import json
from pathlib import Path
import time
import unittest

import check_mobius_prime_storage_073 as checker


ALL_OPERATIONS = 0


def trial_factors(n):
    """Tiny trial-division oracle, independent of the checker's factor sieve."""
    if n == 1:
        return 1, 0, 1
    sign, count, largest, p = 1, 0, 1, 2
    while p * p <= n:
        if n % p == 0:
            count += 1
            largest = p
            n //= p
            if n % p == 0:
                return 0, -1, -1
            sign = -sign
        p += 1
    if n > 1:
        count += 1
        largest = n
        sign = -sign
    return sign, count, largest


def naive_data(scales, profile=None, theta=None):
    profile = profile if profile is not None else [["0", "1", "1"]]
    theta = theta if theta is not None else ["1/2", "2/3"]
    denominator = 1
    for _, _, weight in profile:
        d = Fraction(weight).denominator
        denominator = denominator // gcd(denominator, d) * d
    labels = ["Z", "unit", "omega1", "omega2", "omega3", "omega_ge4"] + ["smooth:" + t for t in theta]
    rows = []
    for k in scales:
        X = Fraction(profile[-1][1]) * k
        X = X.numerator // X.denominator
        cuts = []
        for text in theta:
            exponent = Fraction(text)
            target = X ** exponent.numerator
            cut = 1
            while (cut + 1) ** exponent.denominator <= target:
                cut += 1
            cuts.append(cut)
        state = [0] * len(labels)
        for n in range(1, X + 1):
            weight = sum((Fraction(w) for lo, hi, w in profile
                          if Fraction(lo) * k < n <= Fraction(hi) * k), Fraction(0))
            if not weight:
                continue
            mu, omega, largest = trial_factors(n)
            if not mu:
                continue
            contribution = int(denominator * weight) * mu
            state[0] += contribution
            state[min(omega, 4) + 1] += contribution
            for j, cut in enumerate(cuts):
                if largest <= cut:
                    state[j + 6] += contribution
        rows.append({"k": k, "X": X, "cuts": cuts, "state": state})
    return {"schema": "signed-prime-storage-data-v1", "spec": {"profile": profile, "theta": theta},
            "labels": labels, "denominator": denominator, "rows": rows, "operations": 0}


def simple_candidate(data, q="1", precision=8, rays=None, C="1000", scales=None):
    rays = [] if rays is None else rays
    denominator = data["denominator"]
    base_row = next(x for x in data["rows"] if x["k"] == 1)
    state = [Fraction(x, denominator) for x in base_row["state"]]
    base = state[0]**2
    for ray in rays:
        dot = sum((Fraction(x) * y for x, y in zip(ray["direction"], state)), Fraction(0))
        base += Fraction(ray["weight"]) * dot**2
    return {"schema": "signed-prime-storage-candidate-v1", "spec": deepcopy(data["spec"]),
            "labels": list(data["labels"]), "q": q, "precision": precision, "rays": rays,
            "C": C, "base_upper": str(base), "training_scales": [] if scales is None else scales,
            "training_upper": "0", "uniform_domination_proved": True,
            "uniform_recurrence_proved": False, "uniform_head_bound_proved": False,
            "RH_proved": False, "search_metadata": {"synthetic": True}}


def exact_energy(row, data, candidate):
    state = [Fraction(x, data["denominator"]) for x in row["state"]]
    return state[0]**2 + sum((Fraction(r["weight"]) *
        sum((Fraction(a)*b for a, b in zip(r["direction"], state)), Fraction(0))**2
        for r in candidate["rays"]), Fraction(0))


class SyntheticCheckerTests(unittest.TestCase):
    def setUp(self):
        self.meter = checker.Meter(limit=500000000)

    def tearDown(self):
        global ALL_OPERATIONS
        ALL_OPERATIONS += self.meter.ops

    def admit(self, data):
        return checker.verify_data(data, self.meter)

    def verify(self, candidate, data):
        return checker.verify_candidate(candidate, data, self.meter)

    def evaluate(self, candidate, data, scales=None):
        return checker.evaluate_candidate(candidate, data, self.meter, scales)

    def assertRejected(self, data):
        self.assertFalse(self.admit(data)["verified"])

    def test_signed_rational_multiband_source_trial_oracle(self):
        data = naive_data(list(range(1, 85)), [["0", "3/2", "-2/3"], ["2", "4", "5/7"]],
                          ["1/3", "1/2", "3/4"])
        self.assertTrue(self.admit(data)["verified"])
        self.assertEqual(data["denominator"], 21)

    def test_all_factor_sectors_including_four_prime_product(self):
        data = naive_data([1, 2, 6, 30, 210], theta=["1/4", "1/2", "3/4"])
        self.assertNotEqual(data["rows"][-1]["state"][5], 0)
        self.assertTrue(self.admit(data)["verified"])

    def test_empty_smooth_coordinate_list(self):
        self.assertTrue(self.admit(naive_data([1, 2, 5, 31], theta=[]))["verified"])

    def test_unit_only_exact_cut_equality(self):
        data = naive_data([1], theta=["1/3", "1/2", "2/3"])
        self.assertEqual(data["rows"][0]["state"], [1, 1, 0, 0, 0, 0, 1, 1, 1])
        self.assertTrue(self.admit(data)["verified"])

    def test_lower_open_upper_closed_profile_boundaries(self):
        data = naive_data([1, 2, 3], [["1", "2", "1"], ["2", "3", "-1"]])
        self.assertTrue(self.admit(data)["verified"])
        data["rows"][0]["state"][1] = 1
        data["rows"][0]["state"][0] += 1
        self.assertRejected(data)

    def test_prime_sign_tamper_preserving_sector_sum(self):
        data = naive_data([1, 2, 3])
        data["rows"][2]["state"][2] *= -1
        data["rows"][2]["state"][0] = sum(data["rows"][2]["state"][1:6])
        self.assertRejected(data)

    def test_composite_sign_tamper_preserving_sector_sum(self):
        data = naive_data([1, 6])
        data["rows"][1]["state"][3] *= -1
        data["rows"][1]["state"][0] = sum(data["rows"][1]["state"][1:6])
        self.assertRejected(data)

    def test_squareful_terms_are_zero(self):
        data = naive_data([1, 4], [["0", "1", "1"]], [])
        data["rows"][1]["state"][3] += 1
        data["rows"][1]["state"][0] += 1
        self.assertRejected(data)

    def test_smooth_sum_tamper(self):
        data = naive_data([1, 8, 16])
        data["rows"][-1]["state"][6] += 1
        self.assertRejected(data)

    def test_exact_smooth_cut_tamper(self):
        data = naive_data([1, 16])
        data["rows"][-1]["cuts"][0] = 3
        self.assertRejected(data)

    def test_wrong_endpoint_and_denominator(self):
        data = naive_data([1, 2], [["0", "1", "1/3"]])
        wrong = deepcopy(data)
        wrong["rows"][1]["X"] += 1
        self.assertRejected(wrong)
        data["denominator"] = 6
        self.assertRejected(data)

    def test_wrong_labels_and_incomplete_rows(self):
        data = naive_data([1, 2])
        wrong = deepcopy(data)
        wrong["labels"][2], wrong["labels"][3] = wrong["labels"][3], wrong["labels"][2]
        self.assertRejected(wrong)
        del data["rows"][0]["cuts"]
        self.assertRejected(data)

    def test_rows_strictly_increasing_and_boolean_rejected(self):
        data = naive_data([1, 2])
        data["rows"].reverse()
        self.assertRejected(data)
        data = naive_data([1])
        data["rows"][0]["k"] = True
        self.assertRejected(data)

    def test_overlapping_profile_and_zero_band_rejected(self):
        data = naive_data([1, 2])
        data["spec"]["profile"] = [["0", "2", "1"], ["1", "3", "1"]]
        self.assertRejected(data)
        data["spec"]["profile"] = [["0", "1", "0"]]
        self.assertRejected(data)

    def test_noncanonical_rational_variants_rejected(self):
        for text in ["01", "+1", "1/1", "2/4", "-0", "0/2", "1/0", " 1"]:
            data = naive_data([1])
            data["spec"]["profile"][0][2] = text
            self.assertRejected(data)

    def test_theta_order_and_range_rejected(self):
        for theta in [["1/2", "1/2"], ["2/3", "1/3"], ["0"], ["1"]]:
            data = naive_data([1])
            data["spec"]["theta"] = theta
            self.assertRejected(data)

    def test_exact_integral_power_and_perfect_rational_power(self):
        for k, q, expected in [(7, Fraction(1), 7), (7, Fraction(2), 49),
                               (16, Fraction(3, 2), 64), (64, Fraction(4, 3), 256)]:
            lower, upper = checker.power_enclosure(k, q, 8, self.meter)
            self.assertEqual((lower, upper), (Fraction(expected), Fraction(expected)))

    def test_nonintegral_power_grid_integer_inequalities(self):
        for k, q, precision in [(2, Fraction(3, 2), 8), (13, Fraction(4, 3), 11),
                                 (97, Fraction(7, 5), 24)]:
            lower, upper = checker.power_enclosure(k, q, precision, self.meter)
            R = int(lower * (1 << precision))
            target = k**q.numerator << (precision * q.denominator)
            self.assertLessEqual(R**q.denominator, target)
            self.assertLess(target, (R + 1)**q.denominator)
            self.assertEqual(upper - lower, Fraction(1, 1 << precision))

    def test_large_denominator_power_uses_exact_integer_comparison(self):
        q = Fraction(49999, 25000)
        lower, upper = checker.power_enclosure(2, q, 1, self.meter)
        self.assertEqual((lower, upper), (Fraction(7, 2), Fraction(4)))

    def test_power_accepts_actual_100000_bit_boundary(self):
        lower, upper = checker.power_enclosure(2, Fraction(99999), 8, self.meter)
        self.assertEqual(lower.numerator.bit_length(), 100000)
        self.assertEqual(lower, upper)

    def test_power_budget_overflow_rejected_before_allocation(self):
        with self.assertRaises(checker.ResourceLimit):
            checker.power_enclosure(2, Fraction(100000), 8, self.meter)
        with self.assertRaises(checker.ResourceLimit):
            checker.power_enclosure(2, Fraction(199999, 100000), 8, self.meter)

    def test_meter_limit_and_memory_gate(self):
        result = checker.verify_data(naive_data([1, 2]), checker.Meter(limit=0))
        self.assertFalse(result["verified"])
        self.assertEqual(result["error_type"], "ResourceLimit")
        data = naive_data([1])
        data["rows"] = [{"k": 100000000, "X": 100000000, "cuts": [], "state": [0]*6}]
        data["spec"]["theta"] = []
        data["labels"] = data["labels"][:6]
        self.assertEqual(self.admit(data)["error_type"], "ResourceLimit")

    def test_universal_weighted_square_domination_admitted(self):
        data = naive_data(list(range(1, 17)))
        rays = [{"weight": "2/7", "direction": ["1", "-3", "2/3", "0", "1/5", "0", "-1", "4"]}]
        candidate = simple_candidate(data, rays=rays)
        result = self.verify(candidate, data)
        self.assertTrue(result["verified"])
        self.assertTrue(result["uniform_domination_proved"])
        self.assertFalse(result["uniform_recurrence_proved"])
        self.assertFalse(result["RH_proved"])
        for row in data["rows"]:
            self.assertGreaterEqual(exact_energy(row, data, candidate), Fraction(row["state"][0], data["denominator"])**2)

    def test_signed_cross_terms_retained_inside_square(self):
        data = naive_data([1, 2], theta=[])
        rays = [{"weight": "1", "direction": ["0", "1", "1", "0", "0", "0"]}]
        candidate = simple_candidate(data, rays=rays, scales=[2], C="0")
        result = self.verify(candidate, data)
        self.assertTrue(result["verified"])
        self.assertEqual(result["training_bounds"][0]["upper"], "-2")

    def test_zero_and_negative_ray_weights_rejected(self):
        data = naive_data([1, 2])
        for weight in ["0", "-1"]:
            candidate = simple_candidate(data, rays=[{"weight": weight, "direction": ["0"]*8}])
            self.assertFalse(self.verify(candidate, data)["verified"])

    def test_bad_direction_dimension_and_excess_rays_rejected(self):
        data = naive_data([1])
        candidate = simple_candidate(data, rays=[{"weight": "1", "direction": ["1"]}])
        self.assertFalse(self.verify(candidate, data)["verified"])
        candidate = simple_candidate(data, rays=[{"weight": "1", "direction": ["0"]*8}]*257)
        self.assertFalse(self.verify(candidate, data)["verified"])

    def test_false_theorem_scope_flags_rejected(self):
        data = naive_data([1, 2])
        for flag in ["uniform_recurrence_proved", "uniform_head_bound_proved", "RH_proved"]:
            candidate = simple_candidate(data)
            candidate[flag] = True
            self.assertFalse(self.verify(candidate, data)["verified"])
            self.assertEqual(self.evaluate(candidate, data)["status"], "INVALID")

    def test_actual_base_not_upper_slack_required(self):
        data = naive_data([1, 2])
        candidate = simple_candidate(data)
        candidate["base_upper"] = "2"
        self.assertFalse(self.verify(candidate, data)["verified"])
        self.assertEqual(self.evaluate(candidate, data)["status"], "INVALID")

    def test_every_training_parent_required(self):
        data = naive_data([1, 4])
        candidate = simple_candidate(data, scales=[4])
        self.assertFalse(self.verify(candidate, data)["verified"])
        self.assertEqual(self.evaluate(candidate, data, [4])["status"], "INVALID")

    def test_training_maximum_exact_not_slack(self):
        data = naive_data(list(range(1, 10)))
        candidate = simple_candidate(data, scales=list(range(2, 10)))
        mapping = {r["k"]: r for r in data["rows"]}
        expected = max([Fraction(0)] + [Fraction(mapping[k]["state"][0]**2, k) -
                       Fraction(mapping[k//2]["state"][0]**2, k//2) for k in range(2, 10)])
        candidate["training_upper"] = str(expected)
        self.assertTrue(self.verify(candidate, data)["verified"])
        candidate["training_upper"] = str(expected + 1)
        self.assertFalse(self.verify(candidate, data)["verified"])

    def test_training_includes_odd_even_and_all_declared_scales(self):
        data = naive_data(list(range(1, 20)))
        candidate = simple_candidate(data, scales=list(range(2, 20)), C="0")
        result = self.verify(candidate, data)
        self.assertFalse(result["verified"])
        candidate["training_upper"] = "1"
        self.assertFalse(self.verify(candidate, data)["verified"])

    def test_final_exact_refutations_all_retained(self):
        data = naive_data(list(range(1, 33)))
        candidate = simple_candidate(data, C="0")
        result = self.evaluate(candidate, data)
        mapping = {r["k"]: r for r in data["rows"]}
        expected = [k for k in range(2, 33) if Fraction(mapping[k]["state"][0]**2, k) >
                    Fraction(mapping[k//2]["state"][0]**2, k//2)]
        self.assertEqual(result["status"], "REFUTED")
        self.assertEqual(result["violating_scales"], expected)
        self.assertEqual(len(result["witnesses"]), len(expected))
        self.assertTrue(all(Fraction(w["lower"]) > Fraction(w["C"]) for w in result["witnesses"]))
        self.assertFalse(result["uniform_recurrence_proved"])
        self.assertFalse(result["uniform_head_bound_proved"])
        self.assertFalse(result["RH_proved"])

    def test_explicit_evaluation_scales_exclude_other_rows(self):
        data = naive_data(list(range(1, 33)))
        result = self.evaluate(simple_candidate(data, C="0"), data, [2])
        self.assertEqual(result["status"], "VERIFIED_ON_FINITE_DOMAIN")
        self.assertEqual(result["evaluated_scales"], [2])
        self.assertEqual(result["violating_scales"], [])

    def test_evaluation_requires_base_and_sorted_unique_scales(self):
        data = naive_data(list(range(1, 5)))
        candidate = simple_candidate(data)
        for scales in [[3, 2], [2, 2], [True], [1]]:
            self.assertEqual(self.evaluate(candidate, data, scales)["status"], "INVALID")
        data["rows"] = data["rows"][1:]
        self.assertEqual(self.evaluate(candidate, data, [2])["status"], "INVALID")

    def test_rounding_ambiguous_not_refuted(self):
        data = naive_data(list(range(1, 65)))
        candidate = simple_candidate(data, q="3/2")
        mapping = {r["k"]: r for r in data["rows"]}
        chosen = None
        for k in range(2, 65):
            lk, uk = checker.power_enclosure(k, Fraction(3, 2), 8, self.meter)
            lp, up = checker.power_enclosure(k//2, Fraction(3, 2), 8, self.meter)
            e, ep = Fraction(mapping[k]["state"][0]**2), Fraction(mapping[k//2]["state"][0]**2)
            lower, upper = e/uk - ep/lp, e/lk - ep/up
            if 0 <= lower < upper:
                chosen = k, lower, upper
                break
        self.assertIsNotNone(chosen)
        k, lower, upper = chosen
        candidate["C"] = str((lower + upper)/2)
        result = self.evaluate(candidate, data, [k])
        self.assertEqual(result["status"], "UNRESOLVED_ROUNDING")
        self.assertEqual(result["violating_scales"], [])
        self.assertEqual(result["inconclusive_scales"], [k])
        self.assertEqual(result["inconclusive"][0]["lower"], str(lower))
        self.assertEqual(result["inconclusive"][0]["upper"], str(upper))

    def test_equality_at_C_not_rejection(self):
        data = naive_data([1, 2, 3, 4], theta=[])
        candidate = simple_candidate(data, C="1/4")
        result = self.evaluate(candidate, data, [4])
        self.assertEqual(result["worst_lower"], "1/4")
        self.assertEqual(result["worst_upper"], "1/4")
        self.assertEqual(result["status"], "VERIFIED_ON_FINITE_DOMAIN")

    def test_rational_input_4096_bit_gate_and_arbitrary_denominators(self):
        data = naive_data([1])
        rays = [{"weight": "1/17", "direction": ["1/19", "-2/23", "0", "0", "0", "0", "0", "0"]}]
        candidate = simple_candidate(data, rays=rays)
        self.assertTrue(self.verify(candidate, data)["verified"])
        candidate["rays"][0]["direction"][0] = str(1 << 4096)
        self.assertFalse(self.verify(candidate, data)["verified"])

    def test_declared_source_admission_separate_and_finite_scope(self):
        data = naive_data(list(range(1, 8)))
        result = self.evaluate(simple_candidate(data), data)
        self.assertEqual(result["status"], "VERIFIED_ON_FINITE_DOMAIN")
        self.assertTrue(result["source_admission_required_separately"])
        self.assertTrue(result["finite_only"])
        for flag in ["uniform_recurrence_proved", "uniform_head_bound_proved", "RH_proved"]:
            self.assertFalse(result[flag])

    def test_refutation_keeps_all_rounding_ambiguities_too(self):
        data = naive_data(list(range(1, 33)))
        rays = [{"weight": "1", "direction": ["0", "0", "1", "0", "0", "0", "0", "0"]}]
        candidate = simple_candidate(data, q="3/2", rays=rays)
        initial = self.evaluate(candidate, data, [4])
        lower, upper = Fraction(initial["worst_lower"]), Fraction(initial["worst_upper"])
        self.assertLess(lower, upper)
        candidate["C"] = str((lower + upper)/2)
        result = self.evaluate(candidate, data)
        self.assertEqual(result["status"], "REFUTED")
        self.assertIn(4, result["inconclusive_scales"])
        self.assertIn(5, result["violating_scales"])
        self.assertEqual(len(result["inconclusive"]), len(result["inconclusive_scales"]))

    def test_large_endpoint_source_matches_trial_division(self):
        # The endpoint matches the planned final experiment's maximum.  This
        # sparse direct trial-division oracle checks the full source domain;
        # it never calls the producer or reads a scientific candidate.
        data = naive_data([1, 2, 3, 32768], [["0", "10", "1"]],
                          ["1/9", "1/8", "1/7", "1/6", "1/5", "1/4", "1/3", "1/2"])
        result = self.admit(data)
        self.assertTrue(result["verified"], result)
        self.assertEqual(result["max_X"], 327680)
        self.assertLess(result["estimated_peak_bytes"], checker.MEMORY_BUDGET)

    def test_meter_operations_are_per_call_delta(self):
        data = naive_data([1, 2])
        first = self.admit(data)
        second = self.admit(data)
        self.assertEqual(first["operations"], second["operations"])
        self.assertEqual(self.meter.ops, first["operations"] + second["operations"])


def run_and_record():
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(SyntheticCheckerTests)
    tests = [test.id() for test in suite]
    started = time.perf_counter()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    elapsed = time.perf_counter() - started
    receipt_path = Path(__file__).with_name("mobius_prime_storage_checker_073_development.json")
    receipt = json.loads(receipt_path.read_text()) if receipt_path.exists() else {
        "schema": "independent-checker-development-073-v1", "runs": []}
    receipt["runs"].append({"tests": len(tests), "test_names": tests, "operations": ALL_OPERATIONS,
        "elapsed_seconds": elapsed, "returncode": 0 if result.wasSuccessful() else 1,
        "failures": [{"test": test.id(), "traceback": trace} for test, trace in result.failures],
        "errors": [{"test": test.id(), "traceback": trace} for test, trace in result.errors]})
    receipt["unique_new_synthetic_tests"] = len({test for run in receipt["runs"] for test in run["test_names"]})
    receipt["final_status"] = "PASS" if result.wasSuccessful() else "FAIL"
    receipt["scientific_candidate_outcomes_read"] = False
    receipt["independent_of_producer_search_and_old_checkers"] = True
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    raise SystemExit(0 if result.wasSuccessful() else 1)


if __name__ == "__main__":
    run_and_record()
