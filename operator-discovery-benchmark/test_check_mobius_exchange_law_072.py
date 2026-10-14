"""Synthetic mathematical and tampering tests; no scientific or old-suite input."""
import copy
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt
import unittest

from check_mobius_exchange_law_072 import GRID, Meter, evaluate_law, verify_law


def root(x):
    x = F(x)
    n = isqrt(x.numerator * GRID * GRID // x.denominator)
    return F(n + (n * n * x.denominator < x.numerator * GRID * GRID), GRID)


def trial_mu(n):
    result = 1
    for p in range(2, n + 1):
        if n % p == 0:
            n //= p
            result = -result
            if n % p == 0:
                return 0
    return result


def fixture(profile, cap=3, primal=None, dual=None):
    """Independent small fixture via literal midpoint/mask enumeration."""
    bands = [(F(lo), F(hi), F(v)) for lo, hi, v in profile]
    primes = [p for p in range(2, cap + 1) if all(p % d for d in range(2, p))]
    families = []
    for a in range(1, cap + 1):
        for b in range(a + 1, cap + 1):
            if not trial_mu(a) or not trial_mu(b) or gcd(a, b) != 1:
                continue
            for ilo, ihi, iv in bands:
                for jlo, jhi, jv in bands:
                    lo, hi = max(ilo / a, jlo / b), min(ihi / a, jhi / b)
                    gain = abs(iv) + abs(jv) - abs(trial_mu(a) * iv + trial_mu(b) * jv)
                    if lo < hi and gain > 0:
                        density = F(1)
                        for p in primes:
                            if a * b % p == 0:
                                density *= F(p, p + 1)
                        families.append(dict(a=a, b=b, lo=str(lo), hi=str(hi), left_value=str(iv),
                                             right_value=str(jv), gain=str(gain), density_ratio=str(density)))
    endpoints = sorted({F(f[key]) * f[m] for f in families for key in ("lo", "hi") for m in ("a", "b")})
    rows = set()
    for left, right in zip(endpoints, endpoints[1:]):
        midpoint = (left + right) / 2
        for bits in product((0, 1), repeat=len(primes)):
            mask = sum(bit << j for j, bit in enumerate(bits))
            row = []
            for i, f in enumerate(families):
                mask_ab = sum((1 << j) for j, p in enumerate(primes) if f["a"] * f["b"] % p == 0)
                for multiplier in (f["a"], f["b"]):
                    required = sum((1 << j) for j, p in enumerate(primes) if multiplier % p == 0)
                    if multiplier * F(f["lo"]) < midpoint <= multiplier * F(f["hi"]) and mask & mask_ab == required:
                        row.append(i)
            if row:
                rows.add(tuple(row))
    rows = [list(row) for row in sorted(rows)]
    numerators = [0] * len(families) if primal is None else primal(families)
    denominator = max([GRID] + [sum(numerators[i] for i in row) for row in rows])
    ys = [0] * len(rows) if dual is None else dual(rows)
    weights = [F(n, denominator) for n in numerators]
    rewards = [F(f["gain"]) * F(f["density_ratio"]) * (F(f["hi"]) - F(f["lo"])) for f in families]
    gain = sum((w * r for w, r in zip(weights, rewards)), F(0))
    upper = F(sum(ys), GRID) + sum((max(r - sum((F(y, GRID) for row, y in zip(rows, ys) if i in row), F(0)), 0)
                                  for i, r in enumerate(rewards)), F(0))
    baseline = sum((abs(v) * (hi - lo) for lo, hi, v in bands), F(0))
    error = sum((3 * abs(v) * (root(lo) + root(hi)) for lo, hi, v in bands), F(0))
    error += sum((w * F(f["gain"]) * (2 ** sum(f["a"] * f["b"] % p == 0 for p in primes) + 2) *
                  (root(f["lo"]) + root(f["hi"])) for w, f in zip(weights, families)), F(0))
    return dict(schema="mobius-uniform-exchange-law-v1", profile=[dict(lo=str(lo), hi=str(hi), value=str(v)) for lo, hi, v in bands],
                cap=cap, primes=primes, candidates=families, capacity_rows=rows,
                lambda_denominator=denominator, lambda_numerators=numerators,
                dual_denominator=GRID, dual_numerators=ys, objective_gain=str(gain), objective_upper=str(upper),
                leading_upper=str(baseline - gain), leading_lower=str(baseline - upper), sqrt_error_upper=str(error),
                selected_family_indices=[i for i, n in enumerate(numerators) if n], solver={"fixture": True},
                uniform_profile_bound_proved=True, sublinear_profile_bound_proved=baseline == gain,
                uniform_head_bound_proved=False, RH_proved=False)


class ExchangeLawTests(unittest.TestCase):
    def setUp(self):
        self.simple = fixture([(1, 4, 1)], 2, primal=lambda families: [GRID])

    def test_single_exchange_exact_math(self):
        c = self.simple
        self.assertEqual(c["candidates"], [dict(a=1, b=2, lo="1", hi="2", left_value="1", right_value="1", gain="2", density_ratio="2/3")])
        self.assertEqual(c["capacity_rows"], [[0]])
        self.assertEqual(c["objective_gain"], "4/3")
        self.assertEqual(c["leading_upper"], "5/3")
        self.assertEqual(F(c["sqrt_error_upper"]), 9 + 8 * (root(2) + 1))
        self.assertTrue(verify_law(c)["verified"])

    def test_finite_prices_direct_trial_division(self):
        for k in (1, 2, 3, 5, 11, 17, 31):
            result = evaluate_law(self.simple, k)
            signed = sum(trial_mu(n) for n in range(k + 1, 4 * k + 1))
            baseline = sum(trial_mu(n) ** 2 for n in range(k + 1, 4 * k + 1))
            matched = sum(trial_mu(m) ** 2 for m in range(k + 1, 2 * k + 1) if m % 2)
            self.assertEqual(F(result["actual_signed_target"]), signed)
            self.assertEqual(F(result["certified_finite_price"]), baseline - 2 * matched)
            self.assertEqual(result["family_counts"], [matched])

    def test_generic_rational_profile_and_conflicting_capacities(self):
        c = fixture([(F(1, 3), F(7, 3), F(3, 2)), (3, 7, F(-2, 3))], 7,
                    primal=lambda families: [GRID] * len(families), dual=lambda rows: [GRID // 7] * len(rows))
        self.assertTrue(any(len(row) > 1 for row in c["capacity_rows"]))
        self.assertTrue(verify_law(c)["verified"])
        for k in (1, 3, 11):
            r = evaluate_law(c, k)
            self.assertLessEqual(F(r["actual_absolute_target"]), F(r["certified_finite_price"]))

    def test_source_profile_complete_candidates(self):
        c = fixture([(8, 10, 1), (16, 20, -1)], 7, primal=lambda families: [GRID] * len(families))
        pairs = {(f["a"], f["b"]) for f in c["candidates"]}
        self.assertIn((3, 5), pairs)
        self.assertIn((3, 7), pairs)
        self.assertNotIn((1, 2), pairs)
        self.assertTrue(verify_law(c)["verified"])
        self.assertGreater(F(c["leading_upper"]), 0)
        self.assertFalse(evaluate_law(c, 17)["uniform_head_bound_proved"])

    def test_robust_dual_positive_defect(self):
        self.assertEqual(self.simple["objective_upper"], "4/3")
        c = copy.deepcopy(self.simple)
        c["objective_upper"] = "0"
        c["leading_lower"] = "3"
        with self.assertRaisesRegex(ValueError, "objective_upper"):
            verify_law(c)

    def test_large_dual_negative_leading_lower_retained(self):
        c = fixture([(1, 4, 1)], 2, dual=lambda rows: [10 * GRID])
        self.assertEqual(verify_law(c)["leading_lower"], "-7")

    def test_zero_families_nonempty_profile(self):
        c = fixture([(8, 10, 1), (16, 20, -1)], 2)
        self.assertEqual(c["candidates"], [])
        self.assertEqual(verify_law(c)["leading_upper"], "6")
        self.assertEqual(evaluate_law(c, 1)["family_counts"], [])

    def test_profile_resource_limits_and_extra_claim_rejected(self):
        c = fixture([], 2)
        with self.assertRaisesRegex(ValueError, "1..16"):
            verify_law(c)
        c = copy.deepcopy(self.simple)
        c["profile"] *= 17
        with self.assertRaisesRegex(ValueError, "1..16"):
            verify_law(c)
        c = copy.deepcopy(self.simple)
        c["extra_theorem_claim"] = True
        with self.assertRaisesRegex(ValueError, "fields mismatch"):
            verify_law(c)

    def test_unit_squareful_zero_and_closed_rational_endpoints(self):
        c = fixture([(0, 1, F(3, 2)), (F(3, 2), 2, F(-1, 2))], 2)
        first = evaluate_law(c, 1)
        self.assertEqual(F(first["actual_signed_target"]), 2)  # mu(1)=1, mu(2)=-1
        c = fixture([(3, 4, 7)], 2)
        result = evaluate_law(c, 1)
        self.assertEqual(result["actual_signed_target"], "0")  # mu(4)=0
        self.assertEqual(result["baseline_squarefree_price"], "0")

    def test_missing_extra_reordered_families(self):
        c = fixture([(1, 8, 1)], 3)
        for families in (c["candidates"][:-1], c["candidates"] + c["candidates"][:1], list(reversed(c["candidates"]))):
            tampered = copy.deepcopy(c)
            tampered["candidates"] = families
            with self.assertRaises(ValueError):
                verify_law(tampered)

    def test_missing_extra_capacity_and_false_divisibility(self):
        for mutation in (lambda c: c.update(capacity_rows=[]),
                         lambda c: c["capacity_rows"].append([0]),
                         lambda c: c["candidates"][0].update(density_ratio="1")):
            c = copy.deepcopy(self.simple)
            mutation(c)
            with self.assertRaises(ValueError):
                verify_law(c)

    def test_primal_overload_and_unit_upper(self):
        for field, value in (("lambda_numerators", [GRID + 1]), ("lambda_numerators", [-1]),
                             ("lambda_denominator", GRID - 1), ("dual_denominator", GRID + 1),
                             ("dual_numerators", [-1])):
            c = copy.deepcopy(self.simple)
            c[field] = value
            with self.assertRaises(ValueError):
                verify_law(c)

    def test_capacity_overload_even_with_individual_bounds(self):
        c = fixture([(1, 8, 1)], 3, primal=lambda families: [GRID] * len(families))
        self.assertTrue(any(len(row) > 1 for row in c["capacity_rows"]))
        c["lambda_denominator"] = GRID
        with self.assertRaisesRegex(ValueError, "capacity"):
            verify_law(c)

    def test_full_error_all_endpoints_cannot_be_dropped(self):
        for key in ("objective_gain", "leading_upper", "leading_lower", "sqrt_error_upper"):
            c = copy.deepcopy(self.simple)
            c[key] = str(F(c[key]) + F(1, GRID))
            with self.assertRaisesRegex(ValueError, key):
                verify_law(c)

    def test_scope_flags_and_selected(self):
        for key, value in (("uniform_profile_bound_proved", False), ("sublinear_profile_bound_proved", True),
                           ("uniform_head_bound_proved", True), ("RH_proved", True),
                           ("RH_proved", 0), ("selected_family_indices", [])):
            c = copy.deepcopy(self.simple)
            c[key] = value
            with self.assertRaises(ValueError):
                verify_law(c)

    def test_noncanonical_and_typed_inputs(self):
        for mutate in (lambda c: c["profile"][0].update(lo="2/2"),
                       lambda c: c["profile"][0].update(value="0"),
                       lambda c: c.update(profile=[dict(lo="2", hi="4", value="1"), dict(lo="1", hi="2", value="1")]),
                       lambda c: c.update(cap=True), lambda c: c.update(primes=[True]),
                       lambda c: c.update(lambda_numerators=[True]),
                       lambda c: c["candidates"][0].update(a=True),
                       lambda c: c.update(capacity_rows=[[False]])):
            c = copy.deepcopy(self.simple)
            mutate(c)
            with self.assertRaises(ValueError):
                verify_law(c)

    def test_root_exact_and_roundup(self):
        c = fixture([(0, F(1, 7), 1)], 2)
        self.assertEqual(F(c["sqrt_error_upper"]), 3 * root(F(1, 7)))
        self.assertTrue(verify_law(c)["verified"])

    def test_meter_abort_and_evaluator_scale(self):
        with self.assertRaises(RuntimeError):
            verify_law(self.simple, Meter(limit=0))
        with self.assertRaises(RuntimeError):
            verify_law(self.simple, Meter(seconds=-1))
        for k in (0, -1, True, F(1, 2)):
            with self.assertRaises(ValueError):
                evaluate_law(self.simple, k)

    def test_resource_cap_explicit_no_partial_answer(self):
        with self.assertRaisesRegex(ValueError, "resource cap"):
            evaluate_law(self.simple, 50_000_001)
        c = copy.deepcopy(self.simple)
        c["objective_gain"] = str(1 << 4097)
        with self.assertRaisesRegex(ValueError, "bit cap"):
            verify_law(c)


if __name__ == "__main__":
    unittest.main()
