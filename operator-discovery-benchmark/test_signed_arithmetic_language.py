"""Independent factor checks and exact signed AST boundary regressions."""

from fractions import Fraction as Q
from math import gcd, isqrt
import json
import unittest

import signed_arithmetic_language as lang
from detector_safe_evaluation import Status


def factor_coefficients(N):
    mu, liouville = [0], [0]
    for n in range(1, N + 1):
        rest, exponents, p = n, [], 2
        while p * p <= rest:
            exponent = 0
            while rest % p == 0:
                rest //= p
                exponent += 1
            if exponent:
                exponents.append(exponent)
            p += 1
        if rest > 1:
            exponents.append(1)
        sign = (-1) ** sum(exponents)
        mu.append(0 if any(e > 1 for e in exponents) else sign)
        liouville.append(sign)
    return mu, liouville


class SignedLanguageTests(unittest.TestCase):
    def table(self, node, N):
        result = lang.evaluate(node, N)
        self.assertEqual(result.status, Status.AVAILABLE, result)
        json.dumps(result.value)
        return [Q(value) for value in result.value['coefficients']]

    def test_actual_coefficients_against_independent_factorization(self):
        mu, liouville = factor_coefficients(512)
        self.assertEqual(self.table(lang.expr('mu'), 512), mu)
        self.assertEqual(self.table(lang.expr('liouville'), 512), liouville)
        actual = lang.complete_mobius(512).value
        self.assertFalse(actual['provenance']['prime_or_factor_oracle_used'])

    def test_signed_convolution_and_point_product(self):
        mu, liouville = lang.expr('mu'), lang.expr('liouville')
        one = lang.expr('one')
        self.assertEqual(self.table(lang.expr('convolution', mu, one), 64), [0, 1] + [0] * 63)
        squares = self.table(lang.expr('convolution', liouville, one), 64)
        self.assertEqual(squares, [0] + [int(isqrt(n) ** 2 == n) for n in range(1, 65)])
        product = self.table(lang.expr('product', mu, liouville), 64)
        expected_mu = factor_coefficients(64)[0]
        self.assertEqual(product, [n * n for n in expected_mu])

    def test_rational_weights_serialized_AST_and_prefix(self):
        node = lang.expr('add', lang.expr('scale', lang.expr('mu'), weight='1/3'),
                         lang.expr('scale', lang.expr('one'), weight='-2/5'))
        table = self.table(node.to_dict(), 12)
        mu = factor_coefficients(12)[0]
        self.assertEqual(table, [0] + [Q(mu[n], 3) - Q(2, 5) for n in range(1, 13)])
        pref = self.table(lang.expr('prefix', node), 12)
        self.assertEqual(pref, [sum(table[:n + 1]) for n in range(13)])

    def test_shift_dilate_quotient_root_and_masks(self):
        base = lang.expr('prefix', lang.expr('one'))
        self.assertEqual(self.table(lang.expr('shift', base, offset=-2), 6), [0, 0, 0, 1, 2, 3, 4])
        self.assertEqual(self.table(lang.expr('dilate', base, factor=3), 6), [0, 3, 6, 9, 12, 15, 18])
        self.assertEqual(self.table(lang.expr('floor_index', base, divisor=3), 6), [0, 0, 0, 1, 1, 1, 2])
        self.assertEqual(self.table(lang.expr('root_index', base, order=2), 6), [0, 1, 1, 1, 2, 2, 2])
        self.assertEqual(self.table(lang.expr('truncate', base, cutoff=3), 6), [0, 1, 2, 3, 0, 0, 0])
        self.assertEqual(self.table(lang.expr('coprime_mask', base, modulus=6), 6),
                         [0] + [n if gcd(n, 6) == 1 else 0 for n in range(1, 7)])
        self.assertEqual(self.table(lang.expr('residue_mask', base, modulus=3, residue=1), 6),
                         [0, 1, 0, 0, 4, 0, 0])

    def test_full_power_normalizer_huge_denominator_and_root(self):
        self.assertEqual(lang.ceil_power(2, '3/2').value['ceiling'], 3)
        self.assertEqual(lang.ceil_power(3, Q(1, 10 ** 100)).value['ceiling'], 2)
        self.assertEqual(lang.floor_root(255, 10 ** 100).value['root'], 1)
        self.assertEqual(lang.floor_root(256, 8).value['root'], 2)
        normalized = lang.expr('normalize', lang.expr('one'), power='3/2')
        self.assertEqual(self.table(normalized, 4), [0, 1, Q(1, 3), Q(1, 6), Q(1, 8)])

    def test_missing_budget_never_publishes_partial_sums(self):
        tiny = lang.WorkBudget(max_operations=10)
        result = lang.complete_mobius(100, budget=tiny)
        self.assertEqual(result.status, Status.MISSING)
        self.assertIsNone(result.value)
        result = lang.evaluate(lang.expr('normalize', lang.expr('one'), power='1000001'), 2)
        self.assertEqual(result.status, Status.MISSING)
        self.assertIsNone(result.value)
        too_many_cells = lang.WorkBudget(max_cells=8)
        self.assertEqual(lang.evaluate(lang.expr('dilate', lang.expr('one'), factor=100),
                                      3, budget=too_many_cells).status, Status.MISSING)

    def test_invalid_expressions_and_unsupported_logs(self):
        for node in [lang.expr('scale', lang.expr('one'), weight=0.5),
                     lang.expr('floor_index', lang.expr('one'), divisor=0),
                     lang.expr('normalize', lang.expr('one'), power='-1'),
                     lang.expr('formal_log'),
                     lang.expr('mu', unexpected=1)]:
            self.assertEqual(lang.evaluate(node, 8).status, Status.INVALID)

    def test_complete_mixed_moment_retains_negative_signs(self):
        mu = lang.expr('mu')
        result = lang.mixed_moment(mu, lang.expr('one'), 4)
        self.assertEqual(result.value['signed_sum'], -1)
        self.assertEqual(result.value['term_count'], 4)
        self.assertTrue(result.value['all_signed_products_retained'])

    def test_full_coupled_defect_and_shared_crosses(self):
        mu = factor_coefficients(1024)[0]
        M = [sum(mu[:n + 1]) for n in range(len(mu))]
        for X in [1, 2, 4, 16, 64, 256]:
            response = lang.coupled_response(X)
            self.assertEqual(response.status, Status.AVAILABLE, response)
            row = response.value
            json.dumps(row)
            u = isqrt(4 * X - 1)
            self.assertEqual(row['cutoff'], u)
            direct = sum(M[n] ** 2 for n in range(2 * X, 4 * X)) - 4 * sum(
                M[n] ** 2 for n in range(X, 2 * X))
            F2 = [sum(mu[a] * mu[b] * (n // (a * b))
                      for a in range(1, u + 1) for b in range(1, u + 1))
                  for n in range(X, 4 * X)]
            cross_parent = sum(M[u] * F2[n - X] for n in range(X, 2 * X))
            cross_child = sum(M[u] * F2[n - X] for n in range(2 * X, 4 * X))
            self.assertEqual(row['moments']['cross']['parent'], cross_parent)
            self.assertEqual(row['moments']['cross']['child'], cross_child)
            self.assertEqual(row['signed_defect'], direct)
            self.assertEqual(row['negative_low_prefix_credit'], -8 * X * M[u] ** 2)
            self.assertEqual(row['reconstructed_defect'], direct)
            self.assertEqual(row['identity_residual'], 0)
            self.assertTrue(row['all_prefix_coefficients_recovered'])
            self.assertFalse(row['global_actual_signed_bound_proved'])

    def test_liouville_floor_calibration_charges_unsigned_terms(self):
        for x in [1, 2, 16, 64, 1024]:
            row = lang.liouville_floor_sum(x).value
            self.assertEqual(row['signed_sum'], isqrt(x))
            self.assertEqual(row['unsigned_charge'], sum(x // d for d in range(1, x + 1)))
            self.assertEqual(row['term_count'], x)


if __name__ == '__main__':
    unittest.main()
