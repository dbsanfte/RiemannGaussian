"""Small exact kernel checks, deliberately not a native-coverage campaign."""
import unittest
from flint import fmpz_mod_poly_ctx
from frobenius_screen import (_multipoint_eval, frobenius_screen,
                              orbit_product, screen_details)


def direct(modulus, w, length):
    result, power = 1, 1
    for _ in range(length):
        power = power * w % modulus
        result = result * (power - 1) % modulus
    return result


class ProductKernelTests(unittest.TestCase):
    def test_empty_and_single(self):
        self.assertEqual(orbit_product(15, 2, 0), 1)
        self.assertEqual(orbit_product(15, 4, 1), 3)

    def test_global_zero_factor_and_repeated_block_points(self):
        # ceil(sqrt(10))=4; w**4=1 modulo 15 gives repeated points.
        self.assertEqual(orbit_product(15, 4, 10), direct(15, 4, 10))
        self.assertEqual(orbit_product(15, 4, 10), 0)

    def test_composite_zero_divisors_without_a_zero_leaf(self):
        # Factors 1,3,7 are all nonzero modulo 21, but their product is zero.
        self.assertEqual(orbit_product(21, 2, 3), 0)
        self.assertEqual(orbit_product(15, 2, 2), 3)

    def test_tail_and_exact_square(self):
        for N, w, length in [(10403, 2, 13), (77, 5, 16), (35, 0, 7)]:
            with self.subTest(N=N, w=w, length=length):
                self.assertEqual(orbit_product(N, w, length), direct(N, w, length))

    def test_remainder_tree_repeated_points_and_nonunit_differences(self):
        context = fmpz_mod_poly_ctx(15)
        coefficients = [2, 3, 4, 1]
        points = [2, 2, 7, 2, 12]  # odd tree, repeats, nonunit differences
        expected = []
        for point in points:
            value = 0
            for coefficient in reversed(coefficients):
                value = (value * point + coefficient) % 15
            expected.append(value)
        self.assertEqual(_multipoint_eval(context(coefficients), points, context), expected)

    def test_public_formula_and_unverified_contract_flag(self):
        # Only formula integration is tested; these are NOT native-order fixtures.
        for N, k, q in [(35, 2, 2), (20**6 - 1, 20, 2)]:
            result = screen_details(N, k, q)
            self.assertEqual(result.Z, direct(N, pow(q, N, N), result.B))
            self.assertEqual(frobenius_screen(N, k, q), result.gcd)
            self.assertFalse(result.native_order_contract_verified)
        with self.assertRaises(ValueError):
            screen_details(35, 1, 2)
        with self.assertRaises(ValueError):
            screen_details(35, 2, 5)


if __name__ == "__main__":
    unittest.main(verbosity=2)
