"""Tiny exact substitution/factor certificates; no archive/source evaluation."""
import copy
from fractions import Fraction as Q
from math import gcd
import unittest
import check_prime_exchange_discovery as C

METERS = []


class Meter:
    def __init__(self, cap=2000000):
        self.operations = 0; self.cap = cap; self.peak_cells = 0; METERS.append(self)

    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('strict charge')
        if n > self.cap - self.operations: raise OverflowError('synthetic cap')
        self.operations += n

    def live(self, cells):
        self.charge(); self.peak_cells = max(self.peak_cells, cells)
        if cells > 6000000: raise MemoryError('synthetic resident cap')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_prime_exchange_discovery operations=' +
          str(sum(m.operations for m in METERS)))


def tensor(first, second=None):
    return [first, [] if second is None else second] + [[] for _ in range(7)]


def evaluate(poly, x, y, m):
    result = Q(0)
    for (i, j), coefficient in poly:
        m.charge(i + j + 4); result += Q(coefficient) * x ** i * y ** j
    return result


class PrimeExchangeCheckerTests(unittest.TestCase):
    def test_exact_48_normalized_linear_forms(self):
        forms = C.linear_forms()
        self.assertEqual(len(forms), 48); self.assertEqual(forms, sorted(forms))
        self.assertEqual(len({tuple(f) for f in forms}), 48)
        for a, b, c in forms:
            self.assertNotEqual((a, b), (0, 0)); self.assertEqual(gcd(gcd(abs(a), abs(b)), abs(c)), 1)
            self.assertGreater(a if a else b, 0)
        self.assertIn([1, -1, 0], forms); self.assertIn([0, 2, 1], forms)
        self.assertNotIn([-1, 1, 0], forms)

    def test_substitution_both_axes_and_fractional_intercepts(self):
        m = Meter()
        # (2x+y+1)(x-y): rational substitution x=-(y+1)/2.
        p = [[[0, 1], -1], [[0, 2], -1], [[1, 0], 1], [[1, 1], -1], [[2, 0], 2]]
        self.assertTrue(C.divisible(p, [2, 1, 1], m)); self.assertTrue(C.divisible(p, [1, -1, 0], m))
        self.assertFalse(C.divisible(p, [1, 1, 0], m))
        horizontal = [[[0, 0], '1/2'], [[0, 1], '1'], [[1, 0], '1/2'], [[1, 1], '1']]
        self.assertTrue(C.divisible(horizontal, [0, 2, 1], m))
        self.assertFalse(C.divisible(horizontal, [0, 1, 1], m))
        self.assertTrue(C.divisible([], [1, 0, 0], m))
        self.assertFalse(C.divisible([[[0, 0], 1]], [1, 0, 0], m))
        for y in (Q(-3, 2), Q(1, 3), Q(2)):
            self.assertEqual(evaluate(p, -(y + 1) / 2, y, m), 0)

    def test_full_recomposition_with_zero_tensor_components(self):
        m = Meter()
        original = tensor([[[0, 2], -1], [[2, 0], 1]], [[[0, 1], -1], [[1, 0], 1]])
        quotients = tensor([[[0, 1], '1'], [[1, 0], '1']], [[[0, 0], '1']])
        factors = [dict(coefficients=[1, -1, 0], multiplicity=1)]
        record = C.verify(original, factors, quotients, m)
        self.assertTrue(record['residual_maximal']); self.assertEqual(record['searched_linear_form_count'], 48)
        self.assertFalse(record['whole_signed_bound_proved']); self.assertEqual(record['full_domain_recovery'], 'OPEN')
        for x, y in ((Q(1, 2), Q(2, 3)), (Q(-2), Q(3))):
            for before, after in zip(original, quotients):
                m.charge(2); self.assertEqual(evaluate(before, x, y, m), (x - y) * evaluate(after, x, y, m))
        bad = copy.deepcopy(quotients); bad[1][0][1] = '2'
        with self.assertRaises(ValueError): C.verify(original, factors, bad, m)
        dropped = copy.deepcopy(original); dropped[1] = []
        with self.assertRaises(ValueError): C.verify(dropped, factors, quotients, m)

    def test_multiplicity_and_maximality_are_independently_checked(self):
        m = Meter()
        original = tensor([[[0, 2], 1], [[1, 1], -2], [[2, 0], 1]])
        factor = dict(coefficients=[1, -1, 0], multiplicity=2)
        C.verify(original, [factor], tensor([[[0, 0], '1']]), m)
        with self.assertRaises(ValueError): C.verify(original, [dict(factor, multiplicity=1)], tensor([[[0, 1], '-1'], [[1, 0], '1']]), m)
        with self.assertRaises(ValueError): C.verify(original, [], tensor([[[0, 2], '1'], [[1, 1], '-2'], [[2, 0], '1']]), m)
        with self.assertRaises(ValueError): C.verify(original, [dict(factor, multiplicity=3)], tensor([[[0, 0], '1']]), m)
        # A residual nonlinear factor outside the finite searched class is allowed.
        nonlinear = tensor([[[0, 0], 1], [[2, 0], 1]])
        C.verify(nonlinear, [], tensor([[[0, 0], '1'], [[2, 0], '1']]), m)

    def test_factor_order_no_duplicates_and_normalization(self):
        m = Meter(); original = tensor([[[0, 0], -1], [[2, 0], 1]])
        quotients = tensor([[[0, 0], '1']])
        factors = [dict(coefficients=[1, 0, -1], multiplicity=1), dict(coefficients=[1, 0, 1], multiplicity=1)]
        C.verify(original, factors, quotients, m)
        for fs in (list(reversed(factors)), [factors[0], factors[0]],
                   [dict(coefficients=[-1, 0, 1], multiplicity=1)],
                   [dict(coefficients=[2, 0, -2], multiplicity=1)],
                   [dict(coefficients=[1, 0, -1], multiplicity=True)],
                   [dict(coefficients=[1, 0, -1], multiplicity=0)],
                   [dict(factors[0], extra=1)]):
            with self.assertRaises(ValueError): C.verify(original, fs, quotients, m)

    def test_directed_edge_constants_and_open_domain_obligations(self):
        m = Meter()
        record = C.edge_bound('3/4', '1/3', '4', m)
        self.assertEqual(record['energy_upper_power'], '0'); self.assertTrue(record['cofinal'])
        self.assertEqual(record['constant_multiplier'], '14'); self.assertEqual(record['constant_power_of_two'], '1')
        self.assertEqual(record['logdegree'], 2); self.assertEqual(record['orientation'], 'r<q')
        self.assertTrue(record['both_orientation_supports_retained']); self.assertFalse(record['growing_degree_graphs_admitted'])
        self.assertIn('uniformly', record['outgoing_degree_scope'])
        self.assertEqual(record['symmetric_component'], 'OPEN'); self.assertEqual(record['core_component'], 'OPEN')
        self.assertEqual(record['full_domain_recovery'], 'OPEN'); self.assertFalse(record['whole_signed_bound_proved'])
        self.assertFalse(C.edge_bound('1/2', '1/3', '1', m)['cofinal'])
        self.assertTrue(C.edge_bound('4/5', '1/3', '3/2', m)['cofinal'])
        high = C.edge_bound('5/6', '2', '2', m)
        self.assertEqual(high['constant_power_of_two'], '0')
        for theta, weight, degree in (('1', '1/3', '1'), ('1/3', '1/3', '1'), ('3/4', '0', '1'),
                                       ('3/4', '-1/3', '1'), ('3/4', '1/3', '0'), ('6/8', '1/3', '1'),
                                       ('3/4', '1/3', True), ('3/4', '1/3', '1/0')):
            with self.assertRaises(ValueError): C.edge_bound(theta, weight, degree, m)

    def test_invalid_polynomial_schemas_and_all_zero_input(self):
        m = Meter(); f = [1, -1, 0]
        for p in ([[[0, 0], 0]], [[[0, 0], True]], [[[0, 0], '2/4']], [[[True, 0], 1]],
                  [[[25, 0], 1]], [[[1, 0], 1], [[0, 0], 1]], [[[0, 0], 1], [[0, 0], 2]],
                  [[[0], 1]], [[[0, 0], 1.0]]):
            with self.assertRaises(ValueError): C.divisible(p, f, m)
        with self.assertRaises(ValueError): C.verify([[]] * 9, [], [[]] * 9, m)
        with self.assertRaises(ValueError): C.verify([[]] * 8, [], [[]] * 9, m)
        with self.assertRaises(ValueError): C.verify(tensor([[[0, 0], '1']]), [], tensor([[[0, 0], '1']]), m)
        with self.assertRaises(ValueError): C.verify(tensor([[[0, 0], 1]]), [], tensor([[[0, 0], 1]]), m)

    def test_shared_meter_and_cap(self):
        m = Meter(); p = [[[0, 1], -1], [[1, 0], 1]]
        C.divisible(p, [1, -1, 0], m); previous = m.operations
        C.verify(tensor(p), [dict(coefficients=[1, -1, 0], multiplicity=1)], tensor([[[0, 0], '1']]), m)
        self.assertGreater(m.operations, previous); self.assertLess(m.peak_cells, 6000000)
        with self.assertRaises(OverflowError): C.divisible(p, [1, -1, 0], Meter(cap=1))


if __name__ == '__main__': unittest.main()
