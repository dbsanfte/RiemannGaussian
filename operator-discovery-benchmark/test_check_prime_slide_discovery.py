"""Small exact rational tests for independent component algebra/support scope."""
from fractions import Fraction as Q
import unittest
import check_prime_slide_discovery as C

METERS = []


class Meter:
    def __init__(self, cap=2000000):
        self.operations = 0; self.cap = cap; self.peak_cells = 0; METERS.append(self)

    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('nonnegative integer work')
        if n > self.cap - self.operations: raise OverflowError('synthetic cap')
        self.operations += n

    def live(self, cells):
        self.charge(); self.peak_cells = max(self.peak_cells, cells)
        if cells > 6000000: raise MemoryError('resident cap')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_prime_slide_discovery operations=' +
          str(sum(m.operations for m in METERS)))


def action(coefficient, left, right):
    return dict(coefficient=coefficient, left=left, right=right)


def polynomial_value(rows, points, meter):
    total = Q(0)
    for exponent, coefficient in rows:
        term = Q(coefficient)
        for power, point in zip(exponent, points):
            meter.charge(power + 2); term *= point ** power
        total += term; meter.charge()
    return total


def direct_row(label, exponent, point, meter):
    if exponent == 0: meter.charge(); return Q(1)
    if label == 1:
        meter.charge(2 * exponent + 2); return point ** exponent - point ** (exponent - 1)
    if label == 2:
        meter.charge(4 * exponent + 2); return point ** (2 * exponent) - point ** (2 * exponent - 2)
    result = Q(0)
    for j in range(exponent + 1):
        meter.charge(2)
        result += direct_row(1, j, point, meter) * direct_row(2, exponent - j, point, meter)
    return result


def direct_component(program, i, j, points, meter):
    total = Q(0)
    for term in program['terms']:
        value = Q(term['coefficient'])
        for axis, point in enumerate(points):
            meter.charge(2)
            value *= direct_row(i, term['left'][axis], point, meter)
            value *= direct_row(j, term['right'][axis], point, meter)
        total += value; meter.charge()
    return total


class PrimeSlideCheckerTests(unittest.TestCase):
    def test_all_local_prime_power_rows_through_six(self):
        m = Meter()
        for e in range(7):
            p = dict(binding='same_prime', terms=[action(1, [e], [0])])
            rows = C.expand(p, m)
            for t in (Q(1, 2), Q(2, 3), Q(3, 5)):
                for i in range(3):
                    self.assertEqual(polynomial_value(rows[3 * i], (t,), m), direct_row(i, e, t, m))
            for component in rows:
                self.assertEqual(component, sorted(component, key=lambda row: row[0]))
                self.assertTrue(all(type(c) is int and c != 0 for _, c in component))

    def test_repeated_prime_double_slide_defect(self):
        m = Meter(); p = dict(binding='same_prime', terms=[action(1, [2], [0]), action(-2, [1], [1]), action(1, [0], [2])])
        rows = C.expand(p, m)
        self.assertEqual(rows[5], [[[0], -2], [[1], 1], [[2], 2], [[3], -2], [[4], 1]])
        for t in (Q(1, 2), Q(2, 3), Q(3, 5)):
            m.charge(15)
            self.assertEqual(polynomial_value(rows[5], (t,), m), (t - t ** 2) ** 2 + t + t ** 2 - 2)
            self.assertNotEqual(direct_row(1, 2, t, m), direct_row(1, 1, t, m) ** 2)
        facts = C.facts(p, m)
        self.assertEqual(facts['component_valuations'][5], [0])
        self.assertEqual(facts['common_valuations'], [0])
        self.assertFalse(facts['whole_signed_bound_proved'])

    def test_distinct_prime_bilinear_slide_retains_two_coordinates(self):
        m = Meter(); p = dict(binding='distinct_primes', terms=[
            action(1, [1, 1], [0, 0]), action(-1, [1, 0], [0, 1]),
            action(-1, [0, 1], [1, 0]), action(1, [0, 0], [1, 1])])
        rows = C.expand(p, m)
        self.assertEqual(rows[5], [[[1, 1], 1], [[1, 2], -1], [[2, 1], -1], [[2, 2], 1]])
        for t, s in ((Q(1, 2), Q(2, 3)), (Q(3, 5), Q(4, 7))):
            m.charge(15)
            self.assertEqual(polynomial_value(rows[5], (t, s), m), (t - t ** 2) * (s - s ** 2))
            for i in range(3):
                for j in range(3): self.assertEqual(polynomial_value(rows[3 * i + j], (t, s), m), direct_component(p, i, j, (t, s), m))
        facts = C.facts(p, m)
        self.assertEqual(facts['component_valuations'][5], [1, 1])
        self.assertEqual(facts['component_l1'][5], 4)
        self.assertIsNone(facts['component_valuations'][4])  # antisymmetrized identical sources

    def test_full_tensor_high_exponents_and_negative_coefficients(self):
        m = Meter()
        programs = [dict(binding='same_prime', terms=[action(2, [3], [3]), action(-1, [1], [2])]),
                    dict(binding='distinct_primes', terms=[action(-2, [2, 1], [1, 2]), action(1, [0, 0], [1, 1])])]
        for p in programs:
            rows = C.expand(p, m); dims = len(p['terms'][0]['left'])
            points = (Q(2, 5), Q(3, 7))[:dims]
            for i in range(3):
                for j in range(3): self.assertEqual(polynomial_value(rows[3 * i + j], points, m), direct_component(p, i, j, points, m))

    def test_zero_components_and_common_coordinatewise_valuations(self):
        m = Meter(); zero = dict(binding='same_prime', terms=[action(1, [1], [0]), action(-1, [1], [0])])
        f = C.facts(zero, m)
        self.assertEqual(f['multipliers'], [[]] * 9); self.assertEqual(f['component_l1'], [0] * 9)
        self.assertEqual(f['component_valuations'], [None] * 9); self.assertIsNone(f['common_valuations'])
        shifted = dict(binding='distinct_primes', terms=[action(1, [3, 3], [0, 0])])
        f = C.facts(shifted, m)
        self.assertEqual(f['common_valuations'], [1, 1])
        for rows, valuation, norm in zip(f['multipliers'], f['component_valuations'], f['component_l1']):
            m.charge(3 * len(rows))
            self.assertEqual(norm, sum(abs(c) for _, c in rows))
            self.assertEqual(valuation, [min(e[k] for e, _ in rows) for k in range(2)])

    def test_support_geometry_and_no_squared_single_bank_substitution(self):
        m = Meter()
        smooth = C.support_bound('same_prime', ['1/3'], '5/6', m)
        bank = C.support_bound('distinct_primes', ['1/3', '1/3'], '5/6', m)
        single = C.support_bound('same_prime', ['2/3'], '5/6', m)
        self.assertEqual(smooth['energy_upper_power'], '13/18')
        self.assertEqual(bank['energy_upper_power'], '4/9')
        self.assertEqual(single['energy_upper_power'], '4/9')
        self.assertNotEqual(bank['geometry'], single['geometry'])
        self.assertEqual(bank['independent_labels'], ['q', 'r']); self.assertEqual(bank['prime_count'], 2)
        self.assertEqual(bank['index_support'], 'h<=n/q,k<=n/r')
        self.assertEqual(smooth['index_support'], 'h<=n,k<=n/q')
        self.assertTrue(bank['logs_retained']); self.assertTrue(bank['distinct_and_coprime_domain_required'])
        self.assertFalse(bank['whole_signed_bound_proved'])
        for binding, weights in (('same_prime', ['1/3', '1/3']), ('distinct_primes', ['2/3']), ('same_prime', ['0']), ('distinct_primes', ['1/3', '0'])):
            with self.assertRaises(ValueError): C.support_bound(binding, weights, '5/6', m)

    def test_invalid_schema_bindings_indices_and_rationals(self):
        base = dict(binding='same_prime', terms=[action(1, [1], [0])])
        invalid = [{}, dict(base, id=1), dict(base, binding='unbound'), dict(base, terms=[]),
                   dict(base, terms=[action(True, [1], [0])]), dict(base, terms=[action(0, [1], [0])]),
                   dict(base, terms=[action(3, [1], [0])]), dict(base, terms=[action(1, [True], [0])]),
                   dict(base, terms=[action(1, [7], [0])]), dict(base, terms=[action(1, [3], [4])]),
                   dict(base, terms=[action(1, [1, 0], [0, 0])]), dict(base, terms=[dict(action(1, [1], [0]), extra=1)])]
        for p in invalid:
            with self.assertRaises(ValueError): C.validate(p)
        m = Meter()
        for weight, theta in ((True, '5/6'), ('2/6', '5/6'), ('-1/3', '5/6'), ('1/3', '1'), ('1/3', '1/3'), ('1/3', '1/0')):
            with self.assertRaises(ValueError): C.support_bound('same_prime', [weight], theta, m)

    def test_shared_meter_and_resource_failure(self):
        p = dict(binding='same_prime', terms=[action(1, [1], [0])]); m = Meter()
        C.expand(p, m); initial = m.operations; C.facts(p, m)
        self.assertGreater(m.operations, initial); self.assertLess(m.peak_cells, 6000000)
        with self.assertRaises(OverflowError): C.expand(p, Meter(cap=1))


if __name__ == '__main__': unittest.main()
