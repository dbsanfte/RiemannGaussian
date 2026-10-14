"""Exact tiny occupancy-mode and complete prefix-kernel tests."""
from fractions import Fraction as Q
import unittest
import check_occupancy_transfer as C

METERS = []


class Meter:
    def __init__(self, cap=2000000):
        self.operations = 0; self.cap = cap; METERS.append(self)

    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('strict operation charge')
        if n > self.cap - self.operations: raise OverflowError('synthetic operation cap')
        self.operations += n


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_occupancy_transfer operations=' +
          str(sum(m.operations for m in METERS)))


def absent(bits, coefficient='1'):
    return [coefficient if not mask & bits else '0' for mask in range(16)]


def polynomial(values, z, meter):
    meter.charge(8)
    return Q(values[0]) + Q(values[1]) * z ** 2 + Q(values[2]) * z ** 4


class OccupancyCheckerTests(unittest.TestCase):
    def test_known_modes_all16_relations_and_fractional_scaling(self):
        m = Meter()
        for potential, u, v in ((absent(15), '0', '0'), (absent(5), '0', '2'),
                                (absent(3, '1/3'), '1', '1'), (absent(1, '-2/3'), '1', '2'),
                                (['1'] * 16, '2', '2')):
            record = C.verify_mode(potential, u, v, m)
            for mask in range(16):
                m.charge(6)
                self.assertEqual(Q(record['Nu'][mask]), Q(potential[mask | 1]) + Q(potential[mask | 4]))
                self.assertEqual(Q(record['Nv'][mask]), Q(potential[mask | 2]) + Q(potential[mask | 8]))
                self.assertEqual(Q(record['Nu'][mask]), Q(u) * Q(potential[mask]))
                self.assertEqual(Q(record['Nv'][mask]), Q(v) * Q(potential[mask]))
            self.assertFalse(record['energy_contraction_proved']); self.assertFalse(record['RH_proved'])
        self.assertEqual(C.verify_mode(absent(3), '1', '1', m)['bulk_polynomial'], ['-1', '1', '1'])

    def test_envelope_is_scalar_algebra_and_stable_final_mask_obstruction(self):
        m = Meter(); stable = []
        for potential, u, v in ((absent(15), '0', '0'), (absent(5), '0', '2'), (absent(3), '1', '1')):
            record = C.verify_mode(potential, u, v, m); stable.append(potential)
            self.assertTrue(record['stable']); self.assertEqual(record['final_mask_value'], '0')
            self.assertTrue(record['stable_final_mask_zero']); self.assertTrue(record['algebraic_envelope_only'])
            for t in (Q(1, 10), Q(1, 2), Q(3, 4)):
                m.charge(8)
                a, b = Q(u), Q(v)
                self.assertLessEqual(abs(1 - a - b + a * t + b * t * t), Q(record['bulk_envelope']))
        constant = C.verify_mode(['1'] * 16, '2', '2', m)
        self.assertFalse(constant['stable']); self.assertEqual(constant['bulk_envelope'], '3')
        self.assertEqual(constant['final_mask_value'], '1')
        target = ['0'] * 15 + ['1']
        with self.assertRaises(ValueError): C.verify_recovery(stable, ['1', '2', '-3'], target, m)

    def test_mutated_modes_nonintegral_eigenvalues_and_zero_rejected(self):
        m = Meter(); potential = absent(3)
        for u, v in (('11/6', '1'), ('1', '-1'), ('1/2', '1'), ('2', '1')):
            with self.assertRaises(ValueError): C.verify_mode(potential, u, v, m)
        damaged = potential[:]; damaged[14] = '1'
        with self.assertRaises(ValueError): C.verify_mode(damaged, '1', '1', m)
        with self.assertRaises(ValueError): C.verify_mode(['0'] * 16, '0', '0', m)

    def test_complete_formal_kernel_all_masks_and_boundaries(self):
        m = Meter(); potential = [str(Q(mask - 7, 3)) for mask in range(16)]
        for X, q, h, k in ((1, 2, 1, 1), (4, 3, 1, 5), (4, 3, 5, 1),
                            (8, 5, 3, 7), (4, 3, 8, 1), (4, 3, 1, 8)):
            for mask in range(16):
                record = C.verify_kernel(potential, X, q, h, k, mask, m)
                m.charge(6)
                self.assertEqual(record['W'], max(0, 2 * X - max(X, h, k)))
                self.assertEqual(record['W_L'], max(0, 2 * X - max(X, q * h, k)))
                self.assertEqual(record['W_R'], max(0, 2 * X - max(X, h, q * k)))
                self.assertEqual(record['formal_pair'], record['recomposed'])
                self.assertEqual(record['left_exit_count'], record['W'] - record['W_L'])
                self.assertEqual(record['right_exit_count'], record['W'] - record['W_R'])
                self.assertTrue(record['exact_identity_verified']); self.assertFalse(record['full_target_recovered'])
                for z in (Q(1, 2), Q(2, 3)):
                    r, s = 1 - z ** 2, 1 - z ** 4; m.charge(12)
                    f = list(map(Q, potential))
                    pair = f[mask] * record['W'] - (r * f[mask | 1] + s * f[mask | 2]) * record['W_L'] - (r * f[mask | 4] + s * f[mask | 8]) * record['W_R']
                    self.assertEqual(polynomial(record['formal_pair'], z, m), pair)
                    self.assertEqual(pair, polynomial(record['bulk_part'], z, m) + polynomial(record['left_exit'], z, m) + polynomial(record['right_exit'], z, m))

    def test_units_one_orientation_exits_and_outside_support(self):
        m = Meter(); f = ['1'] * 16
        unit = C.verify_kernel(f, 1, 2, 1, 1, 0, m)
        self.assertEqual((unit['W'], unit['W_L'], unit['W_R']), (1, 0, 0))
        left = C.verify_kernel(f, 4, 3, 1, 5, 0, m)
        right = C.verify_kernel(f, 4, 3, 5, 1, 0, m)
        self.assertEqual((left['left_exit_count'], left['right_exit_count']), (0, 3))
        self.assertEqual((right['left_exit_count'], right['right_exit_count']), (3, 0))
        outside = C.verify_kernel(f, 4, 3, 8, 1, 15, m)
        self.assertEqual(outside['formal_pair'], ['0', '0', '0'])
        self.assertEqual(outside['left_exit'], ['0', '0', '0'])
        self.assertEqual(outside['right_exit'], ['0', '0', '0'])

    def test_exact_coordinate_recovery_keeps_every_mask(self):
        m = Meter(); first = absent(3, '1/3'); second = absent(5, '-2/3')
        m.charge(32); target = [str(2 * Q(a) - Q(b)) for a, b in zip(first, second)]
        record = C.verify_recovery([first, second], ['2', '-1'], target, m)
        self.assertEqual(record['reconstructed'], target); self.assertTrue(record['exact_linear_recovery_verified'])
        self.assertFalse(record['whole_signed_bound_proved'])
        damaged = target[:]; damaged[15] = '1'
        with self.assertRaises(ValueError): C.verify_recovery([first, second], ['2', '-1'], damaged, m)
        with self.assertRaises(ValueError): C.verify_recovery([first], ['2', '1'], target, m)

    def test_strict_shapes_rationals_and_fresh_prime_fixture_domain(self):
        m = Meter()
        for f in (['1'] * 15, ['1'] * 17, [1] * 16, ['2/4'] * 16, ['1/0'] * 16, ['0.5'] * 16, [True] * 16):
            with self.assertRaises(ValueError): C.verify_mode(f, '2', '2', m)
        f = ['1'] * 16
        for X, q, h, k, mask in ((0, 2, 1, 1, 0), (257, 2, 1, 1, 0), (True, 2, 1, 1, 0),
                                  (4, 1, 1, 1, 0), (4, 4, 1, 1, 0), (4, 3, 3, 1, 0),
                                  (4, 3, 1, 6, 0), (4, 3, 0, 1, 0), (4, 3, 1, 1, 16), (4, 3, 1, 1, True)):
            with self.assertRaises(ValueError): C.verify_kernel(f, X, q, h, k, mask, m)


    def test_literal_bernstein_quadratic_complete_partition(self):
        m = Meter(); poly = [[0, '1'], [2, '-1']]
        # p(z)=1-z^2; degree2 local Bernstein values are
        # [1-left^2,1-left*right,1-right^2].
        segments = [dict(left='0', right='1/2', coefficients=['1', '1', '3/4']),
                    dict(left='1/2', right='9/10', coefficients=['3/4', '11/20', '19/100'])]
        record = C.verify_bernstein(poly, segments, m)
        self.assertTrue(record['verified']); self.assertTrue(record['prime_root_domain_included'])
        self.assertTrue(record['algebraic_envelope_only']); self.assertFalse(record['energy_contraction_proved'])
        zero = C.verify_bernstein([], [dict(left='0', right='9/10', coefficients=['0'])], m)
        self.assertTrue(zero['verified'])
        single = C.verify_bernstein([[0, '1']], [dict(left='0', right='9/10', coefficients=['1'])], m)
        self.assertFalse(single['whole_signed_bound_proved'])

    def test_bernstein_mutation_coverage_and_coefficient_bound_rejected(self):
        m = Meter(); p = [[0, '1'], [2, '-1']]
        for segments in ([dict(left='0', right='9/10', coefficients=['1', '1', '1/5'])],
                         [dict(left='0', right='1/2', coefficients=['1', '1', '3/4'])],
                         [dict(left='1/10', right='9/10', coefficients=['1', '1', '19/100'])],
                         [dict(left='0', right='9/10', coefficients=['2', '1', '19/100'])],
                         [dict(left='0', right='9/10', coefficients=['1', '19/100'])],
                         [dict(left='0', right='9/10', coefficients=['1', '1', '19/100'], extra=1)]):
            with self.assertRaises(ValueError): C.verify_bernstein(p, segments, m)
        for poly in ([[0, '0']], [[True, '1']], [[25, '1']], [[1, '1'], [0, '1']], [[0, 1]], [[0, '2/4']]):
            with self.assertRaises(ValueError): C.verify_bernstein(poly, [dict(left='0', right='9/10', coefficients=['1'])], m)

    def test_shared_meter_and_resource_cap(self):
        m = Meter(); f = absent(3)
        C.verify_mode(f, '1', '1', m); initial = m.operations
        C.verify_kernel(f, 4, 3, 1, 5, 0, m)
        self.assertGreater(m.operations, initial)
        with self.assertRaises(OverflowError): C.verify_mode(f, '1', '1', Meter(cap=1))


if __name__ == '__main__': unittest.main()
