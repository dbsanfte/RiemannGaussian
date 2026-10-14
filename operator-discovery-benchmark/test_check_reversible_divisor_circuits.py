"""Tiny independent exact circuit/inverse and admission counterexamples."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest
from unittest.mock import patch

import check_reversible_divisor_circuits as C


def convolution(alpha, phase=None):
    return dict(op='convolve', alpha=alpha,
                prime_phase=['constant', 1] if phase is None else deepcopy(phase))


def sign(phase):
    return dict(op='sign', phase=deepcopy(phase))


def program(*stages):
    return dict(stages=list(stages))


def certificate(candidate):
    orders = []
    for stage in candidate['stages']:
        if stage['op'] == 'convolve':
            alpha = abs(Q(stage['alpha']))
            orders.append((alpha.numerator + alpha.denominator - 1) // alpha.denominator)
    return dict(schema='reversible-divisor-circuit-v1', program=deepcopy(candidate),
        convolution_orders=orders, recovery_power=sum(orders),
        domain='discrete_weighted_l2_sigma_gt_half',
        bound='(1+1/epsilon)^recovery_power',
        coefficient_binding='same_fixed_source_in_all_stages_and_inverse')


class Checks(unittest.TestCase):
    meters = []

    @classmethod
    def tearDownClass(cls):
        total = sum(m.operations for m in cls.meters)
        print('SYNTHETIC_WORK module=test_check_reversible_divisor_circuits operations=%d' % total)
        if total > 2000000:
            raise AssertionError('owned circuit development exceeds2m')

    def meter(self, cap=1000000, **kwargs):
        meter = C.Meter(cap, **kwargs)
        self.meters.append(meter)
        return meter

    def test_independent_factor_sources_and_control_boundary(self):
        meter = self.meter()
        mu = C.source('mu', 64, meter)
        self.assertEqual(mu[:17], [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0])
        control = C.source('partial_prime_13', 64, meter)
        self.assertEqual(control[:17], mu[:17])
        self.assertEqual((mu[17], control[17], mu[34], control[34], control[49]), (-1, 1, 1, -1, 0))
        self.assertEqual(C.source('one', 8, meter), [0] + [1] * 8)

    def test_baseline_prefix_and_full_exact_moments(self):
        meter = self.meter()
        values = C.source('one', 8, meter)
        output = C.evaluate(program(), values, meter)
        self.assertEqual(output, list(range(9)))
        self.assertEqual(C.moments(output, [1, 2, 4], meter),
                         [dict(X=1, energy='1'), dict(X=2, energy='13/4'), dict(X=4, energy='63/8')])
        self.assertEqual(C.moments(output, [], meter), [])
        self.assertEqual(values, [0] + [1] * 8)

    def test_negative_fractional_euler_coefficients_and_all_divisors(self):
        meter = self.meter()
        # A coefficient impulse at1 gives prefix input1 at every positive n.
        values = [0, 1] + [0] * 7
        output = C.evaluate(program(convolution('-1/2')), values, meter)
        self.assertEqual([output[1], output[2], output[4], output[8]],
                         [Q(1), Q(1, 2), Q(3, 8), Q(5, 16)])
        self.assertEqual([output[2] - output[1], output[4] - output[2], output[8] - output[4]],
                         [Q(-1, 2), Q(-1, 8), Q(-1, 16)])
        self.assertEqual(output[6], Q(1, 4))
        self.assertEqual(C.moments(output, [3], meter), [dict(X=3, energy='41/576')])
        altered = C.evaluate(program(convolution('-1/2', ['constant', -1])), values, meter)
        self.assertEqual([altered[2], altered[4], altered[8]], [Q(3, 2), Q(11, 8), Q(23, 16)])

    def test_fractional_inverse_composition_with_fixed_source_phases(self):
        meter = self.meter()
        values = C.source('mu', 64, meter)
        prime_phase = ['multiply', ['source_sign', ['n']], ['parity', ['quotient', 2]]]
        phase = ['multiply', ['source_sign', ['subtract_root', 1, 2]],
                 ['residue_sign', ['remainder', 7], 5, [0, 2, 4]]]
        # Circuit C_alpha,S followed by its reversed inverse S,C_-alpha.
        composed = program(convolution('1/2', prime_phase), sign(phase), sign(phase),
                           convolution('-1/2', prime_phase))
        self.assertTrue(C.verify(certificate(composed), meter))
        self.assertEqual(C.evaluate(composed, values, meter), C.evaluate(program(), values, meter))
        # Three Euler convolution exponents sum tozero, with the same chi.
        group_identity = program(convolution('1/2', prime_phase), convolution('-3/2', prime_phase),
                                 convolution('1', prime_phase))
        self.assertEqual(C.evaluate(group_identity, values, meter), C.evaluate(program(), values, meter))
        wrong_inverse = program(convolution('1/2'), convolution('-1/2', ['constant', -1]))
        self.assertNotEqual(C.evaluate(wrong_inverse, values, meter), C.evaluate(program(), values, meter))

    def test_phase_queries_bind_original_source_not_intermediate_state(self):
        meter = self.meter()
        candidate = program(convolution('1/2'), sign(['source_sign', ['n']]))
        mu = C.source('mu', 8, meter)
        output = C.evaluate(candidate, mu, meter)
        # At2 the transformed state is+1/2; the original coefficient is-1.
        self.assertEqual(output[2], Q(-1, 2))
        one = C.source('one', 8, meter)
        self.assertEqual(C.evaluate(candidate, one, meter)[2], Q(5, 2))
        self.assertEqual(mu[2], -1)

    def test_exact_fractional_index_and_zero_query_domain(self):
        meter = self.meter()
        values = [0] * 65
        values[1], values[32], values[33] = 1, -1, 1
        out = C.evaluate(program(sign(['source_sign', ['root', 5, 6]])), values, meter)
        self.assertEqual((out[63], out[64]), (Q(1), Q(-1)))
        self.assertEqual(C.evaluate(program(sign(['source_sign', ['subtract_root', 5, 6]])),
                                    values, meter)[64], Q(-1))
        baseline = C.evaluate(program(), values, meter)
        always_zero = program(sign(['source_sign', ['subtract_root', 1, 1]]))
        self.assertEqual(C.evaluate(always_zero, values, meter), baseline)
        empty_residues = program(sign(['residue_sign', ['n'], 16, []]))
        self.assertEqual(C.evaluate(empty_residues, values, meter), baseline)
        remainder = C.evaluate(program(sign(['source_sign', ['remainder', 16]])), values, meter)
        self.assertEqual(remainder[64], baseline[64])

    def test_root_and_subtract_root_share_monotone_maps_across_stages(self):
        values = [0] + [1] * 64
        first = sign(['source_sign', ['root', 5, 6]])
        second = sign(['source_sign', ['subtract_root', 5, 6]])
        single_meter = self.meter()
        paired_meter = self.meter()
        single = C.evaluate(program(first), values, single_meter)
        paired = C.evaluate(program(first, second), values, paired_meter)
        self.assertEqual(single, list(range(65)))
        self.assertEqual(paired, single)
        # A second phase/stage shares the SAME exponent map; it pays only its
        # phase/sign traversal, rather than another entire root computation.
        self.assertLess(paired_meter.operations - single_meter.operations, 12 * 64 + 128)
        self.assertLessEqual(paired_meter.peak_live_cells, single_meter.peak_live_cells + 128)

    def test_sign_isometry_and_terminal_sign_validation(self):
        meter = self.meter()
        values = C.source('mu', 32, meter)
        phase = ['multiply', ['parity', ['root', 1, 3]], ['residue_sign', ['quotient', 3], 7, [1, 4]]]
        candidate = program(sign(phase))
        self.assertTrue(C.validate(candidate, meter))
        self.assertTrue(C.verify(certificate(candidate), meter))
        baseline = C.evaluate(program(), values, meter)
        transformed = C.evaluate(candidate, values, meter)
        self.assertEqual(C.moments(transformed, [1, 2, 4, 8, 16], meter),
                         C.moments(baseline, [1, 2, 4, 8, 16], meter))

    def test_certificate_order_power_and_tampering(self):
        meter = self.meter()
        candidate = program(convolution('1/2'), sign(['constant', -1]), convolution('-5/3'), convolution('2'))
        good = certificate(candidate)
        self.assertEqual(good['convolution_orders'], [1, 2, 2])
        self.assertEqual(good['recovery_power'], 5)
        self.assertTrue(C.verify(good, meter))
        for key, value in [('convolution_orders', [1, 1, 2]), ('convolution_orders', [True, 2, 2]),
                           ('recovery_power', 10), ('recovery_power', True), ('domain', 'sigma_gt_zero'),
                           ('bound', '1'), ('coefficient_binding', 'intermediate_state'), ('schema', 'other')]:
            bad = deepcopy(good)
            bad[key] = value
            with self.assertRaises(ValueError):
                C.verify(bad, meter)
        bad = deepcopy(good)
        bad['RH_proved'] = True
        with self.assertRaises(ValueError):
            C.verify(bad, meter)
        empty = certificate(program())
        self.assertEqual(empty['recovery_power'], 0)
        with patch.object(C, 'Meter', return_value=meter):
            self.assertTrue(C.verify(empty))

    def test_strict_program_and_phase_schema(self):
        meter = self.meter()
        for alpha in ('0', '01', '2/2', '1/7', '5/2', '-3', '1.0', '+1'):
            with self.assertRaises(ValueError):
                C.validate(program(convolution(alpha)), meter)
        invalid_phases = [
            ['constant', True], ['constant', 0], ['source_sign', ['root', 2, 4]],
            ['source_sign', ['root', 0, 1]], ['source_sign', ['root', 2, 1]],
            ['source_sign', ['quotient', 1]], ['source_sign', ['remainder', 17]],
            ['source_sign', ['X']], ['residue_sign', ['n'], 3, [1, 1]],
            ['residue_sign', ['n'], 3, [-1]], ['residue_sign', ['n'], 3, [3]],
            ['residue_sign', ['n'], 3, [True]], ['multiply', ['constant', 1]],
        ]
        for phase in invalid_phases:
            with self.assertRaises(ValueError):
                C.validate(program(sign(phase)), meter)
        for bad in ({'stages': [], 'extra': 0}, {'stages': ()},
                    program(*[convolution('1')] * 4), program(*[sign(['constant', 1])] * 3),
                    program(dict(op='convolve', alpha='1', prime_phase=['constant', 1], extra=0))):
            with self.assertRaises(ValueError):
                C.validate(bad, meter)

    def test_phase_nodes_and_depth_include_index_nodes(self):
        meter = self.meter()
        tree = ['constant', 1]
        for _ in range(4):
            tree = ['multiply', deepcopy(tree), deepcopy(tree)]
        self.assertTrue(C.validate(program(sign(tree)), meter))  #31 nodes.
        too_many = ['multiply', tree, ['constant', 1]]
        with self.assertRaises(ValueError):
            C.validate(program(sign(too_many)), meter)
        # Replace one constant leaf by a parity node AND its index: +1 node.
        counted_index = deepcopy(tree)
        counted_index[1][1][1][1] = ['parity', ['n']]
        with self.assertRaises(ValueError):
            C.validate(program(sign(counted_index)), meter)
        deep = ['constant', 1]
        for _ in range(6):
            deep = ['multiply', ['constant', 1], deep]
        self.assertTrue(C.validate(program(sign(deep)), meter))
        with self.assertRaises(ValueError):
            C.validate(program(sign(['multiply', ['constant', 1], deep])), meter)

    def test_invalid_source_output_scale_and_shared_resource_caps(self):
        meter = self.meter()
        for name, horizon in [('unknown', 4), ('mu', 0), ('one', True), ('mu', 131072)]:
            with self.assertRaises(ValueError):
                C.source(name, horizon, meter)
        for values in ([0], [1, 1], [False, 1], [0, True], [0, Q(1)], [0, 2]):
            with self.assertRaises(ValueError):
                C.evaluate(program(), values, meter)
        output = [Q(0), Q(1), Q(-1), Q(2)]
        for scales in ([0], [True], [3], [1, 1], (1,)):
            with self.assertRaises(ValueError):
                C.moments(output, scales, meter)
        for bad in ([False, 1], [0, '1'], [1, 1]):
            with self.assertRaises(ValueError):
                C.moments(bad, [1], meter)
        tiny = self.meter(cap=10)
        with self.assertRaises(OverflowError):
            C.source('mu', 64, tiny)
        used = tiny.operations
        self.assertGreater(used, 0)
        with self.assertRaises(OverflowError):
            C.source('mu', 64, tiny)
        self.assertGreaterEqual(tiny.operations, used)
        cells = self.meter(max_cells=1)
        with self.assertRaises(OverflowError):
            C.evaluate(program(), [0, 1], cells)
        self.assertGreater(cells.peak_live_cells, 1)
        bits = self.meter(max_bits=4)
        with self.assertRaises(OverflowError):
            C.source('mu', 32, bits)


if __name__ == '__main__':
    unittest.main()
