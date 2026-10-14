"""Independent tiny expectations, domain checks and producer parity checks."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest

import check_permuted_arithmetic_circuits as CHECK
import permuted_arithmetic_circuits as PRODUCER
from potential_candidate_language import Meter


METERS = [Meter(950000)]
WORK = METERS[0]
PLUS = ['constant', 1]
MINUS = ['constant', -1]
IDENTITY = {'kind': 'polynomial', 'coefficients': [0, 1, 0]}
POLYNOMIAL = {'kind': 'polynomial', 'coefficients': [0, 1, 2]}
XOR = {'kind': 'xor', 'mask': 'all'}
REVERSE = {'kind': 'reverse_bits'}


def word(*stages):
    return dict(stages=list(stages))


def convolve(alpha='1/6', phase=PLUS):
    return dict(op='convolve', alpha=alpha, prime_phase=deepcopy(phase))


def sign(phase=MINUS):
    return dict(op='sign', phase=deepcopy(phase))


def permute(descriptor=POLYNOMIAL, inverse=False):
    return dict(op='permute', map=deepcopy(descriptor), inverse=inverse)


def shear(coefficient='1/2', direction='even_from_odd', phase=PLUS):
    return dict(op='shear', coefficient=coefficient, direction=direction, phase=deepcopy(phase))


def signal(horizon):
    pattern = [1, -1, 0, 1, 0, -1, 1]
    WORK.charge(horizon + 1)
    return [0] + [pattern[(n - 1) % len(pattern)] for n in range(1, horizon + 1)]


def vector(horizon):
    WORK.charge(horizon + 1)
    return list(range(horizon + 1))


def limited_meter(limit, **kwargs):
    result = Meter(limit, **kwargs)
    METERS.append(result)
    return result


def certificate(program, order, power, permutations=0, shears=0, factor='1'):
    return dict(schema=CHECK.SCHEMA, program=deepcopy(program), fractional_order=order,
                recovery_power=power, permutation_count=permutations, shear_count=shears,
                shear_factor=factor, domain=CHECK.DOMAIN, bound=CHECK.BOUND,
                coefficient_binding=CHECK.BINDING)


class PermutedCheckerTests(unittest.TestCase):
    def test_closed_horizons_including_baseline_and_source(self):
        for horizon in (2, 4, 5, 6, 8, 62):
            values = signal(horizon)
            with self.subTest(horizon=horizon):
                with self.assertRaises(ValueError):
                    CHECK.evaluate(word(), values, WORK)
                with self.assertRaises(ValueError):
                    CHECK.source('one', horizon, WORK)
        with self.assertRaises(ValueError):
            CHECK.source('one', True, WORK)
        self.assertEqual(CHECK.source('one', 3, WORK), [0, 1, 1, 1])
        self.assertEqual(CHECK.source('mu', 7, WORK), [0, 1, -1, -1, 0, -1, 1, -1])

    def test_malformed_polynomials_and_map_types(self):
        invalid = [dict(kind='polynomial', coefficients=[0, 2, 2]),
                   dict(kind='polynomial', coefficients=[0, 1, 1]),
                   dict(kind='polynomial', coefficients=[0, True, 2]),
                   dict(kind='polynomial', coefficients=[9, 1]),
                   dict(kind='polynomial', coefficients=[0]),
                   dict(kind='xor', mask='bottom'),
                   dict(kind='reverse_bits', extra=0),
                   dict(kind='rotate_bits', shift=0),
                   dict(kind='rotate_bits', shift=True),
                   dict(kind='rotate_bits', shift=5),
                   dict(kind='compose', maps=[XOR]),
                   dict(kind='choose', phase=PLUS, positive=XOR)]
        for descriptor in invalid:
            with self.subTest(kind=descriptor['kind']):
                with self.assertRaises(ValueError):
                    CHECK.validate(word(permute(descriptor)), WORK)
        with self.assertRaises(ValueError):
            CHECK.validate(word(permute(XOR, inverse=0)), WORK)

    def test_map_node_and_depth_bounds(self):
        nested = deepcopy(XOR)
        for _ in range(4):
            nested = dict(kind='compose', maps=[nested, deepcopy(XOR)])
        with self.assertRaises(ValueError):
            CHECK.validate(word(permute(nested)), WORK)
        wide = dict(kind='compose', maps=[dict(kind='compose', maps=[deepcopy(XOR) for _ in range(3)])
                                         for _ in range(3)])
        wide['maps'][0]['maps'][0] = dict(kind='compose', maps=[deepcopy(XOR) for _ in range(3)])
        with self.assertRaises(ValueError):
            CHECK.validate(word(permute(wide)), WORK)

    def test_recovery_metadata_fractional_order_shear_and_strict_types(self):
        program = word(convolve('1/6'), permute(), convolve('-1/3'), shear('-1/2'))
        good = certificate(program, '1/2', 1, permutations=1, shears=1, factor='2')
        self.assertTrue(CHECK.verify(good, WORK))
        for field, bad in [('fractional_order', '3/6'), ('recovery_power', 2),
                           ('recovery_power', True), ('permutation_count', True),
                           ('shear_count', True), ('shear_factor', '2/1'),
                           ('domain', 'open_horizon'), ('coefficient_binding', 'current_state')]:
            forged = deepcopy(good)
            forged[field] = bad
            with self.subTest(field=field):
                with self.assertRaises(ValueError):
                    CHECK.verify(forged, WORK)
        base = certificate(word(), '0', 0)
        base['permutation_count'] = False
        with self.assertRaises(ValueError):
            CHECK.verify(base, WORK)

    def test_strict_stage_schema_phase_and_source(self):
        invalid = [word(convolve('0')), word(convolve('2/4')),
                   word(shear('0')), word(shear(direction='both')),
                   word(sign(['constant', True])),
                   word(sign(['source_sign', ['root', 2, 4]])),
                   word(*[convolve() for _ in range(4)]),
                   word(*[shear() for _ in range(3)]),
                   word(*[sign() for _ in range(4)])]
        for program in invalid:
            with self.assertRaises(ValueError):
                CHECK.validate(program, WORK)
        with self.assertRaises(ValueError):
            CHECK.evaluate(word(), [0, 1, True, 0], WORK)
        with self.assertRaises(ValueError):
            CHECK.evaluate(word(), [0, 1, Q(0), 0], WORK)

    def test_independent_polynomial_bit_and_composition_values(self):
        values = signal(7)
        initial = vector(7)
        poly = CHECK.apply_to_state(word(permute()), values, initial, WORK)
        self.assertEqual(poly, [0, 1, 2, 3, 4, 7, 6, 5])
        xor = CHECK.apply_to_state(word(permute(XOR)), values, initial, WORK)
        self.assertEqual(xor, [0, 1, 3, 2, 7, 6, 5, 4])
        reverse = CHECK.apply_to_state(word(permute(REVERSE)), values, initial, WORK)
        self.assertEqual(reverse, [0, 1, 2, 3, 4, 6, 5, 7])
        composed = dict(kind='compose', maps=[POLYNOMIAL, XOR])
        result = CHECK.apply_to_state(word(permute(composed)), values, initial, WORK)
        self.assertEqual(result, [0, 1, 3, 2, 7, 4, 5, 6])

    def test_rotate_leading_bits_and_inverse(self):
        values = signal(15)
        initial = vector(15)
        program = word(permute(dict(kind='rotate_bits', shift=1)))
        result = CHECK.apply_to_state(program, values, initial, WORK)
        self.assertEqual(result[8:], [8, 10, 12, 14, 9, 11, 13, 15])
        self.assertEqual(CHECK.apply_to_state(CHECK.inverse(program, WORK), values, result, WORK), initial)

    def test_choose_uses_original_source_at_block_base_in_inverse(self):
        values = [0, 1, 1, 0, -1, 1, 1, 1]
        initial = vector(7)
        descriptor = dict(kind='choose', phase=['source_sign', ['n']],
                          positive=IDENTITY, negative=XOR)
        program = word(permute(descriptor))
        result = CHECK.apply_to_state(program, values, initial, WORK)
        self.assertEqual(result, [0, 1, 2, 3, 7, 6, 5, 4])
        self.assertGreater(result[4], 0)
        self.assertEqual(CHECK.apply_to_state(CHECK.inverse(program, WORK), values, result, WORK), initial)

    def test_shear_expected_signed_envelope_and_inverse(self):
        values = [0, 1, -1, 1]
        program = word(shear('1/2', phase=MINUS))
        state = CHECK.evaluate(program, values, WORK)
        self.assertEqual(state, dict(signed=[0, 1, Q(-1, 2), 1],
                                     absolute=[0, 1, Q(1, 2), 1]))
        restored = CHECK.apply_to_state(CHECK.inverse(program, WORK), values, state['signed'], WORK)
        self.assertEqual(restored, [0, 1, 0, 1])
        initial = [0, 1, 2, 3]
        opposite = word(shear('-1/2', direction='odd_from_even', phase=MINUS))
        self.assertEqual(CHECK.apply_to_state(opposite, values, initial, WORK), [0, 1, 2, 4])

    def test_mixed_stages_inverse_and_path_envelope(self):
        values = signal(31)
        chosen = dict(kind='choose', phase=['source_sign', ['n']],
                      positive=dict(kind='polynomial', coefficients=[1, 1, 2]),
                      negative=dict(kind='compose', maps=[REVERSE, dict(kind='xor', mask='top')]))
        program = word(convolve('-1/3', ['source_sign', ['root', 1, 2]]), permute(chosen),
                       sign(['source_sign', ['subtract_root', 1, 2]]),
                       shear('1/3', phase=['source_sign', ['root', 1, 2]]),
                       convolve('1/6', ['residue_sign', ['n'], 5, [1, 4]]),
                       permute(dict(kind='rotate_bits', shift=-1)),
                       shear('-1/2', 'odd_from_even', ['parity', ['quotient', 2]]))
        state = CHECK.evaluate(program, values, WORK)
        self.assertTrue(all(abs(a) <= b for a, b in zip(state['signed'], state['absolute'])))
        restored = CHECK.apply_to_state(CHECK.inverse(program, WORK), values, state['signed'], WORK)
        WORK.charge(len(values))
        total = 0
        expected = [0]
        for value in values[1:]:
            total = WORK.number(total + value)
            expected.append(total)
        self.assertEqual(restored, expected)
        self.assertEqual(PRODUCER.evaluate(program, values, WORK), state)

    def test_normalizer_rule_order_zero_merges_and_trace_copies(self):
        program = word(permute(IDENTITY), convolve('1/6'), convolve('-1/6'),
                       sign(), sign(), permute(XOR), permute(XOR, inverse=True))
        original = deepcopy(program)
        result = CHECK.normalize(program, WORK)
        self.assertEqual(result['program'], word())
        self.assertEqual([r['rule'] for r in result['rewrites']],
                         ['identity_permutation', 'merge_convolutions',
                          'inverse_signs', 'inverse_permutations'])
        self.assertTrue(all(r['position'] == 0 and r['after'] == [] for r in result['rewrites']))
        self.assertEqual(PRODUCER.normalize(program, WORK), result)
        result['rewrites'][0]['before'][0]['map']['coefficients'][0] = 8
        self.assertEqual(program, original)

    def test_shear_merges_terminal_aliases_and_blocked_merges(self):
        program = word(shear('1/6'), shear('1/3'), convolve())
        result = CHECK.normalize(program, WORK)
        self.assertEqual(result['program'], word(shear('1/2'), convolve()))
        self.assertEqual(result['rewrites'][0]['rule'], 'merge_shears')
        result['rewrites'][0]['after'][0]['coefficient'] = '2'
        self.assertEqual(result['program']['stages'][0]['coefficient'], '1/2')
        zero = CHECK.normalize(word(shear('1/6'), shear('-1/6')), WORK)
        self.assertEqual(zero['rewrites'][0]['rule'], 'merge_shears')
        self.assertEqual(zero['rewrites'][0]['after'], [])
        terminal = CHECK.normalize(word(convolve(), permute(XOR), sign()), WORK)
        self.assertEqual([r['rule'] for r in terminal['rewrites']],
                         ['terminal_sign', 'terminal_dyadic_permutation'])
        self.assertEqual(terminal['program'], word(convolve()))
        for blocked in [word(convolve('2'), convolve('1/2')),
                        word(convolve('1/4'), convolve('1/5')),
                        word(permute(XOR), permute(XOR), convolve()),
                        word(shear(), shear(direction='odd_from_even'))]:
            self.assertEqual(CHECK.normalize(blocked, WORK)['program'], blocked)

    def test_terminal_permutation_preserves_dyadic_moments_only(self):
        values = signal(7)
        raw = word(convolve('-1/3'), permute(XOR))
        normalized = CHECK.normalize(raw, WORK)['program']
        first = CHECK.evaluate(raw, values, WORK)
        second = CHECK.evaluate(normalized, values, WORK)
        self.assertEqual(CHECK.moments(first, [1, 2, 4], WORK),
                         CHECK.moments(second, [1, 2, 4], WORK))
        self.assertNotEqual(first['signed'], second['signed'])

    def test_moments_initial_head_and_malformed_state(self):
        state = CHECK.evaluate(word(), CHECK.source('one', 7, WORK), WORK)
        self.assertEqual(CHECK.moments(state, [1, 2, 4], WORK),
                         [dict(X=1, energy='1', absolute_energy='1'),
                          dict(X=2, energy='13/4', absolute_energy='13/4'),
                          dict(X=4, energy='63/8', absolute_energy='63/8')])
        with self.assertRaises(ValueError):
            CHECK.initial_cost(state, WORK)
        head = CHECK.evaluate(word(), CHECK.source('one', 31, WORK), WORK)
        self.assertEqual(CHECK.initial_cost(head, WORK), '31')
        for scales in ([True], [2, 2], [5]):
            with self.assertRaises(ValueError):
                CHECK.moments(state, scales, WORK)
        forged = deepcopy(state)
        forged['absolute'][2] = 1
        with self.assertRaises(ValueError):
            CHECK.moments(forged, [2], WORK)
        forged = deepcopy(state)
        forged['signed'][0] = False
        with self.assertRaises(ValueError):
            CHECK.initial_cost(forged, WORK)

    def test_decomposition_keeps_raw_remaining_permutation(self):
        values = [0, 1, 1, 1]
        program = word(permute(XOR), convolve('1'))
        state = CHECK.evaluate(program, values, WORK)
        self.assertEqual(state['signed'], [0, 1, 4, 3])
        expected = [dict(X=1, diagonal_energy='1', lower_energy='0', mixed_energy='0', total_energy='1'),
                    dict(X=2, diagonal_energy='13/4', lower_energy='1/2',
                         mixed_energy='5/2', total_energy='25/4')]
        self.assertEqual(CHECK.decomposition(program, values, state, [1, 2], WORK), expected)
        self.assertEqual(PRODUCER.decomposition(program, values, state, [1, 2], WORK), expected)

    def test_decomposition_shear_and_invalid_scales(self):
        values = [0, 1, 1, 1]
        program = word(permute(XOR), shear(), convolve('1'))
        state = CHECK.evaluate(program, values, WORK)
        self.assertEqual(CHECK.decomposition(program, values, state, [2], WORK),
                         [dict(X=2, diagonal_energy='5', lower_energy='1/2',
                               mixed_energy='3', total_energy='17/2')])
        baseline = CHECK.evaluate(word(), signal(7), WORK)
        for scales in ([3], [True], [2, 2], [8]):
            with self.assertRaises(ValueError):
                CHECK.decomposition(word(), signal(7), baseline, scales, WORK)

    def test_producer_checker_map_normalizer_and_metadata_parity(self):
        values = signal(15)
        descriptors = [dict(kind='xor', mask='alternating'),
                       dict(kind='polynomial', coefficients=[-3, -1, 2, -4, 6]),
                       dict(kind='compose', maps=[XOR, REVERSE, POLYNOMIAL])]
        for descriptor in descriptors:
            program = word(permute(descriptor), convolve('-1/6'), shear('1/3'))
            self.assertTrue(CHECK.verify(PRODUCER.certificate(program, WORK), WORK))
            self.assertEqual(CHECK.evaluate(program, values, WORK), PRODUCER.evaluate(program, values, WORK))
            self.assertEqual(CHECK.normalize(program, WORK), PRODUCER.normalize(program, WORK))
        program = word(shear('-1/3'), shear('1/6'), convolve('1/6'), convolve('1/3'), sign())
        self.assertEqual(CHECK.normalize(program, WORK), PRODUCER.normalize(program, WORK))

    def test_operation_and_number_caps_preserve_spent_work(self):
        tiny = limited_meter(1)
        with self.assertRaises(OverflowError):
            CHECK.validate(word(), tiny)
        self.assertEqual(tiny.operations, 1)
        narrow = limited_meter(10000, max_bits=2)
        with self.assertRaises(OverflowError):
            CHECK.evaluate(word(), [0, 1, 1, 1, 1, 1, 1, 1], narrow)
        self.assertGreater(narrow.operations, 0)


def tearDownModule():
    operations = sum(meter.operations for meter in METERS)
    print('SYNTHETIC_WORK module=test_check_permuted_arithmetic_circuits operations=' + str(operations))


if __name__ == '__main__':
    unittest.main()
