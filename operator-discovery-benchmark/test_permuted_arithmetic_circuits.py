"""Small synthetic checks of new arithmetic semantics and recovery boundaries."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest

import permuted_arithmetic_circuits as L

WORK = 0


def tearDownModule():
    print('SYNTHETIC_WORK module=test_permuted_arithmetic_circuits operations=' + str(WORK))


def perm(mapping, inverse=False):
    return dict(op='permute', map=mapping, inverse=inverse)


def conv(alpha='1/3', phase=None):
    return dict(op='convolve', alpha=alpha, prime_phase=phase or ['constant', 1])


def shear(c='-1', direction='even_from_odd', phase=None):
    return dict(op='shear', coefficient=c, phase=phase or ['constant', 1], direction=direction)


MAPS = [
    {'kind': 'polynomial', 'coefficients': [3, -3, 2, -4, 6]},
    {'kind': 'xor', 'mask': 'all'}, {'kind': 'xor', 'mask': 'top'},
    {'kind': 'xor', 'mask': 'alternating'}, {'kind': 'reverse_bits'},
    {'kind': 'rotate_bits', 'shift': -2},
    {'kind': 'compose', 'maps': [
        {'kind': 'polynomial', 'coefficients': [1, 3, 2]}, {'kind': 'reverse_bits'}]},
    {'kind': 'choose', 'phase': ['source_sign', ['quotient', 2]],
     'positive': {'kind': 'polynomial', 'coefficients': [2, 3]},
     'negative': {'kind': 'xor', 'mask': 'all'}}]


class ArithmeticCircuitTests(unittest.TestCase):
    def setUp(self):
        self.meters = []

    def tearDown(self):
        global WORK
        WORK += sum(m.operations for m in self.meters)

    def meter(self, limit=500000):
        meter = L.Meter(limit)
        self.meters.append(meter)
        return meter

    def test_all_map_families_are_closed_bijections_and_invert_exactly(self):
        m = self.meter()
        for H in (1, 3, 7, 15, 31, 63):
            values = [0] + [(-1, 0, 1, -1, 1)[n % 5] for n in range(1, H + 1)]
            state = list(range(H + 1))
            for mapping in MAPS:
                program = {'stages': [perm(deepcopy(mapping))]}
                transformed = L.apply_to_state(program, values, state, m)
                self.assertEqual(L.apply_to_state(L.inverse(program, m), values, transformed, m), state)
                for k in range((H + 1).bit_length() - 1):
                    block = 1 << k
                    self.assertEqual(sorted(transformed[block:2 * block]), state[block:2 * block])

    def test_explicit_pullback_composition_order_and_leading_bits(self):
        m = self.meter()
        values, state = [0] + [1] * 15, list(range(16))
        mapping = {'kind': 'compose', 'maps': [
            {'kind': 'polynomial', 'coefficients': [1, 1]}, {'kind': 'reverse_bits'}]}
        result = L.apply_to_state({'stages': [perm(mapping)]}, values, state, m)
        # r=0 -> r=1 -> reverse exactly three bits to4, hence index12.
        self.assertEqual(result[8], 12)
        self.assertEqual(result[15], 8)
        rotated = L.apply_to_state({'stages': [perm({'kind': 'rotate_bits', 'shift': 1})]}, values, state, m)
        self.assertEqual(rotated[9], 10)
        self.assertEqual(rotated[12], 9)

    def test_complete_shear_pair_and_absolute_envelope_hand_example(self):
        m = self.meter()
        values = [0, 1, -1, 1, 0, -1, 1, 0]
        result = L.evaluate({'stages': [shear()]}, values, m)
        self.assertEqual(result, dict(signed=[0, 1, -1, 1, 1, 0, 0, 1],
                                     absolute=[0, 1, 1, 1, 1, 0, 2, 1]))
        self.assertEqual(L.moments(result, [4], m), [dict(X=4, energy='1/8', absolute_energy='3/8')])
        # Dropping the unchanged odd coordinates would falsely produce a smaller energy.
        for direction in ('even_from_odd', 'odd_from_even'):
            word = {'stages': [shear('1/6', direction, ['source_sign', ['n']])]}
            out = L.evaluate(word, values, m)
            recovered = L.apply_to_state(L.inverse(word, m), values, out['signed'], m)
            self.assertEqual(recovered, [0, 1, 0, 1, 1, 0, 1, 1])

    def test_mixed_fractional_word_recovers_same_original_source(self):
        m = self.meter()
        values = [0] + [(-1, 1, 0, 1, -1, 0, -1)[n % 7] for n in range(1, 64)]
        word = {'stages': [
            conv('-1/6', ['source_sign', ['subtract_root', 1, 2]]),
            perm(deepcopy(MAPS[-1])), shear('1/2', 'odd_from_even', ['parity', ['root', 2, 3]]),
            {'op': 'sign', 'phase': ['source_sign', ['root', 1, 3]]},
            perm(deepcopy(MAPS[0]), True), conv('1/3', ['residue_sign', ['n'], 5, [1, 4]])]}
        before = deepcopy(values)
        result = L.evaluate(word, values, m)
        recovered = L.apply_to_state(L.inverse(word, m), values, result['signed'], m)
        prefix = [0]
        for v in values[1:]:
            prefix.append(prefix[-1] + v)
        self.assertEqual(recovered, prefix)
        self.assertEqual(values, before)
        self.assertTrue(all(abs(a) <= b for a, b in zip(result['signed'], result['absolute'])))
        self.assertTrue(any(abs(a) < b for a, b in zip(result['signed'], result['absolute'])))

    def test_normalization_exact_merges_and_inverse_traces(self):
        m = self.meter()
        p = perm(deepcopy(MAPS[0]))
        sign = {'op': 'sign', 'phase': ['parity', ['root', 1, 6]]}
        raw = {'stages': [conv('1/6'), conv('-1/6'), p, perm(deepcopy(MAPS[0]), True), sign, sign]}
        normal = L.normalize(raw, m)
        self.assertEqual(normal['program'], {'stages': []})
        self.assertEqual([r['rule'] for r in normal['rewrites']],
                         ['merge_convolutions', 'inverse_permutations', 'inverse_signs'])
        merged = L.normalize({'stages': [shear('1/3'), shear('1/6'), conv('1/2')]}, m)
        self.assertEqual(merged['program']['stages'][0]['coefficient'], '1/2')
        cancelled = L.normalize({'stages': [shear('1/2'), shear('-1/2'), conv()]}, m)
        self.assertEqual(cancelled['program'], {'stages': [conv()]})
        self.assertEqual(raw['stages'][0]['alpha'], '1/6')

    def test_terminal_permutation_alias_is_only_dyadic(self):
        m = self.meter()
        values = [0] + [1] * 15
        word = {'stages': [perm({'kind': 'xor', 'mask': 'all'})]}
        normal = L.normalize(word, m)
        self.assertEqual(normal['equivalence'], 'dyadic_moments')
        raw = L.evaluate(word, values, m)
        plain = L.evaluate(normal['program'], values, m)
        self.assertEqual(L.moments(raw, [2, 4, 8], m), L.moments(plain, [2, 4, 8], m))
        self.assertNotEqual(L.moments(raw, [3], m), L.moments(plain, [3], m))

    def test_recovery_fractional_order_and_shear_cost(self):
        m = self.meter()
        program = {'stages': [conv('-1/3'), perm(MAPS[0]), shear('-1/2'),
                              conv('1/6'), shear('1/3', 'odd_from_even')]}
        cert = L.certificate(program, m)
        self.assertEqual(cert['fractional_order'], '1/2')
        self.assertEqual(cert['recovery_power'], 1)
        self.assertEqual(cert['permutation_count'], 1)
        self.assertEqual(cert['shear_count'], 2)
        self.assertEqual(cert['shear_factor'], '10/3')
        cert['program']['stages'][0]['alpha'] = '1'
        self.assertEqual(program['stages'][0]['alpha'], '-1/3')

    def test_closed_horizon_and_complete_exact_envelope_required(self):
        m = self.meter()
        for values in ([0, 1, -1], [False, 1], [0, True], [0, 0.0]):
            with self.assertRaises(ValueError):
                L.evaluate({'stages': []}, values, m)
        with self.assertRaises(ValueError):
            L.source('one', 6, m)
        for state in (dict(signed=[0, 1], absolute=[0, 0]),
                      dict(signed=[0, True], absolute=[0, 1]),
                      dict(signed=[0, 1, 1], absolute=[0, 1, 1])):
            with self.assertRaises(ValueError):
                L.moments(state, [1], m)
        valid = dict(signed=[0] * 8, absolute=[0] * 8)
        for scales in ([True], [2, 2], [5]):
            with self.assertRaises(ValueError):
                L.moments(valid, scales, m)
        with self.assertRaises(ValueError):
            L.initial_cost(valid, m)

    def test_reject_nonbijective_maps_and_unbound_stage_fields(self):
        m = self.meter()
        invalid = [
            {'kind': 'polynomial', 'coefficients': [0, 2]},
            {'kind': 'polynomial', 'coefficients': [0, 1, 1]},
            {'kind': 'polynomial', 'coefficients': [0, True]},
            {'kind': 'rotate_bits', 'shift': 0}, {'kind': 'xor', 'mask': 1},
            {'kind': 'choose', 'phase': ['constant', 1], 'positive': MAPS[0], 'negative': MAPS[1], 'at': 'n'}]
        for mapping in invalid:
            with self.assertRaises(ValueError):
                L.validate({'stages': [perm(mapping)]}, m)
        for stage in (dict(op='permute', map=MAPS[0], inverse=1),
                      shear('2/4'), shear('0'), shear('1/7'), shear(direction='both')):
            with self.assertRaises(ValueError):
                L.validate({'stages': [stage]}, m)

    def test_initial_head_is_complete_and_fixed_across_closed_extensions(self):
        m = self.meter()
        values = [0] + [(-1, 0, 1)[n % 3] for n in range(1, 64)]
        word = {'stages': [perm(deepcopy(MAPS[-1])), shear('1/3'), conv('-1/6')]}
        short = L.evaluate(word, values[:32], m)
        long = L.evaluate(word, values, m)
        self.assertEqual(short['signed'], long['signed'][:32])
        self.assertEqual(L.initial_cost(short, m), L.initial_cost(long, m))
        expected = sum((Q(long['signed'][n] ** 2, n * n) for n in range(1, 32)), Q(0))
        self.assertEqual(L.initial_cost(long, m), str(expected))

    def test_full_fresh_lower_and_cross_terms_hand_example(self):
        m = self.meter()
        values = [0, 1, -1, 1, 0, -1, 1, 0]
        word = {'stages': [conv('1')]}
        state = L.evaluate(word, values, m)
        self.assertEqual(L.decomposition(word, values, state, [4], m), [
            dict(X=4, diagonal_energy='3/16', lower_energy='7/16', mixed_energy='1/2', total_energy='9/8')])
        with self.assertRaises(ValueError):
            L.decomposition(word, values, state, [3], m)


if __name__ == '__main__':
    unittest.main()
