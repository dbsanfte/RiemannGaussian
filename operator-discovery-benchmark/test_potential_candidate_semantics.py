"""Tiny structural cases, with independent finite algebra calibration."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest
from unittest.mock import patch

import potential_candidate_language as L
import check_potential_candidate_discovery as FINITE
import potential_candidate_semantics as S

_METERS = []
_PRODUCER_METER = L.Meter
_CHECKER_METER = FINITE.Meter


class ProducerMeter(_PRODUCER_METER):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs); _METERS.append(self)


class CheckerMeter(_CHECKER_METER):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs); _METERS.append(self)


def setUpModule():
    global _PATCHES
    _PATCHES = [patch.object(L, 'Meter', ProducerMeter), patch.object(FINITE, 'Meter', CheckerMeter)]
    for item in _PATCHES:
        item.start()


def tearDownModule():
    for item in reversed(_PATCHES):
        item.stop()
    print('SYNTHETIC_WORK module=test_potential_candidate_semantics operations=' +
          str(sum(m.operations for m in _METERS)))


def meter(**kwargs):
    return L.Meter(1000000, **kwargs)


def program(tree, weight='1'):
    return dict(states=[dict(weight=weight, tree=tree)])


def prefix(endpoint=None, name='n'):
    return ['sum', name, ['int', 1], ['v', 't'] if endpoint is None else endpoint, ['x', ['v', name]]]


def lag(divisor=2):
    return prefix(['idiv', ['v', 't'], ['int', divisor]])


def root_prefix(base='t', a=1, b=2):
    return prefix(['root', ['v', base], a, b])


def annotations(result, kind):
    return [a for s in result['states'] for a in s['annotations'] if a['kind'] == kind]


class SemanticsTests(unittest.TestCase):
    def test_baseline_target_copy_lag_domains_and_multi_state(self):
        m = meter()
        self.assertEqual(S.analyze(dict(states=[]), m)['mechanism'], 'baseline')
        for divisor, expected in ((1, 'target_copy'), (2, 'lag'), (3, 'lag')):
            result = S.analyze(program(lag(divisor)), m)
            self.assertEqual(result['mechanism'], expected)
            item = annotations(result, 'prefix_identity')[0]
            self.assertEqual(item['divisor'], divisor)
            self.assertEqual(item['initial_core_potential'], '1' if divisor == 1 else '0')
            self.assertEqual(item['domain'], 'all integer X>=1' if divisor == 1
                             else 'positive X divisible by divisor')
        paired = dict(states=[dict(weight='1', tree=lag()), dict(weight='1', tree=root_prefix())])
        self.assertEqual(S.analyze(paired, m)['mechanism'], 'multi_state')

    def test_exact_lag_pairing_and_initial_exception_with_independent_source(self):
        m = meter(); checker_meter = FINITE.Meter(1000000)
        values = L.mobius(15, m); evaluator = L.Evaluator(values, m)
        checker = FINITE.Checker(15, checker_meter)
        for divisor, X in ((2, 4), (3, 6)):
            value = program(lag(divisor))
            result = evaluator.measure(value, X)
            self.assertEqual(result, checker.measure(value, X))
            baseline = checker.measure(dict(states=[]), X // divisor)
            self.assertEqual(Q(result['V']), Q(baseline['E']) / divisor)
            self.assertEqual(evaluator.measure(value, 1)['V'], '0')
            self.assertEqual(evaluator.measure(value, 1)['W'], '1')

    def test_whole_point_mask_retains_core_signs_but_inner_factor_is_mixed(self):
        m = meter(); point = ['x', ['root', ['v', 't'], 1, 3]]
        whole = S.analyze(program(['mul', point, lag()]), m)
        self.assertEqual(whole['mechanism'], 'mask')
        self.assertEqual(whole['states'][0]['core_mechanism'], 'lag')
        self.assertEqual(annotations(whole, 'whole_state_point_masks')[0]['factor_paths'], [[1]])
        self.assertTrue(annotations(whole, 'whole_state_point_masks')[0]['retained_core_signs'])
        self.assertEqual(annotations(whole, 'prefix_identity')[0]['scope'], 'unmasked_core_square')
        mixed = S.analyze(program(['add', prefix(), ['mul', point, lag()]]), m)
        self.assertEqual(mixed['mechanism'], 'coupled_sum')
        self.assertEqual(annotations(mixed, 'whole_state_point_masks'), [])
        terms = annotations(mixed, 'signed_sum_square')[0]['terms']
        self.assertEqual(terms[0]['point_factor_paths'], [])
        self.assertEqual(terms[1]['point_factor_paths'], [[2, 1]])
        self.assertEqual(annotations(mixed, 'signed_sum_square')[0]['sign_claim'], S.SIGN_CLAIM)

    def test_common_point_factor_across_signed_terms_is_a_norm_gate(self):
        m = meter(); point = ['x', ['root', ['v', 't'], 1, 2]]
        original = program(['add', ['mul', deepcopy(point), prefix()],
                                      ['scale', '-1', ['mul', deepcopy(point), lag()]]])
        factored = program(['mul', deepcopy(point), ['add', prefix(), ['scale', '-1', lag()]]])
        result = S.analyze(original, m)
        self.assertEqual(result['mechanism'], 'mask')
        self.assertEqual(result['states'][0]['core_mechanism'], 'coupled_sum')
        common = annotations(result, 'common_point_masks')[0]['factors']
        self.assertEqual(len(common), 1)
        self.assertEqual(common[0]['occurrence_paths'], [[1, 1], [2, 2, 1]])
        signed = annotations(result, 'signed_sum_square')[0]
        self.assertEqual([item['coefficient'] for item in signed['terms']], ['1', '-1'])
        self.assertTrue(all(item['point_factor_paths'] == [] for item in signed['terms']))
        actual = L.mobius(15, m)
        for values in (actual, [0] + [Q((n % 4) - 1, 2) for n in range(1, 16)]):
            evaluator = L.Evaluator(values, m)
            self.assertEqual(evaluator.measure(original, 4), evaluator.measure(factored, 4))
        checker = FINITE.Checker(15, FINITE.Meter(1000000))
        self.assertEqual(checker.measure(original, 4), checker.measure(factored, 4))

    def test_different_inner_point_indices_are_not_inferred_common(self):
        left = ['x', ['root', ['v', 't'], 1, 2]]
        right = ['x', ['root', ['v', 't'], 1, 3]]
        result = S.analyze(program(['add', ['mul', left, prefix()], ['mul', right, lag()]]), meter())
        self.assertEqual(result['mechanism'], 'coupled_sum')
        self.assertEqual(annotations(result, 'common_point_masks'), [])

    def test_standalone_root_envelope_never_bounds_a_mixed_state(self):
        m = meter()
        for base, a, b, bound in (('t', 1, 2, '3/2'), ('X', 1, 3, '1'), ('t', 0, 7, '3/2')):
            value = program(['scale', '-2', root_prefix(base, a, b)], '1/2')
            result = S.analyze(value, m)
            self.assertEqual(result['mechanism'], 'bounded_root')
            self.assertEqual(result['states'][0]['effective_weight'], '2')
            envelope = annotations(result, 'root_prefix_envelope')[0]
            self.assertEqual(envelope['normalized_core_bound'], bound)
            self.assertEqual(envelope['scope'], 'unmasked_core_square')
            checker = FINITE.Checker(15, FINITE.Meter(1000000))
            for X in (1, 2, 4):
                self.assertLessEqual(Q(checker.measure(value, X)['V']), 2 * Q(bound))
        mixed = S.analyze(program(['add', root_prefix(), prefix()]), m)
        self.assertEqual(mixed['mechanism'], 'coupled_sum')
        self.assertEqual(annotations(mixed, 'root_prefix_envelope')[0]['scope'], 'component_square_only')
        growing = S.analyze(program(root_prefix('t', 2, 3)), m)
        self.assertNotEqual(growing['mechanism'], 'bounded_root')
        self.assertEqual(annotations(growing, 'root_prefix_envelope'), [])

    def test_prime_bank_cross_terms_do_not_claim_prime_mu_sign_variation(self):
        body = ['mul', ['x', ['v', 'p']], prefix(['idiv', ['v', 't'], ['v', 'p']], 'i')]
        tree = ['sum', 'p', ['int', 2], ['root', ['v', 'X'], 1, 2],
                ['guard', ['prime', ['v', 'p']], body]]
        value = program(tree); result = S.analyze(value, meter())
        self.assertEqual(result['mechanism'], 'coupled_bank')
        bank = annotations(result, 'sum_bank_square')[0]
        self.assertTrue(bank['prime_guarded'])
        self.assertEqual(bank['sign_claim'], S.SIGN_CLAIM)
        constant = annotations(result, 'prime_guard_coefficient')[0]
        self.assertEqual(constant['path'], [4, 2, 1])
        self.assertEqual(constant['guard_path'], [4, 1])
        self.assertEqual(constant['identity'], 'mu(prime)=-1')
        simplified = deepcopy(value)
        simplified['states'][0]['tree'][4][2] = ['scale', '-1', deepcopy(body[2])]
        checker = FINITE.Checker(31, FINITE.Meter(1000000))
        self.assertEqual(checker.measure(value, 9), checker.measure(simplified, 9))

    def test_nonlinear_product_and_unknown_guard_stay_unresolved(self):
        m = meter(); result = S.analyze(program(['mul', prefix(), root_prefix()]), m)
        self.assertEqual(result['mechanism'], 'nonlinear')
        self.assertIn('product_correlation', result['states'][0]['unresolved'])
        self.assertEqual(annotations(result, 'root_prefix_envelope')[0]['scope'], 'component_square_only')
        guarded = S.analyze(program(['guard', ['eq', ['gcd', ['v', 'X'], ['v', 't']], ['int', 1]], prefix()]), m)
        self.assertEqual(guarded['mechanism'], 'unknown')
        self.assertIn('unclassified_scalar', guarded['states'][0]['unresolved'])

    def test_zero_weight_keeps_original_domain_and_never_becomes_baseline(self):
        result = S.analyze(program(['x', ['int', 0]], '0'), meter())
        self.assertEqual(result['mechanism'], 'mask')
        self.assertEqual(result['states'][0]['effective_weight'], '0')
        self.assertEqual(annotations(result, 'zero_scalar')[0]['scope'], 'where_original_state_is_defined')
        self.assertFalse(result['universal_estimate_verified'])
        self.assertFalse(result['global_bound_proved'])
        self.assertFalse(result['RH_proved'])

    def test_paths_payload_order_no_hashes_and_shared_meter_failure(self):
        m = meter(); value = program(['add', prefix(), ['scale', '-1', lag()]])
        original = deepcopy(value)
        with patch('hashlib.sha256', side_effect=AssertionError('no hashes')):
            first = S.analyze(value, m); before = m.operations; second = S.analyze(value, m)
        self.assertEqual(first, second)
        self.assertGreater(m.operations, before)
        self.assertEqual(value, original)
        for item in annotations(first, 'prefix_identity'):
            node = value['states'][0]['tree']
            for position in item['path']:
                node = node[position]
            self.assertEqual(node[0], 'sum')
        tiny = L.Meter(1)
        with self.assertRaises(OverflowError):
            S.analyze(value, tiny)
        self.assertEqual(tiny.operations, 1)
        with self.assertRaises(OverflowError):
            S.analyze(program(prefix()), meter(max_cells=100))


if __name__ == '__main__':
    unittest.main()
