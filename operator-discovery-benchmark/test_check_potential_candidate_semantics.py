"""Tiny syntactic and scoped-algebra cases; no arithmetic-source experiments."""
from copy import deepcopy
import unittest

import check_potential_candidate_semantics as C
from check_potential_candidate_discovery import Meter


def var(name):
    return ['v', name]


def integer(value):
    return ['int', value]


def prefix(endpoint=None, name='n'):
    return ['sum', name, integer(1), var('t') if endpoint is None else endpoint, ['x', var(name)]]


def program(tree, weight='1'):
    return dict(states=[dict(weight=weight, tree=tree)])


def notes(annotation, kind):
    return [n for state in annotation['states'] for n in state['annotations'] if n['kind'] == kind]


class Checks(unittest.TestCase):
    meters = []

    @classmethod
    def tearDownClass(cls):
        total = sum(m.operations for m in cls.meters)
        print('SYNTHETIC_WORK module=test_check_potential_candidate_semantics operations=%d' % total)
        if total > 5000000:
            raise AssertionError('owned synthetic development exceeds5m')

    def meter(self, cap=1000000, **kwargs):
        result = Meter(cap, **kwargs)
        self.meters.append(result)
        return result

    def analyze(self, candidate):
        return C.analyze(candidate, self.meter())

    def test_baseline_and_exact_payload_verification(self):
        candidate = dict(states=[])
        annotation = self.analyze(candidate)
        self.assertEqual(annotation, dict(schema=C.SCHEMA, mechanism='baseline', states=[],
            scope=C.SCOPE, universal_estimate_verified=False, global_bound_proved=False, RH_proved=False))
        self.assertTrue(C.verify(candidate, annotation, self.meter()))
        for key, replacement in [('RH_proved', True), ('global_bound_proved', 0),
                                 ('universal_estimate_verified', True), ('scope', 'all sources')]:
            bad = deepcopy(annotation)
            bad[key] = replacement
            with self.assertRaises(ValueError):
                C.verify(candidate, bad, self.meter())

    def test_target_copy_and_exact_lag_domain(self):
        target = self.analyze(program(prefix()))
        self.assertEqual(target['mechanism'], 'target_copy')
        self.assertEqual(notes(target, 'prefix_identity')[0], dict(kind='prefix_identity', path=[],
            endpoint='t', divisor=1, normalized_core_potential='E(X)', domain='all integer X>=1',
            initial_core_potential='1', scope='unmasked_core_square'))
        lag = self.analyze(program(prefix(['idiv', var('t'), integer(3)]), '2'))
        self.assertEqual(lag['mechanism'], 'lag')
        entry = notes(lag, 'prefix_identity')[0]
        self.assertEqual(entry['normalized_core_potential'], 'E(X/divisor)/divisor')
        self.assertEqual(entry['domain'], 'positive X divisible by divisor')
        self.assertEqual(entry['initial_core_potential'], '0')
        self.assertEqual(lag['states'][0]['effective_weight'], '2')
        bad = deepcopy(lag)
        bad['states'][0]['annotations'][0]['domain'] = 'all integer X>=1'
        with self.assertRaises(ValueError):
            C.verify(program(prefix(['idiv', var('t'), integer(3)]), '2'), bad, self.meter())

    def test_standalone_root_envelopes_are_reduced_and_scoped(self):
        for base, bound in [('t', '3/2'), ('X', '1')]:
            candidate = program(prefix(['root', var(base), 2, 6]))
            result = self.analyze(candidate)
            self.assertEqual(result['mechanism'], 'bounded_root')
            note = notes(result, 'root_prefix_envelope')[0]
            self.assertEqual((note['base'], note['exponent'], note['normalized_core_bound']),
                             (base, '1/3', bound))
            self.assertEqual(note['scope'], 'unmasked_core_square')
        zero_exponent = self.analyze(program(prefix(['root', var('t'), 0, 6])))
        self.assertEqual(notes(zero_exponent, 'root_prefix_envelope')[0]['exponent'], '0')
        supercritical = self.analyze(program(prefix(['root', var('t'), 2, 3])))
        self.assertFalse(notes(supercritical, 'root_prefix_envelope'))
        self.assertEqual(supercritical['mechanism'], 'coupled_sum')
        shifted = self.analyze(program(prefix(['max', integer(0), ['isub', var('t'), integer(2)]])))
        self.assertFalse(notes(shifted, 'prefix_identity'))

    def test_whole_state_points_are_masks_with_core_signs_retained(self):
        candidate = program(['scale', '-3/2', ['mul', ['x', var('t')], prefix()]], '2')
        result = self.analyze(candidate)
        state = result['states'][0]
        self.assertEqual((state['mechanism'], state['core_mechanism'], state['outer_coefficient'],
                          state['effective_weight']), ('mask', 'target_copy', '-3/2', '9/2'))
        mask = notes(result, 'whole_state_point_masks')[0]
        self.assertEqual(mask['factor_paths'], [[2, 1]])
        self.assertEqual(mask['identity'], 'mu(n)^2=squarefree(n)')
        self.assertEqual(mask['scope'], 'entire_state_square')
        self.assertTrue(mask['retained_core_signs'])
        self.assertEqual(notes(result, 'prefix_identity')[0]['path'], [2, 2])

    def test_inside_sum_point_factors_preserve_complete_mixed_terms(self):
        first = ['mul', ['x', var('t')], prefix()]
        second = ['scale', '-2', ['mul', ['x', ['root', var('t'), 1, 2]],
                                   prefix(['idiv', var('t'), integer(2)])]]
        result = self.analyze(program(['add', first, second]))
        self.assertEqual(result['mechanism'], 'coupled_sum')
        self.assertFalse(notes(result, 'whole_state_point_masks'))
        self.assertFalse(notes(result, 'common_point_masks'))
        square = notes(result, 'signed_sum_square')[0]
        self.assertEqual([item['coefficient'] for item in square['terms']], ['1', '-2'])
        self.assertEqual([item['point_factor_paths'] for item in square['terms']], [[[1, 1]], [[2, 2, 1]]])
        self.assertEqual([item['factor_paths'] for item in square['terms']], [[[1, 2]], [[2, 2, 2]]])
        self.assertEqual(square['cross_terms'], 'all 2*c_i*c_j*T_i*T_j for i<j retained')
        self.assertEqual(square['sign_claim'], C.SIGN_SCOPE)
        self.assertIn('mixed_term_estimate', result['states'][0]['unresolved'])
        self.assertTrue(all(n['scope'] == 'component_square_only' for n in notes(result, 'prefix_identity')))

    def test_literal_common_factors_are_masks_but_index_aliases_are_not(self):
        source = ['x', var('t')]
        first = ['mul', deepcopy(source), ['mul', deepcopy(source), prefix()]]
        second = ['mul', deepcopy(source), prefix(['root', var('t'), 1, 6])]
        candidate = program(['add', first, ['scale', '-1', second]])
        result = self.analyze(candidate)
        self.assertEqual((result['mechanism'], result['states'][0]['core_mechanism']), ('mask', 'coupled_sum'))
        common = notes(result, 'common_point_masks')[0]
        self.assertEqual(common['factors'], [dict(index_path=[1, 1, 1],
            occurrence_paths=[[1, 1], [2, 2, 1]])])
        square = notes(result, 'signed_sum_square')[0]
        self.assertEqual(square['terms'][0]['point_factor_paths'], [[1, 2, 1]])
        self.assertEqual(square['terms'][1]['point_factor_paths'], [])
        self.assertIn('mixed_term_estimate', result['states'][0]['unresolved'])
        aliased = program(['add', ['mul', ['x', var('t')], prefix()],
                           ['mul', ['x', ['idiv', var('t'), integer(1)]], prefix()]])
        other = self.analyze(aliased)
        self.assertEqual(other['mechanism'], 'coupled_sum')
        self.assertFalse(notes(other, 'common_point_masks'))

    def test_prime_bank_constant_factors_do_not_claim_varying_signs(self):
        body = ['mul', ['x', var('p')], prefix(['idiv', var('t'), var('p')])]
        tree = ['sum', 'p', integer(2), ['root', var('X'), 1, 3],
                ['guard', ['prime', var('p')], body]]
        result = self.analyze(program(tree))
        self.assertEqual(result['mechanism'], 'coupled_bank')
        bank = notes(result, 'sum_bank_square')[0]
        self.assertTrue(bank['prime_guarded'])
        self.assertEqual(bank['body_path'], [4])
        self.assertEqual(bank['cross_terms'], 'all pairs of distinct summation indices retained')
        self.assertEqual(bank['sign_claim'], C.SIGN_SCOPE)
        self.assertEqual(notes(result, 'prime_guard_coefficient'), [dict(kind='prime_guard_coefficient',
            path=[4, 2, 1], guard_path=[4, 1], binding='p', identity='mu(prime)=-1', scope='guarded_summand')])
        self.assertFalse(notes(result, 'whole_state_point_masks'))
        self.assertFalse(notes(result, 'root_prefix_envelope'))
        self.assertIn('index_pair_correlation', result['states'][0]['unresolved'])

    def test_nonlinear_and_mixed_root_bounds_never_bound_whole_expression(self):
        root = prefix(['root', var('t'), 1, 6])
        product = self.analyze(program(['mul', prefix(), root]))
        self.assertEqual(product['mechanism'], 'nonlinear')
        self.assertEqual(notes(product, 'product_square')[0]['factor_paths'], [[1], [2]])
        self.assertEqual(notes(product, 'root_prefix_envelope')[0]['scope'], 'component_square_only')
        self.assertIn('product_correlation', product['states'][0]['unresolved'])
        mixed = self.analyze(program(['add', prefix(), ['scale', '-1', root]]))
        self.assertEqual(mixed['mechanism'], 'coupled_sum')
        self.assertEqual(notes(mixed, 'root_prefix_envelope')[0]['scope'], 'component_square_only')
        self.assertIn('mixed_term_estimate', mixed['states'][0]['unresolved'])

    def test_unknown_guards_and_inner_masks_do_not_get_promoted(self):
        guarded = program(['guard', ['eq', ['gcd', var('t'), integer(2)], integer(1)], prefix()])
        unknown = self.analyze(guarded)
        self.assertEqual(unknown['mechanism'], 'unknown')
        self.assertFalse(notes(unknown, 'prefix_identity'))
        self.assertIn('unclassified_scalar', unknown['states'][0]['unresolved'])
        masked_prefix = ['sum', 'n', integer(1), var('t'),
                         ['guard', ['squarefree', var('n')], ['x', var('n')]]]
        inner = self.analyze(program(masked_prefix))
        self.assertEqual(inner['mechanism'], 'coupled_sum')
        self.assertFalse(notes(inner, 'whole_state_point_masks'))
        self.assertFalse(notes(inner, 'prefix_identity'))

    def test_unit_core_zero_coefficients_and_multiple_states_keep_scope(self):
        point = self.analyze(program(['mul', ['x', var('t')], ['x', var('t')]]))
        self.assertEqual((point['mechanism'], point['states'][0]['core_mechanism']), ('mask', 'unknown'))
        self.assertEqual(notes(point, 'unit_core_potential'), [dict(kind='unit_core_potential',
            normalized_core_potential='1/X', scope='unmasked_core_square')])
        self.assertEqual(point['states'][0]['unresolved'], ['uniform_signed_innovation_estimate'])
        zero = self.analyze(program(['scale', '0', prefix()]))
        self.assertEqual(zero['mechanism'], 'target_copy')
        self.assertEqual(zero['states'][0]['effective_weight'], '0')
        self.assertEqual(zero['states'][0]['annotations'][-1], dict(kind='zero_scalar',
            scope='where_original_state_is_defined'))
        scalar = self.analyze(program(['q', '1']))
        self.assertEqual(scalar['mechanism'], 'unknown')
        multi = self.analyze(dict(states=[dict(weight='1', tree=prefix()),
                                         dict(weight='2', tree=prefix(['root', var('X'), 1, 2]))]))
        self.assertEqual(multi['mechanism'], 'multi_state')
        self.assertEqual([s['state'] for s in multi['states']], [0, 1])

    def test_plausible_false_annotations_are_rejected(self):
        candidate = program(['add', prefix(), ['scale', '-1', prefix(['root', var('t'), 1, 6])]])
        original = self.analyze(candidate)
        self.assertTrue(C.verify(candidate, original, self.meter()))
        for alteration in range(6):
            bad = deepcopy(original)
            state = bad['states'][0]
            if alteration == 0:
                bad['mechanism'] = 'bounded_root'
            elif alteration == 1:
                notes(bad, 'signed_sum_square')[0]['cross_terms'] = 'diagonal squares only'
            elif alteration == 2:
                notes(bad, 'root_prefix_envelope')[0]['scope'] = 'entire_state_square'
            elif alteration == 3:
                state['unresolved'].remove('mixed_term_estimate')
            elif alteration == 4:
                notes(bad, 'signed_sum_square')[0]['terms'][0]['path'] = [2]
            else:
                state['state'] = False
            with self.assertRaises(ValueError):
                C.verify(candidate, bad, self.meter())

    def test_validation_and_shared_resource_failures(self):
        for candidate in (program(prefix(), '-1'), program(['q', '01']),
                          program(['sum', 'N', integer(1), integer(2), ['x', var('N')]])):
            with self.assertRaises(ValueError):
                C.analyze(candidate, self.meter())
        budget = self.meter(cap=8)
        with self.assertRaises(OverflowError):
            C.analyze(program(prefix()), budget)
        used = budget.operations
        self.assertGreater(used, 0)
        with self.assertRaises(OverflowError):
            C.analyze(program(prefix()), budget)
        self.assertGreaterEqual(budget.operations, used)
        cells = self.meter(max_cells=1)
        with self.assertRaises(OverflowError):
            C.analyze(program(prefix()), cells)
        self.assertGreater(cells.peak_live_cells, 1)
        forged = dict(states=[], mechanism=object())
        with self.assertRaises(ValueError):
            C.verify(dict(states=[]), forged, self.meter())


if __name__ == '__main__':
    unittest.main()
