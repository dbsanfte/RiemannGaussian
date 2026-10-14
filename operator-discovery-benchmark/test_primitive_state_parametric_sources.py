import copy
from fractions import Fraction as F
import unittest

import primitive_state_parametric_sources as S
import cancellation_arithmetic_language as A
import cancellation_divisor_cell_language as CELLS
import grouped_arithmetic_language as L


class SourceRecipeTests(unittest.TestCase):
    def test_complete_bound_recipe_inventory(self):
        out = S.recipes()
        self.assertEqual(out['recipe_count'], 74)
        self.assertEqual(len({r['id'] for r in out['recipes']}), 74)
        self.assertEqual(len(out['source_sha256']), 18)
        self.assertFalse(out['universal_compiler_equivalence_formally_proved'])
        self.assertFalse(out['finite_correspondence_is_universal_proof'])
        for flag in S.FLAGS:
            self.assertFalse(out[flag])
        rowmass = [r for r in out['recipes'] if r['family'] == 'primitive_rowmass']
        self.assertEqual([[x['index'] for x in r['descriptor_references']] for r in rowmass],
                         [[9, 21, 33], [45, 57, 69]])

    def test_all_cell_square_sources_match_finite_compiler(self):
        # These two development cases check the adapter against the existing
        # compiler. They cannot certify any statement at untested scales.
        total_operations = 0
        for X in (1, 2):
            data = CELLS.build_additions(X, max_operations=2000000)
            total_operations += data['construction_operations']
            descriptors = CELLS.additions()['square']
            for descriptor, group in zip(descriptors, data['square_groups']):
                state = S.divisor_state(descriptor['theta'], descriptor['power'])
                forms = dict(contrast=state['D'], prefix_plus=S.plus(state['P'], state['D']),
                             prefix_minus=S.minus(state['P'], state['D']))
                p = forms[descriptor['form']]
                expression = S.region_sum(descriptor['region'], S.times(copy.deepcopy(p), copy.deepcopy(p)))
                compiled = A.compile_expression(expression, X, 4*X-1, max_operations=2000000,
                                                max_nodes=10000, max_depth=64, max_degree=4)
                total_operations += compiled['operations']
                expected = {}
                for term in group:
                    poly = L.load_poly(term['poly'])
                    expected = L.add(expected, L.scale(L.mul(poly, poly), F(term['weight'])))
                    total_operations += len(poly)**2 + len(expected)
                self.assertEqual(L.load_poly(compiled['poly']), expected)
        self.assertLess(total_operations, 10000000)

    def test_recipe_mutations_rejected(self):
        recipe = S.recipes()['recipes'][0]
        self.assertTrue(S.validate_recipe(recipe))
        for key, value in [('theta', '1/6'), ('positive_domain', 'selected divisors only'),
                           ('lhs', ['q', '0']), ('descriptor_references', {}), ('id', 'unbound')]:
            changed = copy.deepcopy(recipe)
            changed[key] = value
            with self.assertRaises(ValueError):
                S.validate_recipe(changed)

    def test_sixth_root_not_silently_added_to_published_sources(self):
        with self.assertRaises(ValueError):
            S.divisor_state('1/6', 0)
        # Generic root language calibration belongs in the new proof kernel;
        # this adapter must stay bound to its actual immutable descriptor set.


if __name__ == '__main__':
    unittest.main()
