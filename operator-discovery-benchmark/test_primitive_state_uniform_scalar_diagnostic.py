import copy
from fractions import Fraction as F
import unittest
from unittest.mock import patch

import primitive_state_uniform_scalar_diagnostic as D
import grouped_arithmetic_templates as BASE
import grouped_arithmetic_language as POLY
import cancellation_divisor_cell_language as CELLS


def vector():
    return [F(0)] * 1957


def signed(x, index, value):
    x[366 + 2*index] = max(F(value), F(0))
    x[367 + 2*index] = max(-F(value), F(0))


class ScalarReadinessTests(unittest.TestCase):
    def test_zero_and_scope(self):
        out = D.analyze(vector())
        self.assertEqual(out['majorant_M'], '0')
        self.assertTrue(out['elementary_scalar_ready'])
        self.assertEqual(out['canonical_anchored_initial_cost'], '1')
        for name in D.FLAGS:
            self.assertIs(out[name], False)
        self.assertFalse(out['imposed_on_search'])
        self.assertIn('all-scale nonconstant coefficient identity', out['unresolved_obligations'])

    def test_gamma_zero_is_not_partition_cancellation(self):
        x = vector()
        signed(x, 21, 5)
        signed(x, 33, -9)
        self.assertEqual(12*F(5) + F(20, 3)*(-9), 0)
        out = D.analyze(x)
        self.assertFalse(out['elementary_scalar_ready'])
        self.assertIsNone(out['majorant_M'])
        self.assertEqual(out['rowmass_gate'][0]['effective_head'], '5')
        self.assertEqual(out['rowmass_gate'][0]['effective_tail'], '-9')

    def test_signed_split_partition_and_invariance(self):
        x = vector()
        for indices in ((9, 21, 33), (45, 57, 69)):
            for j, v in zip(indices, (F(7, 3), F(-7, 3), F(-7, 3))):
                signed(x, j, v)
        out = D.analyze(x)
        self.assertTrue(out['elementary_scalar_ready'])
        self.assertEqual(out['majorant_M'], '0')
        x[366+2*9] += 11
        x[367+2*9] += 11
        self.assertEqual(D.analyze(x)['rowmass_gate'], out['rowmass_gate'])

    def test_scalar_majorant_components_and_constant_exclusion(self):
        x = vector()
        x[0] = 10**30
        x[1592] = 10**30
        signed(x, 0, -3)       # norm, one: 4*3
        signed(x, 192, 2)      # unit: 2
        x[312] = -4           # parent cell, negative still scalar-bounded
        signed(x, 331, -2)     # parent cell one: 2
        signed(x, 333, 6)      # parent cell contrast: 3
        x[1717] = -3           # H00: | -3 |
        signed(x, 433, -2)     # parent norm tau=-2: 3
        signed(x, 463+15+6, 4) # child prime contrast tau=-2: 12
        out = D.analyze(x)
        self.assertEqual(out['components'], dict(base='14', cell_squares='1', cell_relations='5', matrices='3', primitive='15'))
        self.assertEqual(out['majorant_M'], '38')
        self.assertEqual(out['excluded_constant_square']['weight'], str(10**30))
        self.assertFalse(out['finite_candidate_checked'])

    def test_primitive_atoms_combine_before_absolute_values(self):
        x = vector()
        signed(x, 433, 3)
        signed(x, 439, 6)
        signed(x, 434, 10**20)  # prefix atom has formal constant zero
        out = D.analyze(x)
        self.assertEqual(out['components']['primitive'], '0')
        group = next(r for r in out['primitive_scalar_groups'] if r['family'] == 'norm' and r['region'] == 'parent')
        self.assertEqual(group['tau'], '0')

    def test_original_and_quotient_matrix_constants_agree(self):
        x = vector()
        for j in range(360):
            x[1597+j] = F((j % 13)-6, 7)
        z, u = D.Z, D.U
        def quadratic(values, v):
            mat = [[F(0)]*15 for _ in range(15)]
            it = iter(values)
            for a in range(15):
                for b in range(a, 15):
                    mat[a][b] = mat[b][a] = next(it)
            return sum(v[a]*mat[a][b]*v[b] for a in range(15) for b in range(15))
        expected = 2*quadratic(x[1597:1717], z)+quadratic(x[1717:1837], z)-2*quadratic(x[1837:], z)
        out = D.analyze(x)
        self.assertEqual(F(out['formal_matrix_scalar_coefficient']), expected)
        self.assertEqual(F(out['canonical_anchored_initial_cost']), 1+quadratic(x[1597:1717], u)+quadratic(x[1837:], u))
        self.assertNotEqual(z, u)

    def test_full_rowmass_polynomials_partition_at_boundaries(self):
        # A compiler regression check; the all-scale argument is the exact
        # complementary domain partition, not these two sample horizons.
        for X in (1, 2):
            instance = BASE.build_instance('mu', X, 6, 32, max_operations=2000000)['instance']
            def expand(group):
                terms = []
                for term in group:
                    relation = POLY.relation(term['spec'], 'mu', 4*X-1)
                    terms.append(POLY.mul(POLY.load_poly(term['multiplier']), relation))
                return POLY.add(*terms)
            for all_index, head_index, tail_index in ((9, 21, 33), (45, 57, 69)):
                polynomials = [expand(instance['relation_groups'][j]) for j in (all_index, head_index, tail_index)]
                self.assertEqual(polynomials[0], POLY.add(polynomials[1], polynomials[2]))

    def test_cell_constants_match_generated_formal_polynomials(self):
        instance = CELLS.build_additions(1, max_operations=2000000)
        square_desc = CELLS.additions()['square']
        relation_desc = CELLS.additions()['relation']
        for d, group in zip(square_desc, instance['square_groups']):
            actual = sum(F(term['weight'])*POLY.load_poly(term['poly']).get((), F(0))**2 for term in group)
            self.assertEqual(actual, F({'parent': 1, 'child': 2}[d['region']], 4))
        for d, group in zip(relation_desc, instance['relation_groups']):
            actual = sum(POLY.load_poly(term['multiplier']).get((), F(0))*
                         POLY.relation(term['spec'], 'mu', 3).get((), F(0)) for term in group)
            expected = {'one': F(-1), 'prefix': F(0), 'contrast': F(1, 2), 'normalization': F(1)}[d['form']]
            self.assertEqual(actual, {'parent': 1, 'child': 2}[d['region']]*expected)

    def test_unknown_grammar_and_inexact_or_unbounded_input_rejected(self):
        ds = copy.deepcopy(D.LANGUAGE.descriptors())
        ds['square'][0]['weight'] = 'different'
        with patch.object(D.LANGUAGE, 'descriptors', return_value=ds), self.assertRaises(ValueError):
            D.analyze(vector())
        for value in (0.0, True, '1e10000000', '2/2', '0'*2500):
            x = vector()
            x[0] = value
            with self.assertRaises(ValueError):
                D.analyze(x)
        x = vector()
        x[0] = 2**4096
        with self.assertRaises(OverflowError):
            D.analyze(x)


if __name__ == '__main__':
    unittest.main()
