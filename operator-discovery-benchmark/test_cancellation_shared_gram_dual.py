import copy
import unittest

import cancellation_shared_gram_dual as D
import check_cancellation_shared_gram as I


def poly(*terms):
    return [dict(m=list(m), c=str(q)) for m, q in terms]


def fixture():
    # Constant atom, zero atom and diagonal-only monomial are all intentional.
    instance = dict(target='mu', horizon=1, lhs=poly(((1, 1), -1)),
                    square_groups=[], relation_groups=[])
    blocks = [{'z2': [[poly(((), 1)), []]],
               'a5': [[poly(((1,), 1)), [], [], [], []]]}]
    return [instance], blocks, {'z2': 2, 'a5': 5}


class SharedGramDual(unittest.TestCase):
    def test_complete_mixed_dimension_separator(self):
        instances, blocks, specs = fixture()
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertTrue(out['certified'], out)
        self.assertTrue(out['independent_full_Gram_check_passed'])
        self.assertEqual(list(out['gram_duals']), ['a5', 'z2'])
        self.assertEqual(len(out['gram_columns_dot_y']), 18)
        self.assertIn(dict(instance=0, m=[1, 1]), out['monomials'])
        self.assertIn(dict(instance=0, m=[]), out['monomials'])
        self.assertEqual(out['gram_duals']['a5']['matrix'][0][0], '1')
        self.assertTrue(I.verify_dual(instances, blocks, specs, out)['verified'])

    def test_constant_moment_not_assumed_zero(self):
        instances, blocks, specs = fixture()
        instances[0]['lhs'] = poly(((), -1))
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertTrue(out['certified'], out)
        self.assertEqual(out['constant_coordinates'], ['1'])
        self.assertFalse(out['all_C_q_extension_requires_zero_constant_coordinates'])

    def test_full_gram_diagonal_prevents_false_separator(self):
        instances, blocks, specs = fixture()
        instances[0]['lhs'] = poly(((1, 1), 1))
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertFalse(out['certified'])
        self.assertIn('no exact infeasibility', out['reason'])

    def test_all_cross_moments_restricted_to_zero(self):
        instances, blocks, specs = fixture()
        instances[0]['lhs'] = poly(((1,), -1))
        blocks[0]['z2'] = [[poly(((), 1)), poly(((1,), 1))]]
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertFalse(out['certified'])
        self.assertIn('no exact infeasibility', out['reason'])

    def test_auxiliary_constant_coverage(self):
        instances, blocks, specs = fixture()
        instances.append(dict(target='mu', horizon=1, lhs=[], square_groups=[], relation_groups=[]))
        blocks.append({'z2': [], 'a5': []})
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertTrue(out['certified'], out)
        self.assertEqual(len(out['constant_coordinates']), 2)
        self.assertIn(dict(instance=1, m=[]), out['monomials'])

    def test_classifications_and_bad_coverage(self):
        nonnegative, relations, layout = D.classify([{}]*8, (1, 1), 5, {'g': 2})
        self.assertEqual(nonnegative, [0, 3, 4, 5, 7])
        self.assertEqual(relations, [1, 2, 6])
        self.assertEqual(layout, [('g', 2, [(5, 0, 0), (6, 0, 1), (7, 1, 1)])])
        with self.assertRaises(ValueError):
            D.classify([{}]*7, (1, 1), 5, {'g': 2})

    def test_malformed_inputs_and_resource_limit(self):
        args = fixture()
        for limit in (float('nan'), True, 0):
            self.assertEqual(D.propose(*args[:2], gram_specs=args[2], time_limit=limit)['status'], 'uncertified')
        self.assertEqual(D.propose(*args[:2], gram_specs=args[2], max_rows=1)['status'], 'missing_resource')
        args[1][0]['z2'][0].append([])
        self.assertFalse(D.propose(*args[:2], gram_specs=args[2])['certified'])

    def test_independent_rejects_mutation(self):
        instances, blocks, specs = fixture()
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertTrue(out['certified'], out)
        bad = copy.deepcopy(out)
        bad['gram_duals']['a5']['matrix'][0][1] = '1'
        bad['gram_duals']['a5']['matrix'][1][0] = '1'
        with self.assertRaises(ValueError):
            I.verify_dual(instances, blocks, specs, bad)
        bad = copy.deepcopy(out)
        bad['monomials'] = [m for m in bad['monomials'] if m['m'] != [1, 1]]
        with self.assertRaises(ValueError):
            I.verify_dual(instances, blocks, specs, bad)


if __name__ == '__main__':
    unittest.main()
