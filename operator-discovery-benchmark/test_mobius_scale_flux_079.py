import copy
from fractions import Fraction as Q
import unittest

import mobius_scale_flux_079 as P
import check_mobius_scale_flux_079 as C


def synthetic(u, t):
    d = [t, -t, 1]+[0]*7
    gram = [dict(i=i, j=j, terms=[dict(left_token='1', right_token='1', coefficient='1')] if i == j else [])
            for i in range(10) for j in range(i, 10)]
    return dict(u=u, flux_features=[{'1': str(x)} if x else {} for x in d], gram_upper=gram, token_intervals={'1': ['1', '1']})


class ScaleFlux(unittest.TestCase):
    def test_complete_shared_cells_keep_signs_gaps_outer_support_and_root_tokens(self):
        arithmetic = P.P.Arithmetic(160)
        parent = [dict(left=0, right=40, weight={'x': '2'}), dict(left=44, right=160, weight={'x': '-1', 'y': '1/3'})]
        child = [dict(left=0, right=12, weight={'x': '-1'}), dict(left=20, right=80, weight={'y': '2'})]
        for gamma in ('1/7', '17/53', '2/3', '53/17'):
            cells = P.construct_cells(arithmetic, 640, parent, child, [2, 7], gamma)
            result = C.verify_cells(parent, child, [2, 7], gamma, cells)
            self.assertEqual(result['status'], 'VERIFIED_CELLS', result)
            pv, cv = arithmetic.features(parent, [2, 7], gamma), arithmetic.features(child, [2, 7], gamma)
            for i in range(10):
                expected = {}
                P.add(expected, pv[i]); P.add(expected, cv[i], Q(-1))
                self.assertEqual(cells['flux_features'][i], P.saved(expected))
            self.assertTrue(any(c['child_category'] == 10 for c in cells['cells']))
            broken = copy.deepcopy(cells); broken['cells'][0]['signed_count'] += 1
            self.assertEqual(C.verify_cells(parent, child, [2, 7], gamma, broken)['status'], 'INVALID')

    def test_root_identity_is_shared_but_counts_cannot_be_rebound(self):
        a = dict(token_intervals={'1': ['1', '1'], 'x': ['1/3', '1/2']}, token_definitions={'x': {'count': 7}})
        b = dict(token_intervals={'1': ['1', '1'], 'x': ['2/5', '3/5']}, token_definitions={'x': {'count': 7}})
        self.assertEqual(P.merge_tokens(a, b)['x'], ['2/5', '1/2'])
        b['token_definitions']['x']['count'] = 8
        with self.assertRaises(ValueError): P.merge_tokens(a, b)

    def test_uniform_floor_coefficient_price_and_exact_inactive_channels(self):
        kernel = [dict(divisor=4, weight='-1'), dict(divisor=5, weight='1')]
        proposal = P.fixed_norm(kernel, [2, 3], 100)
        check = C.verify_coefficient_norm(kernel, [2, 3], 100, proposal['certificate'])
        self.assertEqual(check['status'], 'VERIFIED_UNIFORM_COEFFICIENT_NORM', check)
        inactive = P.inactive_coordinates(proposal['folded_kernel'], '2/5', 100)
        self.assertEqual(inactive, [0, 3, 4, 5, 6])
        self.assertEqual(C.verify_inactive(proposal['folded_kernel'], '2/5', 100, inactive)['status'], 'VERIFIED_INACTIVE_COORDINATES')
        for u in (1, 99, 100, 137):
            actual = sum(sum(Q(k['weight']) for k in proposal['folded_kernel'] if n <= u//k['divisor'])**2 for n in range(1, u+1))
            self.assertLessEqual(actual, Q(proposal['certificate']['I'])*u+Q(proposal['certificate']['E']))

    def test_detector_discovers_a_signed_pair_and_rejects_broken_continuation(self):
        rows = {u: synthetic(u, t) for u, t in [(16, 10), (32, 20), (64, 40)]}
        rays = P.ray_dictionary([0, 1, 2])
        bank = P.floating_leaf_bank(rows, rays, '1')
        cover = P.discover_cover(bank, ['1']*3+['0']*7, '1')
        self.assertEqual(cover['status'], 'CONDITIONAL_COVER_PROPOSAL', cover)
        self.assertTrue(any(leaf['a'][:3] == ['1', '1', '0'] for leaf in cover['leaves']))
        for leaf in cover['leaves']:
            leaf.update(P.calibrate_leaf(rows, leaf['a'], '1'))
        price = P.cover_price(cover['leaves'], cover['coefficients'], '1')
        check = C.verify_cover(cover['target'], [x['a'] for x in cover['leaves']], cover['coefficients'],
                               [x['kappa'] for x in cover['leaves']], '1', {'price': str(price)})
        self.assertEqual(check['status'], 'VERIFIED_CONDITIONAL_COVER', check)
        self.assertFalse(check['uniform_correlation_proved'])
        self.assertLess(price, 4)
        pair = next(x for x in cover['leaves'] if x['a'][:3] == ['1', '1', '0'])
        good = synthetic(128, 80)
        self.assertEqual(C.verify_local_leaf(good, pair['a'], pair['kappa'], '1')['status'], 'CERTIFIED_FINITE')
        good['flux_features'][1] = {'1': '-79'}
        self.assertEqual(C.verify_local_leaf(good, pair['a'], pair['kappa'], '1')['status'], 'REFUTED_FINITE')

    def test_actual_cells_witness_proper_leaf_not_disguised_total(self):
        arithmetic = P.P.Arithmetic(120)
        parent = [dict(left=0, right=120, weight={'1': '1'})]
        child = [dict(left=0, right=60, weight={'1': '1'})]
        payload = P.construct_cells(arithmetic, 480, parent, child, [], '1/2')
        tokens = {'1': ['1', '1']}
        ray = ['0', '1']+['0']*8
        witness = P.noncircular_witness(payload, tokens, ray)
        self.assertIsNotNone(witness)
        self.assertEqual(C.verify_noncircularity(payload, ray, tokens, witness)['status'], 'VERIFIED_NONCIRCULARITY')
        self.assertIsNone(P.noncircular_witness(payload, tokens, ['1']*10))

    def test_empty_intervals_and_resource_domain_are_not_arithmetic_refutations(self):
        arithmetic = P.P.Arithmetic(30)
        empty = P.construct_cells(arithmetic, 120, [], [], [], '13/19')
        self.assertEqual(C.verify_cells([], [], [], '13/19', empty)['status'], 'VERIFIED_CELLS')
        with self.assertRaises(ValueError):
            P.construct_cells(arithmetic, 120, [dict(left=0, right=30, weight={'1': '1'})], [], [], '0')
        self.assertEqual(P.exact_solve([['1']+['0']*9], ['0', '1']+['0']*8), None)


if __name__ == '__main__': unittest.main()
