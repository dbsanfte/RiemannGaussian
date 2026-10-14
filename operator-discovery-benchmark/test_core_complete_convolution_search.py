"""Synthetic exact identities, complete pricing and transfer-domain regressions."""
import copy
import unittest
from fractions import Fraction as Q

import core_complete_convolution_search as P
from prime_bank_candidates import Meter

METER = Meter(100000000, 300)


def conv(a, b, n):
    out = [Q(0)]*n
    for k in range(1, n+1):
        out[k-1] = sum((a[d-1]*b[k//d-1] for d in range(1, k+1) if k % d == 0), Q(0))
        METER.charge(k)
    return out


def evaluate(poly, states, n):
    out = [Q(0)]*n
    for key, c in poly.items():
        value = [Q(1)]+[Q(0)]*(n-1)
        for v in key:
            value = conv(value, states[v], n)
        out = [a+c*b for a, b in zip(out, value)]
    return out


def cutoff(n, a):
    a = Q(a)
    return max(i for i in range(n+1) if i**a.denominator <= n**a.numerator)


class CompleteConvolutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.actual = P.prefix_library('mobius', '1/24', METER)
        cls.generic = P.prefix_library('bounded', '1/24', METER)

    def test_prefix_search_derives_complete_pair_and_cube_envelopes(self):
        pair, cube = self.actual['levels'][1:]
        self.assertEqual(pair['bound'], P.collect([P.term(12, 1, Q(1, 2), lx=1), P.term(4, 2)]))
        self.assertEqual(cube['bound'], P.collect([P.term(270, 1, Q(2, 3), lx=2),
            P.term(36, 2, Q(1, 3), lx=1), P.term(8, 3)]))
        self.assertEqual(pair['candidates'][pair['selected']]['alpha'], '1/2')
        self.assertEqual(cube['candidates'][cube['selected']]['alpha'], '1/3')
        self.assertFalse(self.actual['ordinary_critical_moment_convergence_assumed'])

    def test_generic_ablation_preserves_powers_and_pays_reciprocal_logs(self):
        actual, generic = self.actual['levels'][2]['bound'], self.generic['levels'][2]['bound']
        self.assertEqual([(r['U_power'], r['X_power']) for r in actual],
                         [(r['U_power'], r['X_power']) for r in generic])
        self.assertEqual(generic[0]['logU_degree'], 2)
        self.assertEqual(actual[0]['logU_degree'], 0)

    def test_scale_relation_changes_the_proof_choice(self):
        wide = P.prefix_library('mobius', '3/4', METER)
        self.assertEqual(wide['levels'][2]['candidates'][wide['levels'][2]['selected']]['rule'], 'coefficient_mass')
        # A critical weighted lift keeps its two logarithms.
        self.assertEqual(P.lift_finite([P.term(1, 0, 1)], ['1/6'], 'mobius'), [P.term(3, 0, 1, lx=2)])

    def test_synthesized_hyperbola_identities_hold_at_every_small_prefix(self):
        for level in self.actual['levels'][1:]:
            trial = level['candidates'][level['selected']]
            m, n = level['power'], 27
            f = [Q((-1)**k*(k % 4+1), k % 3+1) for k in range(1, n+1)]
            t = cutoff(n, trial['alpha'])
            states = dict(E=f, T=f[:t]+[Q(0)]*(n-t))
            columns = [P.decode(b) for b in trial['basis']]+[P.decode(trial['ideal'])]
            self.assertEqual(P.compose(columns, trial['certificate']['solution']), {('E',)*m: Q(1)})
            self.assertEqual(evaluate(P.decode(trial['ideal']), states, n), [0]*n)
            self.assertEqual(evaluate({('T',)*m: Q(1)}, states, n)[0], f[0]**m)

    def test_affine_normalization_collects_the_whole_mean_and_head(self):
        old = P.OLD.hyperbola_synthesize('1/6', '5/6', METER)
        new = P.normalize(old, METER)
        expected = {('E', 'T', 'T'): Q(3), ('R', 'R', 'R'): Q(1), ('R', 'T', 'T'): Q(-3)}
        self.assertEqual(P.decode(new['normalized_join']), expected)
        self.assertEqual(P.add(P.decode(new['normalized_join']), P.decode(new['normalized_remainder'])), {('E',)*3: Q(1)})
        for n in [1, 16, 27]:
            f = [Q((-1)**k*(k % 5+1), 3) for k in range(n)]
            t, r = cutoff(n, '1/6'), cutoff(n, '5/6')
            states = dict(E=f, T=f[:t]+[0]*(n-t), R=f[:r]+[0]*(n-r))
            self.assertEqual(evaluate(expected, states, n), evaluate({('E',)*3: Q(1)}, states, n))

    def test_rectangle_is_not_used_when_its_product_exceeds_the_prefix(self):
        cheap = P.monomial_price(('T',)*3, '1/3', '1/2', self.actual, METER)
        expensive = P.monomial_price(('R',)*3, '1/6', '5/6', self.actual, METER)
        self.assertEqual(cheap['candidates'][cheap['selected']]['rule'], 'complete_rectangle')
        self.assertFalse(any(c['rule'] == 'complete_rectangle' for c in expensive['candidates']))
        self.assertGreater(P.score(expensive['bound'], Q(1, 24))[0], 0)
        with self.assertRaises(ValueError):
            P.monomial_price(('E',)*3, '1/3', '1/2', self.actual, METER)

    def test_complete_geometry_pays_the_large_head_and_certifies_every_threshold(self):
        g = P.complete_geometry('1/6', '5/6', self.actual, METER)
        basis, ideals, _ = P.geometry_columns('1/6', '5/6')
        source = {('E',)*3: Q(1)}
        self.assertTrue(g['every_finite_head_priced'])
        self.assertGreaterEqual(P.score(g['bound'], Q(1, 24))[0], Q(17, 24))
        for t in g['trials']:
            columns = [basis[i] for i in t['allowed']]+ideals
            cert = t['certificate']
            if cert['status'] == 'feasible':
                self.assertEqual(P.compose(columns, cert['solution']), source)
            else:
                y = P.decode(cert['dual'])
                self.assertTrue(all(sum(y.get(k, 0)*v for k, v in col.items()) == 0 for col in columns))
                self.assertNotEqual(sum(y.get(k, 0)*v for k, v in source.items()), 0)

    def test_outer_lift_retains_lower_scale_terms_and_the_exact_head_type(self):
        bound = P.lift_outer(self.actual['levels'][2]['bound'], 2, 3, 'mobius')
        self.assertEqual(bound, P.collect([P.term(2430, Q(5, 3), Q(2, 3), lx=2),
            P.term(81, Q(10, 3), Q(1, 3), lx=1), P.term(8, 5), P.term(8, 1)]))
        self.assertEqual(P.score(P.square_energy(bound), Q(1, 24))[0], Q(17, 36))
        for p, m in [(0, 3), (2, 2), (3, 2)]:
            with self.assertRaises(ValueError):
                P.lift_outer(bound, p, m, 'mobius')

    def test_transfer_search_selects_smaller_cube_only_when_all_padding_is_subcritical(self):
        transfer = P.transfer_search(2, '2/3', '1/24', METER)
        selected = transfer['trials'][transfer['selected']]
        self.assertEqual((selected['alpha'], selected['beta'], selected['base']), ('1/4', '3/4', 'T'))
        self.assertEqual([v['N_power'] for v in selected['normalized_error_energy']], ['-7/36', '-3/4'])
        self.assertEqual((transfer['C1'], transfer['C2']), ('26244', '27216'))
        self.assertFalse(transfer['full_finite_cube_bound_proved'])
        self.assertFalse(transfer['global_fixed_U_Mellin_bound_proved'])
        self.assertTrue(all(not t.get('subcritical_padding') for t in transfer['trials'] if Q(t['beta']) < Q(3, 4)))
        for t in transfer['trials']:
            _, ideals, _ = P.geometry_columns(t['alpha'], t['beta'])
            columns = [P.decode(t['column'])]+ideals
            source = {('E',)*3: Q(1), ('R',)*3: Q(-1)}
            cert = t['certificate']
            if cert['status'] == 'feasible':
                self.assertEqual(P.compose(columns, cert['solution']), source)
            else:
                y = P.decode(cert['dual'])
                self.assertTrue(all(sum(y.get(k, 0)*v for k, v in col.items()) == 0 for col in columns))
                self.assertNotEqual(sum(y.get(k, 0)*v for k, v in source.items()), 0)

    def test_global_moment_defect_is_nonzero_even_when_local_coefficients_agree(self):
        # Local equality does not identify full moments. This is the exact
        # scalar defect identity, using arbitrary rational moment values.
        A, E, R, S = Q(3, 5), Q(7, 4), Q(5, 6), Q(-2, 3)
        J = E-R
        direct = A**2*(E**3-R**3-3*S*S*J)
        factored = A**2*J*(E*E+E*R+R*R-3*S*S)
        self.assertEqual(direct, factored)
        self.assertNotEqual(direct, 0)
        self.assertNotEqual(direct, A**2*(E**3-R**3))

    def test_transfer_ablation_keeps_powers_and_pays_all_generic_logarithms(self):
        actual = P.transfer_search(2, '2/3', '1/24', METER)
        generic = P.transfer_search(2, '2/3', '1/24', METER, profile='bounded')
        a, b = actual['trials'][actual['selected']], generic['trials'][generic['selected']]
        self.assertEqual((a['alpha'], a['beta'], a['base']), (b['alpha'], b['beta'], b['base']))
        self.assertEqual([v['N_power'] for v in a['normalized_error_energy']],
                         [v['N_power'] for v in b['normalized_error_energy']])
        self.assertEqual([v['log_degree'] for v in b['normalized_error_energy']], [8, 4])
        self.assertEqual((generic['C1'], generic['C2']), ('26244', '33048'))
        with self.assertRaises(ValueError):
            P.transfer_search(2, '2/3', '1/24', METER, profile='unknown')

    def test_fractional_transfer_exponents_and_invalid_domains_remain_explicit(self):
        for theta in ['1/2', '3/4', '5/6']:
            t = P.transfer_search(1, theta, '1/24', METER)
            self.assertEqual(t['theta'], theta)
            self.assertTrue(all(v['analytic_moment_not_inferred_from_local_identity']
                                for v in t['trials'] if v['certificate']['status'] == 'feasible'))
        for theta in ['0', '1', '-1/3']:
            with self.assertRaises(ValueError):
                P.transfer_search(2, theta, '1/24', METER)
        with self.assertRaises(OverflowError):
            P.prefix_library('mobius', '1/24', Meter(0, 60))


def tearDownModule():
    print('operations='+str(METER.operations))


if __name__ == '__main__':
    unittest.main()
