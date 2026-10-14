import unittest
from fractions import Fraction as Q

import mobius_prime_moment_075 as S


class SourceAndSearch(unittest.TestCase):
    def test_exact_rational_lattice_and_units(self):
        M, _ = S.arithmetic(400, S.Meter())
        for t in [Q(a, b) for a in range(120) for b in (7, 13, 31)]:
            def old_z(v):
                return M[int(10*v)]-M[int(8*v)]-M[int(20*v)]+M[int(16*v)]
            self.assertEqual(old_z(t), S.G(int(80*t), M))
            for d in (2, 3, 6, 17):
                self.assertEqual(old_z(t/d), S.G(int(80*t)//d, M))
        self.assertEqual([S.G(u, M) for u in range(10)], [0, 0, 0, 0, -1, 0, 0, 0, 2, 2])

    def test_grid_refinement_preserves_exported_operator(self):
        spec = dict(grid=80, theta=['1/2', '7/11', '3/4', '7/8'], multipliers=[6])
        obligations = dict(candidates=[dict(candidate_file='old', obligation=dict(rays=[
            dict(status='EXACT_SIGNED_PRIME_DILATION_IDENTITY', ray=3,
                 prime_blocks=[dict(lower_theta='1/2', upper_theta='3/4', coefficient='2'),
                               dict(lower_theta='3/4', upper_theta='7/8', coefficient='-1')])]))])
        found = [r for r in S.catalog(spec, obligations) if 'old:ray3' in r['origins']]
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0]['shape'], ['1', '1', '-1/2', '0'])

    def test_exact_prices_and_positive_square_root(self):
        spec = dict(grid=80, theta=['1/2', '17/31', '53/61'], multipliers=[2, 6])
        H = S.price_bounds(spec, 64)
        self.assertEqual(H[-2:], [Q(1, 2), Q(1, 6)])
        M, pi = S.arithmetic(1000, S.Meter())
        for x in (16, 17, 100, 1000):
            theta = list(map(Q, spec['theta']))
            cuts = [S.B.floor_power(x, t) for t in theta]
            for i, (lo, hi) in enumerate(zip(cuts, cuts[1:])):
                reciprocal = sum((Q(1, p) for p in range(lo+1, hi+1) if pi[p]>pi[p-1]), Q(0))
                self.assertLessEqual(reciprocal, H[i])
        for value in (Q(0), Q(1, 9), Q(17, 31), Q(999, 1000)):
            root = S.sqrt_upper(value)
            self.assertGreaterEqual(root, 0)
            self.assertGreaterEqual(root*root, value)

    def test_arbitrary_rational_power_enclosures(self):
        for q in (Q(17, 13), Q(101, 97), Q(1001, 1000)):
            for n in (1, 7, 31):
                lo, hi = S.B.power_bounds(n, q, 10)
                self.assertLessEqual(lo**q.denominator, n**q.numerator)
                self.assertGreaterEqual(hi**q.denominator, n**q.numerator)

    def test_signed_lp_proposal_and_correlation_control(self):
        spec = dict(grid=80, theta=['1/2', '3/4'], multipliers=[2, 3])
        rows = [dict(u=17+i, z=x-y, components=[0, x, y], moments=[0, x*x, y*y])
                for i, (x, y) in enumerate([(1, 0), (0, 1), (1, 1), (-2, 1), (3, -2)])]
        data = dict(spec=spec, rows=rows)
        learned = S.minimax_directions(data, ['1'], S.Meter())
        direct = next(r for r in learned if r.get('kind') == 'direct_only')
        shape = list(map(Q, direct['shape']))
        self.assertEqual(shape, [0, 1, -1])
        beta, receipt = S.fit_beta(shape, rows, [Q(1), Q(1, 2), Q(1, 3)], S.Meter())
        self.assertEqual(S.correlation_assessment(shape, beta, rows, S.Meter())['failures'], 0)
        universal = S.cauchy_beta(shape)
        self.assertEqual(sum((a*a/b for a, b in zip(shape, universal) if b), Q(0)), 1)

    def test_scaling_cannot_hide_a_correlation_counterexample(self):
        shape, beta = [Q(1)], [Q(1)]
        rows = [dict(u=100, components=[6], moments=[12])]
        a = S.correlation_assessment(shape, beta, rows, S.Meter())
        b = S.correlation_assessment([Q(1, 1000)], [Q(1, 1000000)], rows, S.Meter())
        self.assertEqual(a['failures'], 1)
        self.assertEqual(b['failures'], 1)
        self.assertEqual(Q(a['first']['gap'])/1000000, Q(b['first']['gap']))

    def test_feedback_preserves_refutation_and_ambiguity(self):
        p = dict(base_u=16, q='1', operator=['1'], beta=['1'], innovation_C='1', spec={})
        evaluation = dict(failures=[dict(u=17, lemma='innovation', status='UNRESOLVED_ROUNDING'),
                                   dict(u=18, lemma='innovation', status='REFUTED')])
        leaves = S.next_obligations(dict(program=p), evaluation)
        leaf = next(l for l in leaves if l['lemma'] == 'innovation')
        self.assertEqual(leaf['status'], 'FINITE_COUNTEREXAMPLE')
        self.assertEqual(leaf['first_witness']['u'], 18)
        evaluation['failures'].pop()
        leaf = S.next_obligations(dict(program=p), evaluation)[1]
        self.assertEqual(leaf['status'], 'FINITE_ROUNDING_UNRESOLVED')

    def test_resource_gates_precede_matrix_allocation(self):
        class Reject(S.Meter):
            def reserve(self, n):
                raise MemoryError('test gate')
        with self.assertRaises(MemoryError):
            S.make_data(S.SOURCE_SPEC, [160], Reject())
        with self.assertRaises(MemoryError):
            S.fit_beta([Q(1)], [dict(components=[1], moments=[1])], [Q(1)], Reject())


if __name__ == '__main__':
    unittest.main()
