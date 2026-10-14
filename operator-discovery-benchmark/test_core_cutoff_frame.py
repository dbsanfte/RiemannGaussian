"""Generic semantics and counterexamples; no actual-source pilot observations."""
from fractions import Fraction as Q
import unittest
from flint import arb, ctx
from prime_bank_candidates import Meter
import core_cutoff_frame as P

M = Meter(60000000, 180)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_core_cutoff_frame operations='+str(M.operations))


def literal(poly, d):
    result = Q(0)
    for t in poly:
        value = Q(t['coefficient'])
        for i in t['monomial']:
            value *= d[i]
        result += value
    return result


class CutoffFrameTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 192
        cls.catalogues = {n: P.catalogue(n, M) for n in (2, 3, 5)}

    def test_generic_nullspace_and_all_subsets(self):
        for n, c in self.catalogues.items():
            nullity = n*(n-1)//2
            self.assertEqual(len(c['basis']), nullity)
            self.assertEqual(c['constraint_rank'], n*(n+1)-nullity)
            self.assertEqual(len(c['candidates']), 2**nullity-1)
            for item in c['candidates']:
                self.assertTrue(item['normalizer_nonnegative_proved'])
                self.assertFalse(item['normalizer_positive_proved'])
        self.assertFalse(self.catalogues[5]['whole_signed_bound_proved'])

    def test_exact_signed_recovery_for_generic_rational_inputs(self):
        c = self.catalogues[3]
        for d in ([Q(-2), Q(3, 7), Q(5)], [Q(0), Q(0), Q(-9, 2)]):
            for item in c['candidates']:
                S = literal(item['normalizer'], d)
                W = [literal(w, d) for w in item['weights']]
                self.assertGreaterEqual(S, 0)
                self.assertEqual(sum(W), S)
                self.assertEqual(sum(w*t for w, t in zip(W, d)), 0)
                if S:
                    self.assertEqual(sum(w/S for w in W), 1)

    def test_recovery_keeps_paid_vectors_and_all_crosses(self):
        c = self.catalogues[3]
        item = c['candidates'][-1]
        d = [Q(2), Q(-1), Q(7)]
        S = literal(item['normalizer'], d)
        weights = [literal(w, d)/S for w in item['weights']]
        g, J = [Q(3), Q(-5), Q(1)], [Q(2), Q(7), Q(-4)]
        paid = [[Q(1), Q(2), Q(3)], [Q(-2), Q(1), Q(0)], [Q(4), Q(-3), Q(2)]]
        residual = [[g[t]-paid[i][t]-d[i]*J[t] for t in range(3)] for i in range(3)]
        joined = [sum(weights[i]*residual[i][t] for i in range(3)) for t in range(3)]
        restored = [joined[t]+sum(weights[i]*paid[i][t] for i in range(3)) for t in range(3)]
        self.assertEqual(restored, g)
        energy = lambda v: sum(x*x for x in v)
        K = sum(w*w for w in weights)
        self.assertLessEqual(energy(g), 2*energy(joined)+2*K*sum(energy(v) for v in paid))
        diagonal = sum(weights[i]**2*energy(residual[i]) for i in range(3))
        self.assertNotEqual(energy(joined), diagonal)

    def test_equal_nonzero_drifts_cannot_recover_core(self):
        for c in self.catalogues.values():
            n = c['dimension']
            for item in c['candidates']:
                self.assertEqual(literal(item['normalizer'], [Q(1)]*n), 0)
        c = self.catalogues[3]
        result = P.evaluate(c['candidates'][-1], c['basis'], [arb(1)]*3, [(1, 1)]*3, M)
        self.assertEqual(result['status'], 'exact_singular')
        self.assertIsNone(result['K'])

    def test_interval_uncertainty_is_not_exact_zero(self):
        c = self.catalogues[2]
        result = P.evaluate(c['candidates'][0], c['basis'], [arb('1 +/- 0.1')]*2, [(1, 1), (2, 3)], M)
        self.assertEqual(result['status'], 'unresolved_positive')
        self.assertIsNone(result['lambda'])
        result = P.evaluate(c['candidates'][0], c['basis'], [arb(-2), arb(3)], [(1, 1), (2, 3)], M)
        self.assertEqual(result['status'], 'certified_positive')
        self.assertTrue((sum(result['lambda'], arb(0))-1).contains(0))

    def test_integer_cutoffs_at_fractional_root_boundaries(self):
        for exponent in ('1/2', '1/3', '1/6', '5/6', '2/3'):
            r = Q(exponent)
            for N in (1, 3, 7, 8, 63, 64, 65, 728, 729, 730):
                U = P.cutoff(N, exponent)
                self.assertLessEqual(U**r.denominator, N**r.numerator)
                self.assertGreater((U+1)**r.denominator, N**r.numerator)

    def test_complete_moments_and_mobius_inverse(self):
        mu = [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1]
        requests = dict(a=[1, 4, 9, 10], b=[2, 6, 10])
        out = P.moments(mu, requests, M)
        for name, power in [('a', arb(2)/3), ('b', arb(4)/3)]:
            for N in requests[name]:
                direct = sum((mu[n]*(-power*arb(n).log()).exp() for n in range(1, N+1)), arb(0))
                self.assertTrue(out[name][str(N)].overlaps(direct))
        self.assertEqual(out['effective_cutoffs']['9'], 7)
        mu[4] = 1
        with self.assertRaises(ValueError):
            P.moments(mu, requests, M)

    def test_drift_uses_input_polynomial_and_rejects_unimplemented_moment(self):
        poly = [dict(powers=[2, 0, 0, 0], coefficient='2'), dict(powers=[0, 1, 0, 1], coefficient='-3')]
        self.assertTrue(P.drift(poly, arb(2), arb(3), arb(5), M) == -37)
        poly.append(dict(powers=[0, 0, 1, 0], coefficient='1'))
        with self.assertRaises(ValueError):
            P.drift(poly, arb(2), arb(3), arb(5), M)

    def test_feedback_does_not_promote_finite_conditioning_to_core_bound(self):
        item = self.catalogues[2]['candidates'][0]
        out = P.feedback(item, ['generic'], 'finite_recovery_observed')
        self.assertEqual({r['id'] for r in out['required']}, {'eventual_nonsingularity', 'recovery_cost', 'signed_residual', 'finite_head'})
        self.assertTrue(all(r['status'] == 'open' for r in out['required']))
        self.assertFalse(out['whole_signed_bound_proved'])
        self.assertFalse(out['uniform_signed_residual_proved'])
        self.assertTrue(out['all_residual_crosses_retained'])


if __name__ == '__main__':
    unittest.main()
