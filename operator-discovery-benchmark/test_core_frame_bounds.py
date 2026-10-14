"""Generic exact algebra, conditional bounds, and countermodel calibration."""
from fractions import Fraction as Q
import unittest
from prime_bank_candidates import Meter
import core_cutoff_frame as F
import core_frame_bounds as P

M = Meter(50000000, 180)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_core_frame_bounds operations='+str(M.operations))


class FrameBoundTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.catalogue = F.catalogue(3, M)
        cls.result = P.synthesize(cls.catalogue, M)

    def test_exact_and_inexact_polynomial_division(self):
        divisor = {(0,): Q(1), (1,): Q(1)}
        q, r = P.division({(0, 0): Q(1), (1, 1): Q(1)}, divisor, 2, M)
        self.assertTrue(r)
        self.assertEqual(F.add(F.mul(q, divisor, M), r), {(0, 0): Q(1), (1, 1): Q(1)})
        desired = {(0, 2): Q(2, 3), (1, 1): Q(-5)}
        q, r = P.division(F.mul(divisor, desired, M), divisor, 3, M)
        self.assertEqual(q, desired)
        self.assertFalse(r)
        with self.assertRaises(ValueError): P.division(divisor, {}, 2, M)

    def test_all_candidates_and_both_proof_branches(self):
        self.assertEqual(len(self.result['certificates']), len(self.catalogue['candidates']))
        self.assertEqual({c['branch'] for c in self.result['certificates']}, {'exact_quotient', 'cauchy_quotient'})
        self.assertFalse(self.result['whole_signed_bound_proved'])
        for c in self.result['certificates']:
            self.assertTrue(all(len(t['monomial']) == 2 for t in c['bound_numerator']))
            self.assertFalse(c['uniform_actual_recovery_proved'])
            self.assertFalse(c['uniform_actual_residual_proved'])
            self.assertEqual(c['arithmetic_condition']['status'], 'open')

    def test_conditional_quadratic_bound_keeps_signed_crosses(self):
        for cert, frame in zip(self.result['certificates'], self.catalogue['candidates']):
            for d in ([Q(-3), Q(1), Q(2)], [Q(7, 3), Q(-2, 5), Q(-1)], [Q(0), Q(0), Q(1)]):
                s = P.value(P.decode(frame['normalizer']), d, M)
                p = P.value(P.decode(cert['recovery_numerator']), d, M)
                b = P.value(P.decode(cert['bound_numerator']), d, M)
                self.assertLessEqual(p, s*b)
                if s:
                    self.assertLessEqual(p/s**2, b/s)
        first = self.result['certificates'][0]
        normalizer = P.decode(first['arithmetic_condition']['left'])
        self.assertTrue(any(len(set(k)) > 1 and v < 0 for k, v in normalizer.items()))

    def test_symbolic_opposite_drift_calibration_has_uniform_half_bound(self):
        catalogue = F.catalogue(2, M)
        cert = P.synthesize(catalogue, M)['certificates'][0]
        # Substitute d0=t,d1=-t symbolically; all terms have degree2.
        def coefficient(poly):
            return sum(Q(term['coefficient'])*(-1)**term['monomial'].count(1) for term in poly)
        s = coefficient(cert['arithmetic_condition']['left'])
        b = coefficient(cert['bound_numerator'])
        self.assertEqual(s, 4)
        self.assertEqual(b, 2)
        self.assertEqual(s-2*b, 0)
        self.assertEqual(cert['branch'], 'exact_quotient')
        # S=4t^2>0 for t!=0; K=B/S=1/2 on the entire stated domain.
        self.assertEqual(b/s, Q(1, 2))

    def test_countermodel_preserves_recovery_while_residual_is_arbitrarily_large(self):
        for cert in self.result['certificates']:
            witness = cert['countermodel']
            w = list(map(Q, witness['weights']))
            d = list(map(Q, witness['drifts']))
            self.assertGreater(Q(witness['margin']), 0)
            self.assertLessEqual(Q(witness['recovery_cost']), 1/Q(witness['rho']))
            self.assertEqual(sum(w), 1)
            self.assertEqual(sum(x*y for x, y in zip(w, d)), 0)
            for T in (Q(0), Q(-7, 3), Q(10**9)):
                self.assertEqual(sum(x*(T-y) for x, y in zip(w, d)), T)
            self.assertFalse(witness['source_AST_satisfied'])
            self.assertFalse(witness['actual_source_bound_disproved'])
            self.assertEqual(cert['common_mode']['normalized_G_coefficient'], '1')
            self.assertFalse(cert['common_mode']['uniform_signed_control_added'])

    def test_witness_search_handles_a_different_kernel_basis(self):
        rows = [['0', '0', '1', '0'], ['0', '-1', '0', '-1'], ['0', '0', '1', '0']]
        sums = ['0', '-1', '2', '-1']
        v, s = list(map(F.linear, rows)), F.linear(sums)
        W = [F.mul(s, x, M) for x in v]
        S = F.mul(s, s, M)
        catalogue = dict(dimension=3, basis=[dict(id=0, vector=rows, sum=sums)], candidates=[dict(
            id=0, basis_ids=[0], normalizer=F.encode(S), weights=list(map(F.encode, W)))])
        cert = P.synthesize(catalogue, M)['certificates'][0]
        self.assertEqual(cert['countermodel']['drifts'], ['1', '0', '0'])
        self.assertEqual(cert['countermodel']['recovery_cost'], '1')

    def test_feedback_keeps_independent_residual_obligation_and_acyclic_dependencies(self):
        cert = self.result['certificates'][0]
        parent = dict(candidate_id=cert['id'], whole_signed_bound_proved=False)
        output = P.feedback(parent, cert, ['generic source representation'])
        nodes = {n['id']: n for n in output['proof_dependency_graph']}
        visited, active = set(), set()
        def visit(key):
            self.assertNotIn(key, active)
            if key in visited: return
            active.add(key)
            for dependency in nodes[key]['depends_on']: visit(dependency)
            active.remove(key)
            visited.add(key)
        visit('core_control')
        self.assertEqual(nodes['full_signed_residual_control']['status'], 'open')
        self.assertFalse(output['whole_signed_bound_proved'])
        self.assertEqual(output['search_feedback']['equivalent_rewrite_credit'], 0)
        self.assertTrue(output['search_feedback']['unknown_arithmetic_lemmas_remain_admissible'])

    def test_source_substitution_merges_actual_shared_moments(self):
        representations = [dict(geometry_id=i, alpha='1/3', gamma=gamma, drift=dict(theta='2/3',
            polynomial=[dict(powers=[2, 0, 0, 0], coefficient='2'), dict(powers=[0, 1, 0, 1], coefficient='-3')]))
            for i, gamma in enumerate(('1/3', '2/3'))]
        catalogue = F.catalogue(2, M)
        cert = P.synthesize(catalogue, M)['certificates'][0]
        bound = P.source_conditions(representations, [cert], M)[0]
        self.assertEqual(len(bound['variables']), 4)
        self.assertEqual([v.get('family') for v in bound['variables']], ['a', 'b', 'b', None])
        x = [Q(2), Q(-3), Q(1, 5), Q(4)]
        images = [P.value(P.decode(p), x, M) for p in bound['complete_drift_polynomials']]
        expected_s = P.value(P.decode(cert['arithmetic_condition']['left']), images, M)
        expected_b = P.value(P.decode(cert['bound_numerator']), images, M)
        self.assertEqual(P.value(P.decode(bound['denominator']), x, M), expected_s)
        self.assertEqual(P.value(P.decode(bound['recovery_bound_numerator']), x, M), expected_b)
        self.assertFalse(bound['arithmetic_inequality_proved'])

    def test_source_substitution_rejects_unrepresented_correction(self):
        representations = [dict(geometry_id=i, alpha='1/3', gamma='2/3', drift=dict(theta='2/3',
            polynomial=[dict(powers=[0, 0, 1, 0], coefficient='1')])) for i in range(2)]
        with self.assertRaises(ValueError): P.source_conditions(representations, [], M)


if __name__ == '__main__':
    unittest.main()
