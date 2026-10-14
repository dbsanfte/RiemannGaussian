"""Search behavior and soundness boundaries, without the held-out challenges."""
import unittest
from fractions import Fraction as F

import sympy as sp

import multiscale_bound_discovery as P


class DiscoveryTests(unittest.TestCase):
    def test_auxiliary_state_is_invented_and_output_subspace_preserves_cancellation(self):
        r = P.discover(lambda n: F((-1) ** n), 2)
        self.assertEqual(r['status'], 'open_closure_lemma')
        self.assertGreater(len(r['states']), 1)
        self.assertEqual(r['certificate']['bound']['alpha'], '0')
        # A good exact finite fit still needs a source theorem.
        self.assertFalse(r['bound_proved'])
        self.assertFalse(r['whole_signed_bound_proved'])
        ablation = P.discover(lambda n: F((-1) ** n), 2, P.no_state_expansion())
        self.assertEqual(ablation['status'], 'state_dimension_limit')

    def test_finite_alias_forces_state_expansion(self):
        source = lambda n: F(1 if n < 20 else (-1) ** n)
        r = P.discover(source, 2, dict(P.DEFAULT_SPEC, max_states=3))
        self.assertTrue(any(t['event'] == 'finite_counterexample' for t in r['trace']))
        self.assertFalse(r['bound_proved'])

    def test_global_counterexample_changes_search_constraints(self):
        calls = []
        def oracle(states, transitions):
            calls.append(1)
            if len(calls) == 1:
                return dict(verified=False, counterexample_n=500)
            return dict(verified=False, status='no_universal_rule')
        r = P.discover(lambda n: F(1), 2, closure_oracle=oracle)
        self.assertIn(500, r['training_indices'])
        self.assertEqual(len(calls), 2)
        self.assertEqual(r['status'], 'open_closure_lemma')
        self.assertEqual(r['certificate']['bound']['alpha'], '1')

    def test_arbitrary_fractional_exponent_uses_exact_powers(self):
        # A three-phase update gives exactly a cubic-root growth threshold.
        A = sp.Matrix([[0, 1, 0], [0, 0, 1], [2, 0, 0]])
        meter = P.Budget(P.DEFAULT_SPEC)
        bound, _ = P.synthesize_invariant(2, [P.encode_matrix(A), P.encode_matrix(sp.zeros(3))],
                                          P.DEFAULT_SPEC, meter)
        self.assertEqual(bound['alpha'], '1/3')
        L, Q = map(P.rational_matrix, (bound['block_transition'], bound['Q']))
        self.assertTrue(P.exact_psd(4 * Q - (L ** 3).T * Q * (L ** 3)))

    def test_false_metric_and_free_zero_pivot_are_rejected(self):
        self.assertFalse(P.exact_psd(sp.Matrix([[0, 1], [1, 0]])))
        self.assertFalse(P.exact_psd(sp.diag(1, 0), strict=True))
        self.assertTrue(P.exact_psd(sp.diag(1, 0)))

    def test_query_and_operation_stops_are_not_mathematical_obstructions(self):
        for change in [dict(max_queries=1), dict(operation_cap=0), dict(max_source_index=2)]:
            r = P.discover(lambda n: F(n % 7), 2, dict(P.DEFAULT_SPEC, **change))
            self.assertEqual(r['status'], 'resource_limit')
            self.assertFalse(r['bound_proved'])

    def test_unproved_numeric_closure_never_becomes_theorem(self):
        r = P.discover(lambda n: float((-1) ** n), 2)
        self.assertFalse(r['exact_observations'])
        self.assertEqual(r['status'], 'open_closure_lemma')
        self.assertFalse(r['RH_proved'])

    def test_nonzero_unit_is_not_erased(self):
        r = P.discover(lambda n: F(int(n == 0)), 2)
        self.assertEqual(r['certificate']['bound']['alpha'], '0')
        self.assertIn(0, r['training_indices'])
        with self.assertRaises(ValueError):
            P.discover(lambda n: F(0), 2, dict(P.DEFAULT_SPEC, initial_indices=[1, 2]))


if __name__ == '__main__':
    unittest.main()
