"""Synthetic capability checks; no actual core observations or target scores."""
import unittest
import sympy as S
import prime_cofactor_discovery as P


def model():
    return dict(lattice=6, channels=[
        dict(atoms=[dict(kind='mu', shift=1)], weight=['2', '0']),
        dict(atoms=[dict(kind='power', shift=3)], weight=['-1', '0']),
        dict(atoms=[dict(kind='mu', shift=2)], weight=['0', '1'])])


class Discovery(unittest.TestCase):
    def test_companions_are_generated_from_source(self):
        result = P.discover(model())
        self.assertEqual(result['status'], 'universal_law_proposed')
        self.assertEqual(len(result['states']), 3)
        self.assertTrue(all(x['program']['op'] == 'jet' for x in result['states'][1:]))
        self.assertFalse(result['whole_signed_bound_proved'])

    def test_no_state_expansion_fails_nontrivial_source(self):
        result = P.discover(model(), dict(max_states=1))
        self.assertEqual(result['status'], 'unclosed_prime_module')
        self.assertEqual(result['stop'], 'state_cap')

    def test_identical_modes_need_only_observable_quotient(self):
        source = dict(lattice=6, channels=[
            dict(atoms=[dict(kind='mu', shift=2)], weight=['1', '0']),
            dict(atoms=[dict(kind='mu', shift=2)], weight=['-3', '0'])])
        result = P.discover(source)
        self.assertEqual(len(result['states']), 1)
        self.assertEqual(result['status'], 'universal_law_proposed')

    def test_frontier_leading_sign_and_fractional_exponent(self):
        local = [-P.Q + P.Q**4]  # use a genuine local-series coefficient
        local = [1+P.T*local[0]]
        bound = P.frontier_bound(0, S.Matrix([[1]]), local, [S.Integer(2)], P.Budget())
        self.assertEqual(bound['r'], '1/6')
        self.assertEqual(bound['sign'], -1)
        self.assertEqual(bound['energy_lower_exponent'], '2/3')
        self.assertEqual(bound['q_threshold'], '1/2')
        self.assertIs(bound['refutes_separate_subpower_payment'], True)

    def test_uncertain_leading_coefficient_is_not_skipped(self):
        bound = P.frontier_bound(0, S.Matrix([[1, 1]]),
            [1+P.T*P.Q, 1+P.T*P.Q**2], [P.R-3, S.Integer(1)], P.Budget())
        self.assertEqual(bound['lead_degree'], 1)
        self.assertEqual(bound['status'], 'unresolved_leading_coefficient')
        self.assertIsNone(bound['energy_lower_exponent'])

    def test_joined_search_uses_obstruction_and_detects_restatement(self):
        bound = dict(state=0, energy_lower_exponent='2/3')
        result = P.search_joined_forms(bound)
        self.assertEqual(len(result['rows']), 275)
        self.assertGreater(result['counts']['refuted_by_rough_lower_bound'], 0)
        self.assertEqual(result['counts']['endpoint_restatement'], 4)
        self.assertEqual(sum(result['counts'].values()), 275)
        self.assertFalse(result['broader_multiscale_grammar_refuted'])


if __name__ == '__main__':
    unittest.main()
