"""New056 synthetic verification; no earlier scientific source is loaded."""
from fractions import Fraction as Q
import unittest
import prime_insertion_core_search_056 as S

M = S.Meter()


class SearchTests(unittest.TestCase):
    def test_microscopic_search_general_exponents_and_order(self):
        gammas = S.cutoff_grammar(18, '2', M)
        words = [{'primes': [7]}, {'primes': [3, 7]}]
        for power in ['1/2', '0']:
            result = S.search_microscopic('1/3', words, gammas, power, M)
            for row in result['selected']:
                gamma = Q(row['request']['gamma']); k = len(row['request']['primes'])
                self.assertEqual(gamma, (1-Q(power))/(k-Q(1, 3)))
                self.assertTrue(row['growth_sufficient'])
                self.assertFalse(row['middle_bound_proved'])
                self.assertFalse(row['certificate']['complete_target_bound_proved'])
        with self.assertRaises(ValueError):
            S.microscopic_certificate({'alpha': '1/3', 'primes': [], 'gamma': '1/2'}, M)

    def test_universal_recovery_without_fitted_constant(self):
        request = {'tail_request': {'alpha': '1/13', 'primes': [], 'tau': '3/4'}, 'log_power': '2/11'}
        certificate = S.recovery_schema_certificate(request, M)
        self.assertEqual(certificate['full_constant']['C_low_coefficient'], '1')
        self.assertNotIn('low_core', certificate['request'])
        self.assertIn('FOR EVERY', certificate['low_core_constant_quantifier'])
        self.assertFalse(certificate['low_core_bound_proved'])

    def test_boolean_word_identification_and_independent_check(self):
        features = [[], [2], [11], [2, 11]]
        vector = ['1', '-1', '-1', '1']
        word = S.factor_boolean_word(features, vector, M)
        self.assertEqual(word['E_primes'], [2, 11])
        self.assertTrue(S.verify_boolean_word(features, vector, word, M))
        bad = dict(word, E_primes=[2])
        with self.assertRaises(ValueError): S.verify_boolean_word(features, vector, bad, M)
        self.assertIsNone(S.factor_boolean_word(features, ['1', '-2', '0', '0'], M))

    def test_generic_cutoff_domain(self):
        cutoffs = S.cutoff_grammar(11, '7/5', M)
        self.assertIn('3/11', cutoffs)
        self.assertIn('7/5', cutoffs)
        self.assertNotIn('0', cutoffs)
        self.assertEqual(list(map(Q, cutoffs)), sorted(set(map(Q, cutoffs))))
        with self.assertRaises(ValueError): S.cutoff_grammar(True, meter=M)

    def test_selection_changes_with_requested_growth(self):
        cutoffs = S.cutoff_grammar(9, '2', M)
        for power in ['1/3', '2/3', '2/9']:
            result = S.search_cutoffs('3/7', [[], [7]], cutoffs, power, meter=M)
            self.assertTrue(all(Q(r['request']['tau']) == 1-Q(power) for r in result['selected']))
        result = S.search_cutoffs('3/7', [[]], ['1/7', '1/3'], '1/2', meter=M)
        self.assertEqual(result['selected'], [])

    def test_log_boundary_and_proof_scope(self):
        below = S.tail_certificate({'alpha': '1/11', 'primes': [], 'tau': '2/3'}, M)
        at = S.tail_certificate({'alpha': '1/11', 'primes': [2, 7], 'tau': '1'}, M)
        above = S.tail_certificate({'alpha': '1/11', 'primes': [2], 'tau': '5/4'}, M)
        self.assertEqual(below['upper_bound']['N_power'], '1/3')
        self.assertFalse(S.admits_growth(at['upper_bound'], '0', '0'))
        self.assertTrue(S.admits_growth(at['upper_bound'], '0', '1'))
        self.assertTrue(S.admits_growth(above['upper_bound'], '0', '0'))
        for row in [below, at, above]:
            self.assertFalse(row['complete_target_bound_proved'])
            self.assertFalse(row['RH_proved'])

    def test_invalid_primes_and_parameters(self):
        for primes in [[4], [2, 2], [3, 2], [True]]:
            with self.assertRaises(ValueError):
                S.tail_certificate({'alpha': '2/7', 'primes': primes, 'tau': '3/5'}, M)
        for alpha, tau in [('0', '1'), ('1', '1'), ('1/2', '0'), ('2/4', '1')]:
            with self.assertRaises(ValueError): S.tail_certificate({'alpha': alpha, 'primes': [], 'tau': tau}, M)

    def test_exact_row_reduction(self):
        matrices = [[[1, 2, 3, 4], [0, 1, 2, 3]], [[0, 0, 0, 0]],
            [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]]
        for matrix in matrices:
            result = S.nullspace(matrix, 4, M)
            self.assertEqual(len(result['basis'])+result['rank'], 4)
            for vector in result['basis']:
                self.assertTrue(any(vector))
                self.assertTrue(all(sum(a*b for a, b in zip(row, vector)) == 0 for row in matrix))
                self.assertGreater(next(x for x in vector if x), 0)

    def test_prime_class_matrix_retains_exceptions(self):
        features = [[], [2], [7], [2, 7]]
        source = S.first_jet_matrix(features, M)
        self.assertEqual(source['classes'], ['outside_generator_union', 2, 7])
        bounded = S.jet_certificate({'features': features, 'coefficients': ['1', '-1', '0', '0']}, M)
        self.assertEqual(bounded['status'], 'UNIFORM_FIRST_JET_BOUND')
        self.assertEqual(bounded['uniform_absolute_upper'], '1')
        self.assertFalse(bounded['first_jet_exact_zero_proved'])
        common = S.jet_certificate({'features': features, 'coefficients': ['0', '1', '0', '0']}, M)
        self.assertIsNone(common['uniform_absolute_upper'])
        self.assertEqual(common['common_coefficient'], '1')

    def test_learned_relations_and_ablation(self):
        features = [[], [3], [11], [3, 11]]
        enabled = S.search_relations(features, True, M)
        disabled = S.search_relations(features, False, M)
        self.assertTrue(any(r['certificate']['first_jet_exact_zero_proved'] for r in enabled['rows']))
        self.assertFalse(any(r['certificate']['first_jet_exact_zero_proved'] for r in disabled['rows']))
        for row in enabled['rows']:
            self.assertFalse(row['certificate']['low_core_bound_proved'])
            self.assertFalse(row['certificate']['full_kernel_cancellation_proved'])

    def test_conditional_recovery_not_proof(self):
        for primes in [[], [2]]:
            request = {'tail_request': {'alpha': '2/9', 'primes': primes, 'tau': '1'},
                'low_core': {'constant': '3/2', 'log_power': '4/7', 'status': 'OPEN'}}
            certificate = S.recovery_certificate(request, M)
            self.assertEqual(Q(certificate['full_constant']), Q(3, 2)+20*2**len(primes))
            self.assertEqual(certificate['conditional_original_target_implication'], primes == [])
            self.assertEqual(certificate['log_weight'], '(1+log(N))^log_power')
            self.assertFalse(certificate['complete_target_bound_proved'])
            request['tail_request']['tau'] = '1/3'
            self.assertIsNone(S.recovery_certificate(request, M)['full_constant'])


if __name__ == '__main__':
    unittest.main()
