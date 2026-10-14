"""New synthetic tests of source-bound recurrence discovery and recovery."""
from fractions import Fraction as Q
import unittest
import prime_insertion_middle_search_057 as S

M = S.Meter()


class SearchTests(unittest.TestCase):
    def test_actual_feature_semantics_and_general_transports(self):
        S.validate_features(S.DEFAULT_FEATURES)
        weights = S.parent_transports(5, M)
        self.assertTrue(any('1/5' in row['weights'] for row in weights))
        for row in weights:
            self.assertEqual(sum(map(Q, row['weights'])), 1)
            self.assertTrue(all(Q(w) >= 0 for w in row['weights']))
        bad = [dict(S.DEFAULT_FEATURES[0], primes=[4]), S.DEFAULT_FEATURES[1]]
        with self.assertRaises(ValueError): S.validate_features(bad)

    def test_grammar_retains_signed_auxiliaries_and_moving_band_sources(self):
        features = [S.feature([7], '1/11'), S.feature([3, 7], '5/13'), S.feature([7], '1/11', '2/5')]
        grammar = S.grammar(features, M)
        self.assertTrue(any(form['signed_auxiliary'] for form in grammar['forms']))
        self.assertEqual(grammar['features'], features)
        self.assertFalse(grammar['proof_provider_used'])
        self.assertIn('1/7', grammar['decay_exponents'])
        self.assertEqual(S.source_request('2/7', features[2], 19)['upper_fraction'], '2/5')

    def test_all_neighbor_and_child_arguments_are_present(self):
        numbers = S.sample_numbers([3, 11])
        self.assertEqual(numbers, [2, 3, 4, 6, 7, 10, 11, 12, 22, 23])
        with self.assertRaises(ValueError): S.sample_numbers([2])

    def test_finite_training_does_not_prove_new_scale(self):
        form = {'id': 'test', 'coefficients': [0, 0], 'lambda': '0', 'support': [], 'baseline': True, 'signed_auxiliary': False}
        scales = [3, 4, 5, 6]
        values = {n: [(Q(n), Q(n)), (Q(0), Q(0))] for n in S.sample_numbers(scales)}
        transport = {'id': 'center', 'weights': ['0', '1', '0'], 'center_only': True}
        decays = {'0': {n: (Q(1), Q(1)) for n in scales}}
        row = S.score_form(form, values, scales, [transport], decays, [Q(0), Q(4), Q(8)], M)[0]
        self.assertEqual(row['C'], '8')
        # Synthetic J(n)=n has F(n)=n, so a later center n=10 violatesC8.
        self.assertGreater(Q(20)-Q(10), Q(row['C']))
        self.assertFalse(row['uniform_recurrence_proved'])

    def test_archive_keeps_weak_growth_and_different_control_families(self):
        forms = [
            {'id': 'control', 'coefficients': [0, 0], 'lambda': '0', 'support': [], 'baseline': True, 'signed_auxiliary': False},
            {'id': 'signed', 'coefficients': [1, -1], 'lambda': '1', 'support': [0, 1], 'baseline': False, 'signed_auxiliary': True}]
        transports = [{'id': 'center', 'weights': ['0', '1', '0'], 'center_only': True},
            {'id': 'shift', 'weights': ['1/3', '0', '2/3'], 'center_only': False}]
        rows = []
        for delta in ['0', '2/7']:
            for form in forms:
                for transport in transports:
                    rows.append({'id': delta+form['id']+transport['id'], 'form': form, 'transport': transport,
                        'delta': delta, 'C': '2', 'required_training_C_upper': '3/2', 'status': 'FINITE_TRAINING_PASS'})
        selected = S.select(rows)
        self.assertEqual(len(selected['selected']), 6)
        self.assertEqual({r['delta'] for r in selected['selected']}, {'0', '2/7'})
        self.assertFalse(selected['final_values_used'])

    def test_recovery_coercivity_all_bases_and_shifted_tree(self):
        request = {'alpha': '2/9', 'features': [S.feature([3], '7/11'), S.feature([2, 5], '2/7')],
            'coefficients': [1, -2], 'lambda': '1/3', 'weights': ['1/3', '0', '2/3'], 'delta': '3/11', 'C': '5/7'}
        certificate = S.recovery_certificate(request)
        b0, b1 = list(map(Q, certificate['source_envelopes']))
        self.assertEqual(Q(certificate['base_upper']), 5*(b0*b0+Q(1, 3)*(b0+2*b1)**2))
        self.assertEqual(certificate['recovery']['argument_shift'], 2)
        self.assertEqual(certificate['recovery']['base_maximum'], 5)
        cross = next(x for x in certificate['matrix_terms'] if x['i'] == 0 and x['j'] == 1)
        self.assertEqual(cross['coefficient'], '-4/3')
        self.assertFalse(certificate['uniform_middle_bound_proved'])
        request['delta'] = '0'
        zero = S.recovery_certificate(request)
        self.assertEqual(zero['recovery']['kind'], 'logarithmic')
        self.assertEqual(zero['recovery']['log_coefficient'], '5/7')

    def test_bad_transport_and_insufficient_pointwise_provider(self):
        request = {'alpha': '1/5', 'features': S.DEFAULT_FEATURES[:2], 'coefficients': [1, -1],
            'lambda': '1', 'weights': ['0', '1', '0'], 'delta': '1/7', 'C': '1'}
        certificate = S.recovery_certificate(request)
        attempt = S.proof_attempt(request, certificate)
        self.assertEqual(attempt['status'], 'POINTWISE_PROVIDER_INSUFFICIENT')
        self.assertFalse(attempt['uniform_middle_bound_proved'])
        request['weights'] = ['1', '1', '0']
        with self.assertRaises(ValueError): S.recovery_certificate(request)


if __name__ == '__main__': unittest.main()
