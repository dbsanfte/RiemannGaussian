"""Synthetic056 integration; no scientific arrays or prior suites."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest
import check_prime_insertion_core_056 as C
import prime_insertion_core_search_056 as S
import run_prime_insertion_core_056 as R

SM, CM = S.Meter(), C.Meter()


class IntegrationTests(unittest.TestCase):
    def test_partial_proof_admission(self):
        value = {'verified': True, 'tail_bound_proved': True, 'RH_proved': False,
            'complete_target_bound_proved': False}
        R.validate_verification(value, 'tail_bound_proved')
        for key in ['RH_proved', 'complete_target_bound_proved']:
            with self.assertRaises(ValueError): R.validate_verification(dict(value, **{key: True}), 'tail_bound_proved')
        with self.assertRaises(ValueError): R.validate_verification(dict(value, verified=False), 'tail_bound_proved')

    def test_signed_tail_includes_every_word_term(self):
        features = [[], [2], [7], [2, 7]]
        rows = []
        for feature in features:
            request = {'alpha': '3/11', 'primes': feature, 'tau': '3/4'}
            certificate = S.tail_certificate(request, SM)
            rows.append({'request': request, 'verification': C.verify_tail_bound(request, certificate, CM),
                'independently_verified': True})
        word = {'features': features, 'coefficients': ['1', '-1', '-1', '1']}
        combined = R.signed_tail_recovery(word, rows)
        expected = sum(Q(row['verification']['upper_bound']['constant']) for row in rows)
        self.assertEqual(Q(combined['uniform_sqrt_constant']), expected)
        self.assertEqual(len(combined['terms']), 4)
        self.assertFalse(combined['full_source_bound_proved'])
        with self.assertRaises(ValueError): R.signed_tail_recovery(word, rows[:-1])
        bad = deepcopy(rows); bad[-1]['request']['tau'] = '1'
        with self.assertRaises(ValueError): R.signed_tail_recovery(word, bad)

    def test_relations_discover_complete_insertion_words(self):
        archive = S.search_relations([[], [3], [7], [3, 7]], True, SM)
        counts = R.verify_relation_archive(archive, C, CM, SM)
        self.assertGreater(counts.get('EXACT_FIRST_JET_ZERO', 0), 0)
        words = R.insertion_words(archive)
        self.assertTrue(words)
        for word in words:
            self.assertTrue(word['primes'])
            self.assertEqual(word['operator_word']['D_primes'], [])
            self.assertFalse(word['operator_word']['full_source_bound_proved'])

    def test_program_builders_match_independent_rules(self):
        tail_request = {'alpha': '3/11', 'primes': [3, 7], 'tau': '1/2'}
        request = {'tail_request': tail_request, 'log_power': '2/13'}
        recovery = C.verify_low_core_recovery_schema(request, S.recovery_schema_certificate(request, SM), CM)
        self.assertTrue(recovery['verified'])
        self.assertFalse(recovery['conditional_original_target_implication'])
        self.assertFalse(recovery['low_core_bound_proved'])
        micro_request = {'alpha': '3/11', 'primes': [3, 7], 'gamma': '2/7'}
        certificate = S.microscopic_certificate(micro_request, SM)
        checked = C.verify_microscopic_bound(micro_request, certificate, CM)
        R.validate_verification(checked, 'near_zero_bound_proved')
        self.assertFalse(checked['complete_target_bound_proved'])


if __name__ == '__main__': unittest.main()
