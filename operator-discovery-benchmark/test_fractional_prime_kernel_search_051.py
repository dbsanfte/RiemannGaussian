"""Synthetic kernel/calibration/selection fixtures; no scientific bank run."""
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest
from unittest.mock import patch
from flint import arb, ctx

import fractional_prime_kernel_search_051 as S

METERS = []


def meter(**kwargs):
    value = S.Meter(**kwargs)
    METERS.append(value)
    return value


def request(a='0', b='1', alpha='1', sign=1):
    return {'a': a, 'b': b, 'alpha': alpha, 'sign': sign}


def bounds(row):
    return S._interval(row['value'])


def reference_contains(test, row, expression, work):
    with ctx.workprec(256):
        expected = expression()
        work.charge(32+256*256)
        lo, hi = S._interval(S._enclosure(expected))
    lower, upper = bounds(row)
    test.assertLessEqual(lower, lo)
    test.assertGreaterEqual(upper, hi)


class KernelTests(unittest.TestCase):
    def setUp(self):
        self.original_cache = S.CACHE
        S.CACHE = S.KernelCache(max_bytes=2*1024**2)

    def tearDown(self):
        S.CACHE = self.original_cache

    def test_exact_schema_canonicalization_and_domains(self):
        work = meter()
        bads = [request('01', '0'), request('1/2', '1/2'),
                request('1/3', '1/3'), request(alpha='0'), request(alpha='5/2'),
                request(sign=True), request(a=0), {**request(), 'extra': 1}]
        for bad in bads:
            with self.assertRaises(ValueError):
                S.evaluate(bad, 2, meter=work)
        with self.assertRaises(OverflowError):
            S.evaluate(request(a=str(1 << 4096)), 2, meter=work)
        for n in (0, -1, True, 2**32):
            with self.assertRaises(ValueError):
                S.evaluate(request(), n, meter=work)
        for precision in (127, True, 1025):
            with self.assertRaises(ValueError):
                S.evaluate(request(), 2, precision, work)

    def test_factorization_and_squarefree_divisors_retain_primepowers(self):
        row = S.evaluate(request('1/3', '2/3'), 12, meter=meter())
        self.assertEqual(row['factorization'], [{'prime': 2, 'exponent': 2},
                                               {'prime': 3, 'exponent': 1}])
        self.assertEqual(row['ordinary_mu_n'], 0)
        self.assertEqual([(v['d'], v['mu'], v['log_arguments'][1])
                          for v in row['squarefree_divisors']],
                         [(1, 1, 12), (2, -1, 6), (3, -1, 4), (6, 1, 2)])
        self.assertFalse(row['all_scale_sign_proved'])
        self.assertFalse(row['proof_provider_used'])
        lo, hi = bounds(row)
        self.assertLessEqual(lo, 0)
        self.assertGreaterEqual(hi, 0)

    def test_von_mangoldt_signed_calibration_on_primepower(self):
        work = meter()
        row = S.evaluate(request('2/3', '1/3', sign=-1), 27, meter=work)
        self.assertEqual(row['finite_sign'], 'FINITE_NONNEGATIVE')
        self.assertTrue(row['strict_positive'])
        self.assertFalse(row['prime'])
        reference_contains(self, row, lambda: arb(3).log()/3, work)

    def test_quadratic_signed_mixed_prime_kernel(self):
        work = meter()
        row = S.evaluate(request(alpha='2'), 12, meter=work)
        self.assertTrue(row['strict_positive'])
        self.assertEqual(row['distinct_prime_count'], 2)
        reference_contains(self, row, lambda: 2*arb(2).log()*arb(3).log(), work)
        negative = S.evaluate(request(alpha='2', sign=-1), 12, meter=work)
        self.assertEqual(negative['finite_sign'], 'FINITE_NEGATIVE')
        self.assertLess(bounds(negative)[1], 0)
        ratio_lo, ratio_hi = S._interval(row['signed_over_absolute'])
        self.assertGreater(ratio_lo, 0)
        self.assertLess(ratio_hi, 1)

    def test_three_prime_quadratic_cancellation_is_not_promoted(self):
        row = S.evaluate(request(alpha='2'), 30, meter=meter())
        lo, hi = bounds(row)
        self.assertLessEqual(lo, 0)
        self.assertGreaterEqual(hi, 0)
        if lo < 0:
            self.assertEqual(row['finite_sign'], 'UNRESOLVED_SIGN')
        self.assertFalse(row['uniform_bound_proved'])

    def test_fractional_primepower_log_right_argument(self):
        work = meter()
        row = S.evaluate(request(alpha='1/2'), 4, meter=work)
        reference_contains(self, row, lambda: arb(4).log().sqrt()-arb(2).log().sqrt(), work)
        left = S.evaluate(request('1', '0', '1/2', -1), 4, meter=work)
        reference_contains(self, left, lambda: arb(2).log().sqrt(), work)
        self.assertLess(bounds(row)[1], bounds(left)[0])

    def test_unit_zero_and_arbitrary_rational_denominator(self):
        work = meter()
        row = S.evaluate(request('1/3', '2/3', '1/257'), 1, meter=work)
        self.assertEqual(bounds(row), (0, 0))
        self.assertTrue(row['exact_zero_enclosure'])
        self.assertEqual(row['ordinary_mu_n'], 1)
        self.assertIsNone(row['normalized_by_log_n_alpha'])
        self.assertIsNone(row['signed_over_absolute'])
        nonzero = S.evaluate(request('1/3', '2/3', '1/257'), 2, meter=work)
        self.assertTrue(nonzero['strict_positive'])
        self.assertEqual(nonzero['finite_sign'], 'FINITE_NONNEGATIVE')

    def test_functional_cache_shares_sign_and_separates_precision(self):
        first_work, second_work, higher_work = meter(), meter(), meter()
        first = S.evaluate(request('1/3', '2/3', '2/3'), 18, 128, first_work)
        second = S.evaluate(request('1/3', '2/3', '2/3', -1), 18, 128, second_work)
        self.assertEqual(second_work.factor_divisions, 0)
        self.assertEqual(second_work.log_evaluations, 0)
        self.assertEqual(second_work.power_evaluations, 0)
        self.assertGreater(second_work.cache_hits, 0)
        self.assertEqual(bounds(second), (-bounds(first)[1], -bounds(first)[0]))
        higher = S.evaluate(request('1/3', '2/3', '2/3'), 18, 192, higher_work)
        self.assertGreater(higher_work.log_evaluations, 0)
        self.assertGreater(higher_work.power_evaluations, 0)
        self.assertLess(bounds(higher)[1]-bounds(higher)[0], bounds(first)[1]-bounds(first)[0])
        self.assertFalse(S.CACHE.metadata()['artifact_hashes_used'])

    def test_complete_rational_grammar_and_named_calibration_separation(self):
        work = meter()
        bank = S.grammar(meter=work)
        self.assertEqual(bank['candidate_count'], 3024)
        self.assertEqual(len(bank['discovery']), 2988)
        self.assertEqual(len(bank['calibrations']), 36)
        self.assertEqual(len({v['id'] for v in bank['discovery']+bank['calibrations']}), 3024)
        for entry in bank['discovery']+bank['calibrations']:
            a, b, alpha, sign = S._request(entry['request'], work)
            self.assertLessEqual(a.denominator, 7)
            self.assertLessEqual(alpha.denominator, 11)
            self.assertEqual(alpha == 1, entry['role'] == 'vonMangoldt_calibration')
        self.assertEqual(len(S.CACHE.atoms), 0)

    def test_explicit_work_candidate_and_cache_memory_guards(self):
        with self.assertRaises(OverflowError):
            S.grammar(meter=meter(cap=0))
        with self.assertRaises(OverflowError):
            S.grammar({'a_denominator': 4096, 'alpha_denominator': 4096,
                       'max_candidates': 8}, meter=meter())
        with self.assertRaises(ValueError):
            S.grammar({'a_denominator': True}, meter=meter())
        work = meter()
        with self.assertRaises(MemoryError):
            work.reserve(S.MAX_SEARCH_BYTES+1)
        S.CACHE = S.KernelCache(max_bytes=0)
        row = S.evaluate(request(), 8, meter=work)
        self.assertTrue(row['strict_positive'])
        self.assertEqual(S.CACHE.bytes_estimate, 0)
        self.assertGreater(work.peak_bytes_estimate, 0)

    def test_synthetic_search_early_exit_and_full_coverage(self):
        work = meter()
        def injected(req, n, precision, supplied_meter):
            supplied_meter.charge(16)
            negative = req['sign'] == -1 and n == 3
            enclosure = S._enclosure(arb(-1 if negative else 1))
            return {'n': n, 'value': enclosure,
                    'normalized_by_log_n_alpha': enclosure,
                    'finite_sign': 'FINITE_NEGATIVE' if negative else 'FINITE_NONNEGATIVE',
                    'strict_positive': not negative, 'exact_zero_enclosure': False,
                    'prime': n in (2, 3), 'distinct_prime_count': 2 if n == 6 else 1,
                    'synthetic_injected_response': True}
        with patch.object(S, 'evaluate', injected):
            result = S.search({'grammar': {'a_denominator': 1, 'alpha_denominator': 1,
                                          'max_candidates': 8},
                               'precision': 192, 'irregular_numbers': [9]}, [2, 3, 6], work)
        for row in result['rows']+result['calibrations']:
            if row['request']['sign'] == -1:
                self.assertEqual(row['observed_count'], 2)
                self.assertEqual(row['skipped_after_counterexample'], [6, 9])
                self.assertFalse(row['full_training_coverage'])
                self.assertFalse(row['eligible_for_finite_archive'])
            else:
                self.assertTrue(row['full_training_coverage'])
                self.assertEqual(row['observed_count'], 4)
        self.assertFalse(result['fresh_final_numbers_seen_by_selector'])
        self.assertEqual(len(S.CACHE.atoms), 0)

    def test_selector_diversity_and_unresolved_labels_with_synthetic_rows(self):
        def fixture(name, alpha, height, composite=True, unresolved=False):
            return {'id': name, 'role': 'discovery', 'request': request(alpha=alpha),
                    'complexity': {'rational_height': height, 'a_denominator': 1,
                                   'alpha_denominator': Q(alpha).denominator},
                    'full_training_coverage': True, 'finite_negative_witness': None,
                    'strict_positive_prime_responses': [2, 3],
                    'strict_positive_multiprime_responses': [6] if composite else [],
                    'finite_status': 'NO_FINITE_NEGATIVE_WITH_UNRESOLVED' if unresolved else 'FINITE_NONNEGATIVE_ALL_TESTED'}
        rows = [fixture('toy_a', '1/2', 8), fixture('toy_b', '1/2', 9),
                fixture('toy_c', '2/3', 10, unresolved=True), fixture('toy_d', '3/4', 1, False)]
        negative = fixture('negative_toy', '1/3', 1)
        negative['finite_negative_witness'] = {'n': 2}
        incomplete = fixture('incomplete_toy', '1/3', 1)
        incomplete['full_training_coverage'] = False
        calibration = fixture('calibration_toy', '1', 1)
        calibration['role'] = 'vonMangoldt_calibration'
        archive = S.select(rows+[negative, incomplete, calibration], limit=3)
        self.assertEqual([v['id'] for v in archive['selected']], ['toy_a', 'toy_c', 'toy_d'])
        self.assertEqual(archive['selected'][1]['finite_status'], 'NO_FINITE_NEGATIVE_WITH_UNRESOLVED')
        self.assertFalse(archive['all_scale_sign_proved'])
        self.assertFalse(archive['proof_provider_used'])
        self.assertEqual(S.select(rows, limit=0)['selected'], [])
        with self.assertRaises(ValueError):
            S.select([rows[0], rows[0]])


if __name__ == '__main__':
    path = Path(__file__).with_name('fractional_prime_kernel_search_051_development.json')
    if path.exists():
        raise SystemExit('retain prior focused development receipt')
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(KernelTests))
    receipt = {'schema': 'fractional-prime-kernel-051-development-v1', 'invocations': [{
        'returncode': 0 if result.wasSuccessful() else 1, 'tests': result.testsRun,
        'failures': len(result.failures), 'errors': len(result.errors),
        'elapsed_seconds': time.monotonic()-started,
        'operations': sum(v.operations for v in METERS)}],
        'counts': {name: sum(v.counts()[name] for v in METERS) for name in (
            'factor_divisions', 'divisor_rows', 'log_evaluations', 'power_evaluations',
            'cache_hits', 'requests')},
        'peak_bytes_estimate': max((v.peak_bytes_estimate for v in METERS), default=0),
        'scope': 'synthetic kernel fixtures, vonMangoldt calibrations, grammar enumeration, injected search/selection responses; no scientific candidate table',
        'actual_search_applied': False, 'old_suites_or_studies_replayed': False,
        'proof_provider_imported': False, 'uniform_sign_claimed': False}
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
