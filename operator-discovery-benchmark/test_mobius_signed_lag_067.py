"""New synthetic controls of signed correlations and paid lag transfers."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest

import mobius_signed_lag_067 as S
import mobius_sparse_prefix_066 as SOURCE

METER = S.Meter(cap=300_000_000_000)
PARAMS = {'primes': [2, 3, 5], 'p': 3, 'q': 5, 'alpha': '1/5', 'gamma': '5/28', 'tau': '1/2'}


class SignedLagTests(unittest.TestCase):
    def source(self, N=37, y=25, H=6):
        return SOURCE.construct(N, y, H, PARAMS, METER)

    def test_integer_polynomial_matches_direct_signed_correlations(self):
        for values in ([0], [0, 0], [1, -2, 3], [0, 1, 0, -1, 4, -3], [3, 0, 0, 0]):
            expected = [sum(a*b for a, b in zip(values, values[h:])) for h in range(len(values))]
            self.assertEqual(S.exact_correlations(values, METER), expected)

    def test_all_small_source_prefixes_have_complete_moment_identity(self):
        for N in (2, 7, 19):
            D = 4*N//3
            for y in range(1, D+1):
                H = min(D, 9)
                cert = S.construct(self.source(N, y, H), ['0', '1/7', '2/3'], METER)
                for endpoint in cert['endpoints']:
                    for block in endpoint['blocks']:
                        a = block['correlation_numerators']
                        den = endpoint['denominator']
                        self.assertEqual(Q(a[0]+2*sum(a[1:]), den*den), Q(block['moment']))
                        self.assertEqual(sum(v*v for v in block['row_sums_scaled']), a[0]+2*sum(a[1:]))
                        self.assertLessEqual(Q(block['diagonal']), Q(block['uniform_diagonal_upper']))
                        for part in block['candidates']:
                            self.assertLessEqual(Q(block['moment']), Q(part['finite_moment_upper']))
                            self.assertLessEqual(Q(block['actual_head_variation']), Q(part['finite_head_upper']))

    def test_empty_head_and_full_floor_closure(self):
        empty = S.construct(self.source(2, 1, 1), ['1/257'], METER)
        self.assertEqual(empty['head_stop'], 0)
        self.assertTrue(all(e['blocks'] == [] for e in empty['endpoints']))
        full = S.construct(self.source(37, 49, 9), ['0', '1'], METER)
        for endpoint in full['endpoints']:
            self.assertEqual(endpoint['step_first_moment'], '0')
            for block in endpoint['blocks']:
                self.assertEqual(block['moment'], '0')
                self.assertTrue(all(v == 0 for v in block['correlation_numerators']))

    def test_direct_coefficients_are_retained_separately(self):
        cert = S.construct(self.source(7, 9, 9), ['0'], METER)
        self.assertTrue(any(Q(v) for e in cert['endpoints'] for b in e['blocks'] for v in b['direct_coefficients']))
        for endpoint in cert['endpoints']:
            for block in endpoint['blocks']:
                direct = sum((abs(Q(v)) for v in block['direct_coefficients']), Q(0))
                self.assertEqual(Q(block['actual_head_variation']), direct)

    def test_fractional_cutoff_exact_without_root_whitelist(self):
        for N in (2, 7, 64, 257):
            for delta in ('0', '1', '1/257', '3/11', '5/13', '7/8'):
                value = S.power_cutoff(N, delta, METER)
                p = Q(delta)
                self.assertLessEqual(value**p.denominator, N**p.numerator)
                self.assertGreater((value+1)**p.denominator, N**p.numerator)
        for bad in ('2/4', '-1/2', '3/2', True):
            with self.assertRaises(ValueError): S.power_cutoff(37, bad, METER)
        with self.assertRaises(OverflowError): S.power_cutoff(37, '1/1000000', METER)

    def test_near_far_partition_and_full_cutoff_cover_every_lag(self):
        cert = S.construct(self.source(), ['0', '1/7', '1'], METER)
        for endpoint in cert['endpoints']:
            for block in endpoint['blocks']:
                corr = block['correlation_numerators']
                for part in block['candidates']:
                    self.assertEqual(Q(part['near_signed'])+Q(part['far_signed']), Q(block['signed_cross']))
                    self.assertLessEqual(part['used_cutoff'], len(corr)-1)
                    self.assertFalse(part['uniform_far_bound_proved'])
                self.assertEqual(block['candidates'][-1]['far_signed'], '0')
                self.assertEqual(block['candidates'][0]['near_signed'], '0')

    def test_rational_sqrt_rounds_up_and_within_one_unit(self):
        for value in ('0', '1', '2', '1/3', '999/17'):
            q = Q(value)
            root = S.sqrt_upper(q)
            self.assertGreaterEqual(root*root, q)
            if root:
                self.assertLess((root-Q(1, S.ROUNDING_DENOMINATOR))**2, q)
        with self.assertRaises(ValueError): S.sqrt_upper(-1)

    def test_summary_preserves_every_fraction_and_all_scope_flags(self):
        exponents = ['1/257', '3/11', '1']
        cert = S.construct(self.source(), exponents, METER)
        for endpoint in S.summarize(cert):
            self.assertEqual([p['exponent'] for p in endpoint['candidates']], [None]+exponents)
            self.assertFalse(any(p['uniform_far_bound_proved'] for p in endpoint['candidates']))
            self.assertLessEqual(Q(endpoint['actual_head_variation']), Q(endpoint['moment_cauchy_upper']))
        self.assertFalse(cert['RH_proved'])
        self.assertFalse(cert['uniform_full_head_bound_proved'])

    def test_missing_source_endpoint_and_mixed_raw_row_are_rejected(self):
        source = self.source()
        source['endpoints'][0]['rows'][0]['coefficient'] = '123'
        with self.assertRaises(ValueError): S.construct(source, ['0'], METER)
        source = self.source()
        source['endpoints'].pop()
        with self.assertRaises(ValueError): S.construct(source, ['0'], METER)
        for values in ([], ['1/3', '1/3'], [True]):
            with self.assertRaises(ValueError): S.programs(37, values, METER)

    def test_independent_new_pipeline_and_strict_same_source_binding(self):
        import check_mobius_sparse_prefix_066 as OLD_CHECK
        import check_mobius_signed_lag_067 as CHECK
        import run_mobius_signed_lag_067 as RUN
        source = self.source(41, 37, 11)
        old_meter = OLD_CHECK.Meter(cap=300_000_000_000)
        old_verdict = OLD_CHECK.verify_sparse(source, old_meter)
        METER.charge(old_meter.operations)
        saved = {**{k: source[k] for k in ('N', 'y', 'H', 'parameters')},
            'certificate': source, 'verification': old_verdict,
            'raw_coefficients_match_at_every_row': True, 'comparison_is_raw_only': True,
            'same_saved_raw_source_admission_reused': True,
            'uniform_full_variation_bound_proved': False, 'RH_proved': False}
        cert = S.construct(RUN.bind_sparse(saved), ['0', '1/257', '3/11', '1'], METER)
        check_meter = CHECK.Meter()
        verdict = CHECK.verify_lag(cert, check_meter)
        METER.charge(check_meter.operations)
        self.assertTrue(verdict['verified'])
        self.assertTrue(verdict['new_actual_mu_lag_correlations_evaluated'])
        self.assertTrue(verdict['unmasked_original_source_inverse_evaluated'])
        self.assertFalse(verdict['masked_scientific_prefix_or_LP_evaluated'])
        self.assertFalse(verdict['uniform_full_head_bound_proved'])
        for endpoint in S.summarize(cert):
            self.assertTrue(endpoint['finite_evidence_pareto_exponents'])
        for field in ('N', 'y', 'H'):
            bad = deepcopy(saved)
            bad['verification'][field] += 1
            with self.assertRaises(ValueError): RUN.bind_sparse(bad)
        bad = deepcopy(saved)
        bad['comparison_is_raw_only'] = False
        with self.assertRaises(ValueError): RUN.bind_sparse(bad)
        bad = deepcopy(cert)
        bad['endpoints'][0]['blocks'][0]['correlation_numerators'][1] += 1
        with self.assertRaises(ValueError): CHECK.verify_lag(bad, METER)


if __name__ == '__main__':
    unittest.main()
