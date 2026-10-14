"""New synthetic tests of automated finite bound synthesis and its limits."""
from copy import deepcopy
from fractions import Fraction as Q
from types import SimpleNamespace
from unittest.mock import patch
import unittest
import numpy as np

import mobius_floor_control_068 as S

METER = S.Meter(cap=300_000_000_000)
PARAMS = {'primes': [2, 3, 5], 'p': 3, 'q': 5, 'alpha': '1/5', 'gamma': '5/28', 'tau': '1/2'}


class FloorControlTests(unittest.TestCase):
    def test_fractional_depths_without_root_whitelist(self):
        for N in (2, 11, 64, 257):
            for text in ('0', '1', '1/257', '3/11', '5/13', '7/8'):
                a = Q(text); K = S.power(N, text, METER)
                self.assertLessEqual(K**a.denominator, N**a.numerator)
                self.assertGreater((K+1)**a.denominator, N**a.numerator)
        for text in ('2/4', '-1/3', '4/3', True):
            with self.assertRaises(ValueError): S.power(37, text, METER)
        with self.assertRaises(OverflowError): S.power(37, '1/1000000', METER)

    def test_quotient_blocks_and_rank_spread_match_scalar_enumeration(self):
        for anchors in ([], [1], [37, 26, 5, 1], [360, 288, 180, 144]):
            required = {A//k for A in anchors for k in range(1, A//2+1)}
            for K in (0, 1, 3, 19, 360):
                available = sorted({A//k for A in anchors for k in range(1, min(K, A//2)+1)})
                for B in (1, 2, 4, 512):
                    expect = available if len(available) <= B else ([available[-1]] if B == 1 else
                        [available[i*(len(available)-1)//(B-1)] for i in range(B)])
                    actual, truncated, complete = S.dictionary(anchors, K, B, METER)
                    self.assertEqual((actual, truncated, complete), (expect, len(available)>B, required<=set(expect)))
        shallow = S.dictionary([360, 288, 180, 144], 2, 4, METER)[0]
        deep = S.dictionary([360, 288, 180, 144], 30, 4, METER)[0]
        self.assertNotEqual(shallow, deep)
        self.assertEqual(shallow[-1], deep[-1])

    def test_unsigned_squarefree_mask_and_unit_extraction(self):
        sf = S.squarefree_mask(80, METER)
        for n in range(1, 81):
            self.assertEqual(bool(sf[n]), not any(n%(a*a) == 0 for a in range(2, n+1)))
        k = [0, 3, 0, 0, 999, 0]
        model = S.solve_row(k, -3, 1, sf, [], METER)
        self.assertEqual(model['bound'], '0')
        self.assertEqual(model['box_optimum_lower'], '0')

    def test_actual_joined_source_barrier_family(self):
        N, y = 45, 48
        for ratio in (Q(3, 5), Q(1)):
            g, floors, steps = S.source(N, y, 3, 5, ratio, METER)
            den = ratio.denominator
            k = [g[n]-(g[2*n] if 2*n <= 60 else 0) for n in range(1, 61)]
            expected = [den*(int(24<n<=30)-int(48<n<=60)) for n in range(1, 61)]
            self.assertEqual(k, expected)
            self.assertEqual(S.row_endpoints(steps, 1), [60, 48, 30, 24])
            self.assertEqual(floors.get(1, 0), 0)

    def test_lp_recovers_anonymous_complete_floor_calibration(self):
        D = 37
        k = [0]+[2*(D//n) for n in range(1, D+1)]
        sf = S.squarefree_mask(D, METER)
        model = S.solve_row(k, 0, 2, sf, [D], METER)
        self.assertEqual(model['solver']['status'], 'optimal_float_proposal')
        self.assertGreaterEqual(Q(model['bound']), 1)
        self.assertLessEqual(Q(model['bound']), Q(10001, 10000))
        self.assertLessEqual(Q(model['box_gap']), Q(1, 1000))

    def test_integer_replay_and_box_penalty_match_scalar_formula(self):
        k, direct, den, hs = [0, 1, -2, 3, 0, 1, -1, 2], 2, 3, [3, 7]
        sf = S.squarefree_mask(7, METER); ns = [n for n in range(2, 8) if sf[n]]
        x, eps, z = [S.GRID//3, -S.GRID//5], S.GRID//2, [S.GRID//(i+2) for i in range(len(ns))]
        C = 4*den*len(hs)
        matrix = np.array([[X//n for X in hs] for n in ns], dtype=np.int64)
        proof = S.exact_replay(k, direct, den, ns, hs, C, x, eps, z, matrix, METER)
        center = S.GRID*(direct+k[1])+sum(a*(1-X) for a, X in zip(x, hs))
        resid = sum(abs(S.GRID*k[n]-sum(a*(X//n) for a, X in zip(x, hs))) for n in ns)
        defect = sum(abs(eps*(1-X)-sum(a*(X//n) for n, a in zip(ns, z))) for X in hs)
        lower = eps*(direct+k[1])+sum(a*k[n] for n, a in zip(ns, z))-C*defect
        self.assertEqual(Q(proof['bound']), Q(abs(center)+resid, S.GRID*den))
        self.assertEqual(Q(proof['box_optimum_lower']), Q(lower, S.GRID*den))
        self.assertGreater(defect, 0)

    def test_failed_solver_is_recorded_with_valid_zero_fallback(self):
        result = SimpleNamespace(success=False, nit=None, message='synthetic timeout')
        with patch.object(S, 'linprog', return_value=result):
            model = S.solve_row([0, 1, -3, 2], 1, 1, S.squarefree_mask(3, METER), [3], METER)
        self.assertEqual(model['solver']['status'], 'failed_zero_fallback')
        self.assertEqual(model['bound'], '7')
        self.assertEqual(model['box_optimum_lower'], '0')
        self.assertEqual(model['primal_numerators'], [0])

    def test_complete_span_is_flagged_even_when_price_is_exact(self):
        cert = S.construct(13, 9, 4, PARAMS, ['1'], meter=METER)
        for endpoint in cert['endpoints']:
            for row in endpoint['rows']:
                self.assertTrue(row['plans'][-1]['complete_endpoint_quotients'])
        self.assertFalse(cert['uniform_head_bound_proved'])
        self.assertFalse(cert['RH_proved'])
        self.assertFalse(cert['learner_mobius_signs_accessed'])

    def test_duplicate_dictionaries_reuse_solver_and_keep_all_plans(self):
        with patch.object(S, 'solve_row', wraps=S.solve_row) as solve:
            cert = S.construct(7, 5, 2, PARAMS, ['0', '1/257', '1/17'], meter=METER)
        self.assertEqual(solve.call_count, sum(len(row['models']) for e in cert['endpoints'] for row in e['rows']))
        for endpoint in cert['endpoints']:
            for row in endpoint['rows']:
                self.assertEqual(len(row['plans']), 4)
                self.assertEqual(len({plan['model_index'] for plan in row['plans'][1:]}), 1)

    def test_input_scope_rejects_signed_targets_and_bad_parameters(self):
        for key, value in [('mu', [1, -1]), ('target', '123'), ('p', 0), ('primes', [2, 3, 9]), ('alpha', '2/10')]:
            parameters = deepcopy(PARAMS); parameters[key] = value
            with self.assertRaises(ValueError): S.construct(37, 25, 3, parameters, ['0'], meter=METER)
        for exponents in ([], ['1/3', '1/3'], [True]):
            with self.assertRaises(ValueError): S.construct(37, 25, 3, PARAMS, exponents, meter=METER)
        for value in (float('inf'), float('nan')):
            with self.assertRaises(ValueError): S.quantize(value, 1)
        with self.assertRaises(OverflowError): S.construct(37, 25, 3, PARAMS, ['0'], meter=S.Meter(cap=0))

    def test_independent_pipeline_source_binding_and_far_transfer(self):
        import run_mobius_floor_control_068 as R
        source = R.PRIOR.PRIOR.SEARCH.construct(41, 37, 11, PARAMS, METER)
        old_meter = R.PRIOR.PRIOR.CHECK.Meter(cap=300_000_000_000)
        old_verdict = R.PRIOR.PRIOR.CHECK.verify_sparse(source, old_meter)
        METER.charge(old_meter.operations)
        sparse = {**{k: source[k] for k in ('N', 'y', 'H', 'parameters')},
            'certificate': source, 'verification': old_verdict,
            'raw_coefficients_match_at_every_row': True, 'comparison_is_raw_only': True,
            'same_saved_raw_source_admission_reused': True,
            'uniform_full_variation_bound_proved': False, 'RH_proved': False}
        lag = R.PRIOR.SEARCH.construct(source, ['0', '1/7'], METER)
        lm = R.PRIOR.CHECK.Meter(cap=300_000_000_000)
        lag_verdict = R.PRIOR.CHECK.verify_lag(lag, lm); METER.charge(lm.operations)
        saved = {**{k: source[k] for k in ('N', 'y', 'H')}, 'theta': '1/2',
            'certificate': lag, 'verification': lag_verdict, 'same_raw_source_head': True,
            'all_lags_and_rows_verified': True, 'uniform_far_correlation_bound_proved': False, 'RH_proved': False}
        self.assertIs(R.bind_lag(saved, sparse), source)
        cert = S.construct(41, 37, lag['head_stop'], PARAMS, ['0', '1/257', '3/11', '1'], meter=METER)
        cm = R.CHECK.Meter(); verdict = R.CHECK.verify_control(cert, cm); METER.charge(cm.operations)
        summary = R.summarize_case(saved, source, cert, verdict)
        for endpoint in summary['endpoints']:
            self.assertLessEqual(Q(endpoint['actual_head_variation']), Q(endpoint['selected_head_upper']))
            for block in endpoint['dyadic_far_controls']:
                for far in block['far_controls']:
                    self.assertLessEqual(Q(far['observed_far']), Q(far['far_upper']))
        groups = R.group_sources([('first', saved), ('second', saved)])
        self.assertEqual(len(groups), 1); self.assertEqual(groups[0]['max_j'], lag['head_stop'])
        self.assertEqual(groups[0]['lag_files'], ['first', 'second'])
        for key in ('N', 'y', 'H'):
            bad = deepcopy(saved); bad['verification'][key] += 1
            with self.assertRaises(ValueError): R.bind_lag(bad, sparse)
        bad = deepcopy(source); bad['endpoints'][0]['rows'][0]['coefficient'] = '123'
        with self.assertRaises(ValueError): R.summarize_case(saved, bad, cert, verdict)
        bad = deepcopy(saved); bad['certificate']['endpoints'][0]['blocks'][0]['moment'] = '123'
        with self.assertRaises(ValueError): R.summarize_case(bad, source, cert, verdict)
        self.assertFalse(verdict['original_source_binding_proved'])
        self.assertTrue(verdict['checker_actual_mobius_signs_evaluated'])
        self.assertFalse(verdict['learner_mobius_signs_accessed'])


if __name__ == '__main__':
    unittest.main()
