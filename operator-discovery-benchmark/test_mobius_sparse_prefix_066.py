"""Synthetic tests of complete-convolution contraction, no saved arrays."""
from fractions import Fraction as Q
from math import gcd
import unittest

import mobius_sparse_prefix_066 as S
import mobius_prefix_completion_062 as B
import mobius_prefix_repair_063 as R

METER = S.Meter()
PARAMS = {'primes': [2, 3, 5], 'p': 3, 'q': 5, 'alpha': '1/5', 'gamma': '5/28', 'tau': '1/2'}


class SparsePrefixTests(unittest.TestCase):
    def test_source_rewrite_all_small_prefixes_and_endpoints(self):
        for N in (2, 7, 19):
            D = 4*N//3
            for y in range(1, D+1):
                for ratio in (Q(3, 5), Q(1)):
                    floors, steps, unused = S.decompose(N, y, 3, 5, ratio, METER)
                    for d in range(1, D+2):
                        value = sum((c*(Z//d) for Z, c in floors.items()), Q(0))
                        value += sum((c for T, c in steps.items() if d <= T), Q(0))
                        expected = B.weight(N, 3, d)-ratio*B.weight(N, 5, d) if d <= y else Q(0)
                        self.assertEqual(value, expected)

    def test_full_untruncated_source_contracts_to_six_floors(self):
        cert = S.construct(101, 134, 10, PARAMS, METER)
        for e in cert['endpoints']:
            self.assertEqual(e['steps'], [])
            self.assertEqual(e['coefficient_l1'], '0')
            self.assertTrue(all(t['joined_interval_upper'] == '0' for t in e['tail_bounds']))

    def test_short_raw_coefficients_match_fresh_old_construction(self):
        for N, y, H in ((7, 3, 4), (37, 25, 6), (101, 90, 9)):
            inv = B.inverse_completion(N, y, H, PARAMS, METER)
            base = B.exact_certificate(N, y, H, PARAMS, inv['endpoints'], METER)
            old = R.construct(base, 'raw', meter=METER)['repair']
            new = S.construct(N, y, H, PARAMS, METER)
            self.assertEqual([[r['coefficient'] for r in e['rows']] for e in new['endpoints']], old['coefficients'])

    def test_joined_interval_cancellation_and_unit(self):
        self.assertEqual(S.window_kernel({8: Q(1), 7: Q(-1)}, 1, METER),
                         [{'lo': 4, 'hi': 4, 'coefficient': '-1'}, {'lo': 8, 'hi': 8, 'coefficient': '1'}])
        self.assertEqual(S.window_kernel({1: Q(-2)}, 1, METER),
                         [{'lo': 1, 'hi': 1, 'coefficient': '-2'}])

    def test_direct_small_horizons_and_terminal_inverse_row(self):
        cert = S.construct(7, 9, 9, PARAMS, METER)
        mu = B.ordinary_mu(9, METER)
        for e in cert['endpoints']:
            ratio = Q(e['ratio'])
            coeff = list(map(lambda r: Q(r['coefficient']), e['rows']))
            for d in range(1, 11):
                got = sum((c*((j+1)//d) for j, c in enumerate(coeff)), Q(0))
                expected = B.weight(7, 3, d)-ratio*B.weight(7, 5, d) if d <= 9 else 0
                self.assertEqual(got, expected)
            self.assertEqual(len(e['tail_bounds']), 9)

    def test_uniform_tail_telescoping_dominates_every_actual_tail(self):
        cert = S.construct(257, 100, 29, PARAMS, METER)
        for e in cert['endpoints']:
            self.assertEqual([t['J'] for t in e['tail_bounds']], list(range(1, 30)))
            for t in e['tail_bounds']:
                self.assertLessEqual(Q(t['actual_variation']), Q(t['joined_interval_upper']))
                self.assertLessEqual(Q(t['joined_interval_upper']), Q(t['coarse_upper']))
                self.assertLessEqual(Q(t['coarse_upper']), Q(e['floor_l1'])+Q(e['step_first_moment'])/t['J'])

    def test_arbitrary_rational_tail_locations_and_rejections(self):
        result = S.selected_cutoffs(97, ['1/257', '5/11', '7/8', '1'])
        self.assertEqual([r['J'] for r in result], [1, 45, 85, 97])
        for fractions in (['2/4'], ['0'], ['3/2'], [True]):
            with self.assertRaises(ValueError): S.selected_cutoffs(97, fractions)

    def test_moments_include_every_row_without_claiming_a_rate(self):
        cert = S.construct(37, 31, 7, PARAMS, METER)
        for source, result in zip(cert['endpoints'], S.block_moments(cert)):
            self.assertEqual(sum(b['row_count'] for b in result['blocks']), 7)
            self.assertEqual(sum((Q(b['actual_variation']) for b in result['blocks']), Q(0)), Q(source['coefficient_l1']))

    def test_independent_admission_and_same_raw_source_binding(self):
        from copy import deepcopy
        import check_mobius_prefix_repair_063 as RC
        import check_mobius_prefix_completion_062 as BC
        import check_mobius_sparse_prefix_066 as C
        import run_mobius_sparse_prefix_066 as RUN
        N, y, H = 37, 25, 6
        inv = B.inverse_completion(N, y, H, PARAMS, METER)
        base = B.exact_certificate(N, y, H, PARAMS, inv['endpoints'], METER)
        raw = R.construct(base, 'raw', meter=METER)
        cm = C.Meter(cap=100_000_000)
        raw['repair_verification'] = RC.verify_repair(raw['repair'], cm)
        raw['whole_verification'] = BC.verify_completion(raw['completion'], cm)
        saved = {'N': N, 'y': y, 'H': H, 'candidates': [raw], 'selected_rule': 'core_inverse'}
        chosen, long = RUN.bind_raw(saved)
        self.assertEqual(chosen['rule'], 'raw')
        cert = S.construct(N, y, H, PARAMS, METER)
        self.assertTrue(C.verify_sparse(cert, cm)['verified'])
        self.assertEqual([e['coefficient_l1'] for e in cert['endpoints']], raw['repair']['coefficient_l1'])
        for change in ('scale', 'fill', 'coefficient', 'budget'):
            bad = deepcopy(saved)
            if change == 'scale': bad['N'] += 1
            if change == 'fill': bad['candidates'][0]['repair']['rule'] = 'core_inverse'
            if change == 'coefficient': bad['candidates'][0]['completion']['coefficients'][0][0] = '99'
            if change == 'budget': bad['candidates'][0]['whole_verification']['budget'] = '99'
            with self.assertRaises(ValueError): RUN.bind_raw(bad)
        METER.charge(cm.operations)


if __name__ == '__main__':
    unittest.main()
