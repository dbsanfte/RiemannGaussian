"""Focused synthetic checks for the new actual-moment diagnostic only."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest

import mobius_walsh_moment_probe_065 as P

METER = P.Meter()


def example():
    rows = [{1: 1, 2: 1}, {2: 1, 3: -1}, {}]
    parent = {'ratio': '1', 'l1': '4', 'rows': [
        {'j': j, 'terms': [{'index': n, 'coefficient': str(c)} for n, c in row.items()]}
        for j, row in enumerate(rows, 1)]}
    certificate = {'ratio': '1', 'weights': ['2', '2', '0'], 'weight_mass': '4',
                   'energy_upper': '4', 'energy_terms': [
                       {'index': n, 'coefficient': str(c)} for n, c in [(1, 2), (2, 1), (6, -1)]]}
    return parent, certificate


class MomentProbeTests(unittest.TestCase):
    def test_two_way_energy_preserves_actual_cancellation(self):
        parent, cert = example()
        result = P.analyze_endpoint(parent, cert, 3, 3, set(), METER)
        self.assertEqual(result['global']['actual_energy'], '0')
        self.assertEqual(result['global']['all_free_plus_energy'], '2')
        self.assertEqual(result['global']['all_free_plus_variation'], '2')
        self.assertEqual(result['actual_partition_cauchy_upper'], '0')

    def test_signed_nonzero_energy_and_shared_prime_product(self):
        parent = {'ratio': '1', 'l1': '6', 'rows': [{'j': 1, 'terms': [
            {'index': n, 'coefficient': str(c)} for n, c in [(1, 1), (2, 1), (3, 1), (6, -3)]]}]}
        cert = {'ratio': '1', 'weights': ['6'], 'weight_mass': '6', 'energy_upper': '8/3',
                'energy_terms': [{'index': n, 'coefficient': c} for n, c in [(1, '2'), (2, '-2/3'), (3, '-2/3'), (6, '-2/3')]]}
        result = P.analyze_endpoint(parent, cert, 1, 3, set(), METER)
        self.assertEqual(result['global']['actual_energy'], '8/3')
        self.assertEqual(result['global']['actual_cauchy_upper'], '4')
        self.assertEqual(result['global']['all_free_plus_energy'], '0')

    def test_energy_tamper_and_endpoint_swap_rejected(self):
        p, c = example()
        for change in ('coefficient', 'ratio', 'mass', 'row'):
            parent, cert = deepcopy(p), deepcopy(c)
            if change == 'coefficient': cert['energy_terms'][0]['coefficient'] = '3'
            if change == 'ratio': cert['ratio'] = '3/5'
            if change == 'mass': cert['weight_mass'] = '3'
            if change == 'row': parent['rows'][1]['j'] = 3
            with self.assertRaises(ValueError): P.analyze_endpoint(parent, cert, 3, 3, set(), METER)

    def test_weight_scope_and_zero_rows(self):
        parent, original = example()
        for weights in (['2', '2', '1'], ['-1', '2', '0'], ['3', '2', '0']):
            cert = deepcopy(original); cert['weights'] = weights
            with self.assertRaises(ValueError): P.analyze_endpoint(parent, cert, 3, 3, set(), METER)
        zero = P.moment([{'A': Q(0), 'w': Q(0), 'minus': Q(0), 'plus': Q(0)}])
        self.assertEqual(zero['actual_cauchy_upper'], '0')

    def test_character_scope_rejects_squareful_and_conditioned_factors(self):
        for n, radius, known in [(4, 3, set()), (9, 3, set()), (6, 3, {2}), (77, 7, set())]:
            with self.assertRaises(ValueError): P.character_sign(n, radius, known, {}, METER)
        self.assertEqual(P.character_sign(210, 7, set(), {}, METER), 1)
        self.assertEqual(P.character_sign(30, 5, set(), {}, METER), -1)
        self.assertEqual(P.character_sign(1, 1, set(), {}, METER), 1)

    def test_dyadic_partition_includes_unit_and_terminal_row(self):
        for H in (1, 2, 3, 8, 9, 31):
            covered = [j for a, b in P.intervals(H) for j in range(a, b+1)]
            self.assertEqual(covered, list(range(1, H+1)))
        self.assertEqual(list(P.intervals(9))[-1], (8, 9))

    def test_tail_example_does_not_require_subpower_energy(self):
        for H in (8, 16, 32):
            rows = [{'A': Q(j > H//2), 'w': Q(j > H//2),
                     'minus': Q(j > H//2), 'plus': Q(j > H//2)} for j in range(1, H+1)]
            result = P.moment(rows)
            self.assertEqual(Q(result['actual_energy']), H//2)
            self.assertEqual(Q(result['actual_cauchy_product']), (H//2)**2)
            self.assertEqual(Q(result['actual_cauchy_upper']), H//2)

    def test_root_interval_is_exact_upward_rounding(self):
        for x in (Q(0), Q(1, 7), Q(2), Q(4), Q(123456, 257)):
            upper = P.root_upper(x)
            self.assertGreaterEqual(upper**2, x)
            if upper: self.assertLess((upper-Q(1, 4096))**2, x)


if __name__ == '__main__':
    unittest.main()
