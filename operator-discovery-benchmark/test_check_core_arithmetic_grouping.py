"""Synthetic full-domain checks; no actual-source or grouping study runs."""
import copy
from fractions import Fraction as Q
import unittest
from flint import arb, ctx
import check_core_arithmetic_grouping as C

TOTAL = 0


class Meter:
    def __init__(self, cap=1000000, cells=48000000):
        self.operations = 0; self.peak = 0; self.cap = cap; self.cells = cells
    def charge(self, n=1):
        global TOTAL
        if type(n) is not int or n < 0: raise ValueError('strict metered work')
        self.operations += n; TOTAL += n
        if self.operations > self.cap: raise RuntimeError('work cap')
    def live(self, cells):
        if type(cells) is not int or cells < 0: raise ValueError('strict cells')
        self.peak = max(self.peak, cells)
        if cells > self.cells: raise RuntimeError('cell cap')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_core_arithmetic_grouping operations=' + str(TOTAL))


def ast(kind='none', cutoff='0', step=1, post='identity', value='0'):
    return dict(base=dict(op='strip_small_prime_powers', cutoff=dict(kind=kind, value=cutoff), valuation_step=step),
                post=dict(op=post, value=value))


def reference_cells(coefficients, labels, X, eta, rho, meter):
    """Expand every complete unit cell into all its ordered prefix pairs.

Uses E1 cell differences rather than the checker's max-index Ei kernel.
"""
    e = Q(eta); r = Q(rho); ea = arb(e.numerator) / e.denominator; ra = arb(r.numerator) / r.denominator
    names = sorted(set(labels[1:])); positions = {label: i for i, label in enumerate(names)}
    matrix = [[arb(0) for _ in names] for _ in names]; diagonal = arb(0)
    logs = [arb(0)] + [arb(n).log() for n in range(1, len(coefficients))]; meter.charge(64 * (len(coefficients) - 1) + 10)
    for Y, factor in ((X, -ra), (2 * X, arb(1))):
        for n in range(Y, 2 * Y):
            ell = arb(0) if n == 1 else arb(n).log().expint(1) - arb(n + 1).log().expint(1)
            meter.charge(640)
            for h in range(1, n + 1):
                for k in range(1, n + 1):
                    term = factor * coefficients[h] * coefficients[k] * ((1 - ea) / (n * (n + 1)) + ea * (logs[h] + logs[k]) * ell / 2)
                    i = positions[labels[h]]; j = positions[labels[k]]; matrix[i][j] += term; meter.charge(14)
                    if h == k: diagonal += term; meter.charge()
    return matrix, diagonal


class ArithmeticGroupingTests(unittest.TestCase):
    def setUp(self): ctx.prec = 192; self.meter = Meter()
    def ball(self, left, right): self.assertTrue(left.overlaps(right), (str(left), str(right)))

    def test_complete_signed_groups_fractional_irregular_cells(self):
        X = 3; coefficients = [arb(0)] + [arb((-1) ** n * (n % 3 + 1)) for n in range(1, 4 * X)]
        labels = [0] + [n % 3 - 1 for n in range(1, 4 * X)]
        row = C.grouped_literal(coefficients, labels, X, '3/2', '2/3', self.meter)
        expected, diagonal = reference_cells(coefficients, labels, X, '3/2', '2/3', self.meter)
        self.assertEqual(row['group_labels'], [-1, 0, 1])
        for actual_row, reference_row in zip(row['group_matrix'], expected):
            for actual, reference in zip(actual_row, reference_row): self.ball(actual, reference)
        self.ball(row['diagonal_coefficient_sum'], diagonal)
        total = sum((v for rr in row['group_matrix'] for v in rr), arb(0)); self.meter.charge(9)
        self.ball(total, row['signed_total']); self.ball(total, row['scalar_total'])
        self.assertTrue(row['identity_residual'].contains(0)); self.assertTrue(row['identity_verified'])
        self.assertFalse(row['dyadic_domain']); self.assertFalse(row['whole_signed_bound_proved'])

    def test_positive_and_signed_negative_groups_and_diagonal(self):
        coefficients = list(map(arb, [0, 1, 1, 0, 0, 1, 0, 0])); labels = list(range(8))
        row = C.grouped_literal(coefficients, labels, 2, meter=self.meter)
        self.assertTrue(row['positive_sum'] > 0); self.assertTrue(row['negative_sum'] < 0)
        self.ball(row['signed_total'], row['positive_sum'] + row['negative_sum'])
        self.ball(row['sum_abs'], row['positive_sum'] - row['negative_sum']); self.meter.charge(4)
        for i, rr in enumerate(row['group_matrix']):
            for j, value in enumerate(rr): self.ball(value, row['group_matrix'][j][i])
        group_diagonal = sum((row['group_matrix'][i][i] for i in range(7)), arb(0)); self.meter.charge(7)
        self.ball(group_diagonal, row['diagonal_coefficient_sum'])

    def test_adversarial_single_bucket_is_exact_target_alias(self):
        coefficients = list(map(arb, [0, 1, 0, 0, 0, 1, 0, 0])); labels = [0] + [99] * 7
        row = C.grouped_literal(coefficients, labels, 2, meter=self.meter)
        self.assertEqual(row['group_labels'], [99]); self.assertEqual(len(row['group_matrix']), 1)
        self.ball(row['group_matrix'][0][0], row['scalar_total'])
        self.ball(row['sum_abs'], abs(row['scalar_total'])); self.meter.charge()
        self.assertFalse((row['group_matrix'][0][0] - row['diagonal_coefficient_sum']).contains(0)); self.meter.charge()
        self.assertFalse(row['all_scale_group_bound_proved']); self.assertFalse(row['RH_proved'])

    def test_label_bijection_and_index_permutation_are_distinct(self):
        coefficients = [arb(0)] + [arb(n - 4) for n in range(1, 8)]
        labels = [0] + [n % 2 for n in range(1, 8)]
        row = C.grouped_literal(coefficients, labels, 2, '-1/2', '1/2', self.meter)
        renamed = [0] + [7 if label == 0 else -3 for label in labels[1:]]
        other = C.grouped_literal(coefficients, renamed, 2, '-1/2', '1/2', self.meter)
        self.ball(row['sum_abs'], other['sum_abs']); self.ball(row['signed_total'], other['signed_total'])
        self.ball(row['group_matrix'][0][1], other['group_matrix'][1][0])
        swapped = list(coefficients); swapped[1], swapped[7] = swapped[7], swapped[1]
        moved = C.grouped_literal(swapped, labels, 2, '-1/2', '1/2', self.meter)
        self.assertFalse(row['scalar_total'].overlaps(moved['scalar_total']))

    def test_full_unit_head_and_incomplete_schema_rejection(self):
        coefficients = list(map(arb, [0, 2, -1, 3])); labels = [0, 10, 20, 10]
        row = C.grouped_literal(coefficients, labels, 1, '0', '1/2', self.meter)
        expected, diagonal = reference_cells(coefficients, labels, 1, '0', '1/2', self.meter)
        for rr, ee in zip(row['group_matrix'], expected):
            for a, b in zip(rr, ee): self.ball(a, b)
        self.ball(row['diagonal_coefficient_sum'], diagonal)
        self.assertFalse(row['dyadic_domain'])
        bad_coeff = list(coefficients); bad_coeff[0] = arb(1)
        bad_label = list(labels); bad_label[1] = True
        cases = [(coefficients[:-1], labels, 1, '1', '1/2'), (coefficients, labels[:-1], 1, '1', '1/2'),
                 (bad_coeff, labels, 1, '1', '1/2'), (coefficients, bad_label, 1, '1', '1/2'),
                 (coefficients, labels, True, '1', '1/2'), (coefficients, labels, 1, '2/2', '1/2'),
                 (coefficients, labels, 1, '3', '1/2'), (coefficients, labels, 1, '1', '-1/2')]
        for args in cases:
            with self.subTest(args=args), self.assertRaises(ValueError): C.grouped_literal(*args, meter=self.meter)
        infinite = list(coefficients); infinite[2] = arb('nan')
        with self.assertRaises(ArithmeticError): C.grouped_literal(infinite, labels, 1, meter=self.meter)

    def test_hand_arithmetic_labels_and_complete_removals(self):
        self.assertEqual(C.evaluate_labels(ast('fixed', '2'), 2, self.meter), [0, 1, 1, 3, 1, 5, 3, 7])
        self.assertEqual(C.evaluate_labels(ast('fixed', '2', 2), 2, self.meter), [0, 1, 2, 3, 1, 5, 6, 7])
        self.assertEqual(C.evaluate_labels(ast(post='remove_largest_once'), 2, self.meter), [0, 1, 1, 1, 2, 1, 2, 1])
        self.assertEqual(C.evaluate_labels(ast(post='remove_smallest_once'), 2, self.meter), [0, 1, 1, 1, 2, 1, 3, 1])
        removed = C.evaluate_labels(ast(post='remove_largest_all'), 4, self.meter)
        self.assertEqual([removed[i] for i in (1, 4, 6, 8, 12, 15)], [1, 1, 2, 1, 4, 3])
        self.assertEqual(C.evaluate_labels(ast(post='root', value='2'), 2, self.meter), [0, 1, 1, 1, 2, 2, 2, 2])
        quotient = C.evaluate_labels(ast(post='quotient', value='1/2'), 4, self.meter)
        self.assertEqual(quotient, [0] + [n // 2 for n in range(1, 16)])
        residue = C.evaluate_labels(ast(post='residue', value='3'), 2, self.meter)
        self.assertEqual(residue, [0, 1, 2, 0, 1, 2, 0, 1])

    def test_exact_power_cutoffs_and_log_boundaries(self):
        below = C.evaluate_labels(ast('power', '1/3'), 7, self.meter)
        exact = C.evaluate_labels(ast('power', '1/3'), 8, self.meter)
        self.assertEqual([below[2], below[8], exact[2], exact[8]], [2, 8, 1, 1])
        seven = C.evaluate_labels(ast('log2', '1'), 7, self.meter)
        eight = C.evaluate_labels(ast('log2', '1'), 8, self.meter)
        self.assertEqual([seven[3], seven[12], eight[3], eight[12]], [3, 3, 1, 1])
        square = C.evaluate_labels(ast('power', '2/3'), 8, self.meter)
        self.assertEqual([square[3], square[5], square[12]], [1, 5, 1])
        self.assertEqual(C._integer_root(64, 6, self.meter), 2)
        self.assertEqual(C._integer_root(63, 6, self.meter), 1)
        self.assertEqual(C._integer_root(1, 3, self.meter), 1)

    def test_unknown_asts_and_shared_resource_caps(self):
        invalid = [ast('none', '1'), ast('power', '1/4'), ast('fixed', '5'), ast('log2', '0'),
                   ast(step=True), ast(post='root', value='4'), ast(post='identity', value='1'),
                   ast(post='quotient', value='2/3'), ast(post='residue', value='5')]
        extra = ast(); extra['id'] = 1; invalid.append(extra)
        wrong = ast(); del wrong['post']['value']; invalid.append(wrong)
        for p in invalid:
            with self.subTest(p=p), self.assertRaises(ValueError): C.evaluate_labels(p, 2, self.meter)
        coefficients = [arb(0)] + [arb(1)] * 7; labels = list(range(8))
        low = Meter(cap=10)
        with self.assertRaises(RuntimeError): C.grouped_literal(coefficients, labels, 2, meter=low)
        self.assertGreater(low.operations, low.cap)
        small = Meter(cells=1)
        with self.assertRaises(RuntimeError): C.grouped_literal(coefficients, labels, 2, meter=small)
        self.assertGreater(small.peak, small.cells)
        direct = C.Meter(cap=0)
        with self.assertRaises(RuntimeError): direct.charge()
        self.meter.charge(direct.operations)
        with self.assertRaises(ValueError): direct.charge(True)


if __name__ == '__main__': unittest.main()
