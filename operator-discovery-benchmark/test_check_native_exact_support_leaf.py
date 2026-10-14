"""Independent regression cases for affine leaf recovery and complete rows."""
import ast
import copy
from fractions import Fraction as F
from pathlib import Path
import unittest
import check_native_exact_support_leaf as I


def compression_receipt(columns, lhs, support):
    labels, rows = I.C.augmented_rows(columns, lhs, support)
    canonical = I.C.canonical_compression(columns, lhs, support)
    index = {label: i for i, label in enumerate(labels)}
    retained = [index[label] for label in canonical['representatives']]
    mapping = [dict(row=i, representative=None if r['representative'] is None else index[r['representative']], ratio=r['ratio']) for i, r in enumerate(canonical['row_mapping'])]
    sparse = [[[j, str(q)] for j, q in enumerate(row) if q] for row in rows]
    n = len(support); R = len(rows)
    E = sum(len(columns[i]) for i in support); S = sum(sum(bool(q) for q in columns[i].values()) for i in support)
    T, U = len(lhs), sum(bool(q) for q in lhs.values())
    A = sum(sum(bool(q) for q in row) for row in rows); V = sum(any(row) for row in rows)
    B = sum(sum(bool(q) for q in rows[i]) for i in retained)
    pre = E+2*S+T+U+R+4*A+V+B
    reserve = 4*S+T+R+1; native = len(retained)*max(1, n)**2
    return dict(original_row_labels=labels, retained_rows=retained, mapping=mapping,
                original_system_hash=I.digest(sparse), original_row_order_hash=I.digest(labels),
                original_rows=R, reduced_rows=len(retained), support_size=n,
                original_work_proxy=R*max(1, n)**2, native_work_proxy=native,
                preprocessing_work=pre, preprocessing_actual_work=pre+4*S+1,
                preprocessing_cells=2*S+U+A+B, verification_work_reserve=reserve,
                total_work_proxy=pre+native+reserve)


def receipt(columns, lhs, support, answer=None):
    rebuilt = I.rebuild_leaf_system(columns, lhs, support)
    excluded = {'reduced_columns', 'reduced_target', 'selected_columns', 'original_rhs', 'original_rows', 'rhs', 'inconsistent_rhs_rows'}
    report = {key: copy.deepcopy(value) for key, value in rebuilt.items() if key not in excluded}
    report.update(original_rows=len(rebuilt['original_rows']), status='prepared_remaining_system',
                  preprocessing_actual_work=rebuilt['preprocessing_work'], preprocessing_actual_cells=rebuilt['preprocessing_cells'])
    if answer is not None:
        weights = list(map(F, answer)); reduced = [weights[j] for j in rebuilt['retained_support_positions']]
        comp = compression_receipt(rebuilt['reduced_columns'], rebuilt['reduced_target'], list(range(len(reduced))))
        n, nnz, m, rn = len(support), rebuilt['selected_nonzero_count'], len(rebuilt['original_rows']), len(reduced)
        P, L = rebuilt['pivot_entry_count'], len(rebuilt['pivots'])
        back = 4*P+L+2*rn; full = n+4*nnz+len(lhs)+m+1
        ledger = dict(rebuilt['work_ledger'], remaining_compression_python=comp['preprocessing_actual_work'], full_verification=full)
        if back: ledger['backsubstitution'] = back
        report.update(remaining_compression=comp, reduced_solution=list(map(str, reduced)), exact_support_weights=list(map(str, weights)),
                      backsubstitution_values=[dict(variable=p['variable'], value=str(weights[p['support_position']])) for p in reversed(rebuilt['pivots'])],
                      remaining_native_total_work_proxy=comp['total_work_proxy'],
                      leaf_total_work_proxy=rebuilt['leaf_work_reserve']+comp['total_work_proxy'],
                      total_work_proxy=rebuilt['leaf_work_reserve']+comp['total_work_proxy'],
                      work_ledger=ledger, status='full_original_equality_verified',
                      preprocessing_actual_work=rebuilt['preprocessing_work']+comp['preprocessing_actual_work']+back+full,
                      preprocessing_actual_cells=rebuilt['preprocessing_cells']+comp['preprocessing_cells']+rn+P+nnz)
    return report


class IndependentLeafTests(unittest.TestCase):
    def test_no_producer_native_imports(self):
        source = Path(I.__file__).read_text()
        imports = [node.module for node in ast.walk(ast.parse(source)) if isinstance(node, ast.ImportFrom)]
        imports += [name.name for node in ast.walk(ast.parse(source)) if isinstance(node, ast.Import) for name in node.names]
        self.assertFalse(any(name and name.startswith('native_exact') for name in imports))
        self.assertIn('check_joint_gram_compressed_replay', imports)

    def test_fully_eliminated_system(self):
        columns = [{0: F(2)}, {1: F(3)}]; lhs = {0: F(8), 1: F(15)}; support = [0, 1]
        report = receipt(columns, lhs, support, ['4', '5'])
        self.assertEqual(report['retained_variable_indices'], [])
        self.assertEqual(report['retained_rows'], [])
        self.assertTrue(I.verify_leaf_solution(columns, lhs, support, ['4', '5'], report)['verified'])

    def test_affine_leaves_and_free_variable_unsorted_support(self):
        columns = [{0: F(1), 1: F(1)}, {0: F(1), 1: F(1)}, {0: F(2)}]
        lhs = {0: F(7), 1: F(3)}; support = [2, 1, 0]
        report = receipt(columns, lhs, support, ['2', '0', '3'])
        self.assertEqual([p['variable'] for p in report['pivots']], [2, 0])
        self.assertEqual(report['retained_variable_indices'], [1])
        self.assertTrue(I.verify_leaf_solution(columns, lhs, support, ['2', '0', '3'], report)['verified'])
        alternate = receipt(columns, lhs, support, ['2', '5', '-2'])
        self.assertTrue(I.verify_leaf_solution(columns, lhs, support, ['2', '5', '-2'], alternate)['verified'])
        with self.assertRaises(ValueError): I.verify_leaf_solution(columns, lhs, support, ['2', '5', '-2'], report)

    def test_minimum_original_id_not_support_position(self):
        columns = [{0: F(1)}, {1: F(1)}]; lhs = {0: F(2), 1: F(3)}; support = [1, 0]
        report = receipt(columns, lhs, support, ['3', '2'])
        self.assertEqual(report['pivots'][0]['variable'], 0)
        self.assertEqual(report['pivots'][0]['support_position'], 1)
        self.assertTrue(I.verify_leaf_solution(columns, lhs, support, ['3', '2'], report)['verified'])

    def test_rhs_only_contradiction_retained(self):
        columns = [{0: F(1)}]; lhs = {0: F(2), 1: F(1)}; support = [0]
        rebuilt = I.rebuild_leaf_system(columns, lhs, support)
        self.assertEqual(rebuilt['retained_rows'], [1])
        self.assertEqual(rebuilt['reduced_target'], {1: F(1)})
        self.assertEqual(rebuilt['inconsistent_rhs_rows'], [1])
        report = receipt(columns, lhs, support)
        self.assertTrue(I.verify_leaf_preprocessing(columns, lhs, support, report)['verified'])
        impossible = receipt(columns, lhs, support, ['2'])
        with self.assertRaises(ValueError): I.verify_leaf_solution(columns, lhs, support, ['2'], impossible)
        bad = copy.deepcopy(report); bad['retained_rows'] = []
        with self.assertRaises(ValueError): I.verify_leaf_preprocessing(columns, lhs, support, bad)

    def test_explicit_zero_rows_preserved(self):
        columns = [{0: F(1), 4: F(0)}, {}]; lhs = {0: F(2), 7: F(0)}; support = [0, 1]
        rebuilt = I.rebuild_leaf_system(columns, lhs, support)
        self.assertEqual(rebuilt['original_row_labels'], [0, 4, 7])
        self.assertEqual(rebuilt['reduced_target'], {4: F(0), 7: F(0)})
        self.assertTrue(I.verify_leaf_solution(columns, lhs, support, ['2', '0'], receipt(columns, lhs, support, ['2', '0']))['verified'])

    def test_negative_reconstructed_slack_rejected_when_required(self):
        columns = [{0: F(1), 1: F(1)}, {0: F(-1)}]; lhs = {0: F(2), 1: F(1)}; support = [0, 1]
        report = receipt(columns, lhs, support, ['1', '-1'])
        self.assertTrue(I.verify_leaf_solution(columns, lhs, support, ['1', '-1'], report)['verified'])
        with self.assertRaisesRegex(ValueError, 'nonnegative'):
            I.verify_leaf_solution(columns, lhs, support, ['1', '-1'], report, require_nonnegative=True)

    def test_pivot_rhs_and_returned_weight_tampering(self):
        columns = [{0: F(2)}, {1: F(3)}]; lhs = {0: F(8), 1: F(15)}; support = [0, 1]
        report = receipt(columns, lhs, support, ['4', '5'])
        for key, value in [('variable', 1), ('coefficient', '3'), ('rhs', '9'), ('equation', [[0, '3']])]:
            bad = copy.deepcopy(report); bad['pivots'][0][key] = value
            with self.assertRaises(ValueError): I.verify_leaf_solution(columns, lhs, support, ['4', '5'], bad)
        with self.assertRaises(ValueError): I.verify_leaf_solution(columns, lhs, support, ['5', '5'], report)
        with self.assertRaises(ValueError): I.verify_leaf_solution(columns, lhs, support, ['4'], report)

    def test_support_and_bit_limits(self):
        columns = [{0: F(1)}, {}]; lhs = {0: F(2)}
        with self.assertRaises(ValueError): I.rebuild_leaf_system(columns, lhs, [0, 0])
        with self.assertRaises(ValueError): I.rebuild_leaf_system(columns, lhs, [2])
        with self.assertRaises(ValueError): I.rebuild_leaf_system([{0: 1.0}], lhs, [0])
        with self.assertRaises(OverflowError): I.rebuild_leaf_system(columns, lhs, [0, 1], max_columns=1)
        report = receipt(columns, lhs, [0], ['2'])
        with self.assertRaises(OverflowError): I.verify_leaf_solution(columns, lhs, [0], ['2'], report, max_coefficient_bits=1)
        fractional = [{0: F(3)}]; target = {0: F(1)}
        with self.assertRaises(OverflowError):
            I.verify_leaf_solution(fractional, target, [0], ['1/3'], receipt(fractional, target, [0], ['1/3']), max_denominator=2)

    def test_native_resource_receipt_and_reduced_rhs_tampering(self):
        columns = [{0: F(1), 1: F(1)}, {0: F(1), 1: F(1)}, {0: F(2)}]
        lhs = {0: F(7), 1: F(3)}; support = [2, 1, 0]; answer = ['2', '0', '3']
        report = receipt(columns, lhs, support, answer)
        for field in ('preprocessing_work', 'preprocessing_cells', 'preprocessing_actual_work', 'preprocessing_actual_cells',
                      'backsubstitution_work_reserve', 'full_verification_work_reserve', 'leaf_total_work_proxy', 'total_work_proxy'):
            bad = copy.deepcopy(report); bad[field] += 1
            with self.assertRaises(ValueError): I.verify_leaf_solution(columns, lhs, support, answer, bad)
        bad = copy.deepcopy(report); bad['remaining_compression']['mapping'] = [dict(row=0, representative=0, ratio='1')]
        with self.assertRaises(ValueError): I.verify_leaf_solution(columns, lhs, support, answer, bad)
        bad = copy.deepcopy(report); bad['remaining_system_hash'] = '0'*64
        with self.assertRaises(ValueError): I.verify_leaf_solution(columns, lhs, support, answer, bad)
        with self.assertRaises(OverflowError): I.verify_leaf_solution(columns, lhs, support, answer, report, max_work=1)
        with self.assertRaises(OverflowError): I.verify_leaf_solution(columns, lhs, support, answer, report, max_preprocessing_cells=1)
        with self.assertRaises(OverflowError): I.verify_leaf_solution(columns, lhs, support, answer, report, max_receipt_bytes=1)

    def test_remaining_native_cells_and_normalization_bits(self):
        columns = [{0: F(1), 1: F(1)}, {0: F(1), 1: F(1)}]
        lhs = {0: F(2), 1: F(2)}; support = [0, 1]; answer = ['2', '0']
        report = receipt(columns, lhs, support, answer)
        with self.assertRaises(OverflowError): I.verify_leaf_solution(columns, lhs, support, answer, report, max_cells=2)
        columns = [{0: F(1, 7), 1: F(1, 7)}, {0: F(7), 1: F(7)}]
        lhs = {0: F(7), 1: F(7)}; answer = ['0', '1']
        report = receipt(columns, lhs, support, answer)
        with self.assertRaises(OverflowError): I.verify_leaf_solution(columns, lhs, support, answer, report, max_coefficient_bits=3)

    def test_actual_producer_receipts_replayed_independently(self):
        import native_exact_support_leaf as producer
        fixtures = [([{0: F(2)}, {1: F(3)}], {0: F(8), 1: F(15)}, [1, 0]),
                    ([{0: F(1), 1: F(1)}, {0: F(1), 1: F(1)}, {0: F(2)}], {0: F(7), 1: F(3)}, [2, 1, 0]),
                    ([{0: F(1), 1: F(1)}, {0: F(1), 1: F(1)}], {0: F(2), 1: F(2)}, [0, 1]),
                    ([{0: F(1), 4: F(0)}, {}], {0: F(2), 7: F(0)}, [0, 1]),
                    ([{}], {}, []), ([{}], {4: F(0)}, [0])]
        for columns, lhs, support in fixtures:
            diagnostics = {}
            answer = producer.exact_support_solution(columns, lhs, support, diagnostics=diagnostics)
            report = diagnostics['leaf_elimination']
            self.assertTrue(I.verify_leaf_solution(columns, lhs, support, answer, report)['resource_limits_verified'])
        diagnostics = {}
        self.assertIsNone(producer.exact_support_solution([{0: F(1)}], {0: F(2), 1: F(1)}, [0], diagnostics=diagnostics))
        self.assertTrue(I.verify_leaf_preprocessing([{0: F(1)}], {0: F(2), 1: F(1)}, [0], diagnostics['leaf_elimination'])['rhs_only_rows_retained'])


if __name__ == '__main__':
    unittest.main()
