import copy
import time
import unittest
from fractions import Fraction as F
from unittest.mock import patch
import native_exact_support_leaf as L


class LeafTests(unittest.TestCase):
    def solve(self, columns, rhs, support, **limits):
        diagnostics = {}
        answer = L.exact_support_solution(columns, rhs, support, diagnostics=diagnostics, **limits)
        return answer, diagnostics['leaf_elimination']

    def test_column_leaf_without_any_singleton_row(self):
        # Every equation has at least two coefficients. Only x2 is a leaf.
        columns=[{0:F(1),1:F(1),2:F(1)},
                 {0:F(1),1:F(-1),2:F(1)}, {0:F(1)}]
        answer,receipt=self.solve(columns,{0:F(3),1:F(1),2:F(3)},[0,1,2])
        self.assertEqual(answer,[F(2),F(1),F(0)])
        self.assertEqual([p['variable'] for p in receipt['pivots']],[2])
        self.assertEqual(receipt['retained_variable_indices'],[0,1])
        self.assertEqual(receipt['retained_rows'],[1,2])
        self.assertEqual(receipt['remaining_compression']['support_size'],2)
        self.assertEqual(receipt['exact_support_weights'],['2','1','0'])
        self.assertEqual(receipt['reduced_solution'],['2','1'])

    def test_cascade_reverse_affine_substitution(self):
        answer,receipt=self.solve([{0:F(1),1:F(1)}, {0:F(1)}],{0:F(7),1:F(3)},[0,1])
        self.assertEqual(answer,[F(3),F(4)])
        self.assertEqual([p['variable'] for p in receipt['pivots']],[1,0])
        self.assertEqual(receipt['remaining_variables'],0)
        self.assertEqual(receipt['backsubstitution_values'],[dict(variable=0,value='3'),dict(variable=1,value='4')])

    def test_order_uses_original_variable_id_not_support_position(self):
        answer,receipt=self.solve([{7:F(1)}, {7:F(1)}, {8:F(1)}],{7:F(5),8:F(9)},[2,0,1])
        self.assertEqual(answer,[F(9),F(5),F(0)])
        self.assertEqual([p['variable'] for p in receipt['pivots']],[0,2])
        self.assertEqual(receipt['retained_support_positions'],[2])
        self.assertEqual(receipt['retained_variable_indices'],[1])

    def test_signed_restoration_does_not_assume_nonnegative(self):
        answer,receipt=self.solve([{0:F(-2)}],{0:F(7)},[0])
        self.assertEqual(answer,[F(-7,2)])
        self.assertEqual(receipt['pivots'][0]['coefficient'],'-2')
        self.assertEqual(receipt['status'],'full_original_equality_verified')

    def test_degree_zero_variable_kept_and_zero_rows_preserved(self):
        columns=[{0:F(1),1:F(2),2:F(0)},{}]
        answer,receipt=self.solve(columns,{0:F(-3),1:F(-6),2:F(0)},[0,1])
        self.assertEqual(answer,[F(-3),F(0)])
        self.assertEqual(receipt['original_row_labels'],[0,1,2])
        self.assertEqual(receipt['retained_rows'],[0,1,2])
        self.assertEqual(receipt['remaining_compression']['mapping'][2]['representative'],None)

    def test_rhs_only_contradiction_cannot_be_eliminated(self):
        answer,receipt=self.solve([{0:F(1)}],{0:F(2),1:F(3)},[0])
        self.assertIsNone(answer)
        self.assertEqual(receipt['retained_rows'],[1])
        self.assertEqual(receipt['remaining_compression']['original_row_labels'],[1])
        self.assertEqual(receipt['status'],'remaining_system_inconsistent')

    def test_remaining_inconsistency_preserved(self):
        answer,receipt=self.solve([{0:F(1),1:F(2)}],{0:F(1),1:F(3)},[0])
        self.assertIsNone(answer)
        self.assertEqual(receipt['pivots'],[])
        self.assertEqual(receipt['remaining_compression']['reduced_rows'],2)

    def test_original_equations_rechecked_after_native(self):
        columns=[{0:F(1),1:F(1),2:F(1)},
                 {0:F(1),1:F(-1),2:F(1)}, {0:F(1)}]
        real=L.N.exact_support_solution
        def corrupt(*args,**kwargs):
            result=real(*args,**kwargs)
            result[0]+=1
            return result
        with patch.object(L.N,'exact_support_solution',side_effect=corrupt):
            with self.assertRaisesRegex(ValueError,'full original equality'):
                self.solve(columns,{0:F(3),1:F(1),2:F(3)},[0,1,2])

    def test_caps_and_receipt_before_native(self):
        for limits in ({'max_work':1},{'max_preprocessing_operations':1},
                       {'max_preprocessing_cells':1},{'max_receipt_bytes':1},
                       {'max_rows':1},{'max_columns':1},
                       {'deadline':time.monotonic()-1}):
            with self.subTest(limits=limits):
                with patch.object(L.N,'exact_support_solution',side_effect=AssertionError('native forbidden')):
                    with self.assertRaises((OverflowError,TimeoutError)):
                        self.solve([{0:F(1),1:F(1)},{0:F(1)}],{0:F(2),1:F(1)},[0,1],**limits)

    def test_bits_and_restored_denominator(self):
        with self.assertRaisesRegex(OverflowError,'coefficient bits'):
            self.solve([{0:F(1,7)}],{0:F(7)},[0],max_coefficient_bits=3)
        with self.assertRaisesRegex(OverflowError,'denominator'):
            self.solve([{0:F(3)}],{0:F(1)},[0],max_denominator=2)

    def test_input_validation_and_no_mutation(self):
        columns=[{0:F(1),1:F(1)},{0:F(1)}];rhs={0:F(7),1:F(3)};support=[0,1]
        before=copy.deepcopy((columns,rhs,support))
        self.solve(columns,rhs,support)
        self.assertEqual((columns,rhs,support),before)
        for bad in ([0,0],[True],[-1],[2]):
            with self.assertRaises(ValueError):self.solve(columns,rhs,bad)
        with self.assertRaises(ValueError):self.solve([{0:1.0}],{0:F(1)},[0])
        with self.assertRaises(ValueError):self.solve(columns,rhs,support,max_work=450000001)

    def test_resource_receipt_ledgers_and_reserves(self):
        answer,receipt=self.solve([{0:F(1),1:F(1)},{0:F(1)}],{0:F(7),1:F(3)},[0,1])
        p=receipt['pivot_entry_count'];n=receipt['original_variables'];m=receipt['original_rows'];nnz=receipt['selected_nonzero_count']
        self.assertEqual(receipt['backsubstitution_work_reserve'],8*p+4*len(receipt['pivots'])+2*n+1)
        self.assertEqual(receipt['full_verification_work_reserve'],6*nnz+3*2+3*m+4*n+1)
        self.assertEqual(receipt['leaf_total_work_proxy'],receipt['preprocessing_work']+receipt['backsubstitution_work_reserve']+receipt['full_verification_work_reserve']+receipt['remaining_compression']['total_work_proxy'])
        self.assertEqual(receipt['preprocessing_actual_work'],sum(receipt['work_ledger'].values()))
        self.assertLessEqual(receipt['preprocessing_actual_work'],receipt['leaf_total_work_proxy'])

    def test_dual_same_support_and_all_weights_nonnegative(self):
        r=L.reconstruct_dual_fixed_support([{0:F(1)},{0:F(-1)}],{1:F(-1)},[0,1],[],[0,1],[1],time_limit=5,compilation_work_reserve=23)
        self.assertEqual(r['status'],'exact_separator',r)
        self.assertEqual(r['saved_support'],[1]);self.assertEqual(r['exact_support_weights'],['1'])
        self.assertEqual(r['lhs_dot_y'],'-1')
        info=r['diagnostics']['leaf_elimination']
        self.assertEqual(info['compilation_work_reserve'],23)
        self.assertEqual(info['total_work_proxy'],info['leaf_total_work_proxy']+23+info['dual_build_work_proxy']+info['dual_verification_work_reserve'])
        self.assertLessEqual(info['total_work_proxy'],450000000)

    def test_negative_restored_dual_slack_is_unknown(self):
        # y=-1 forces the restored singleton slack to -1. Equality alone is
        # insufficient; a different support has not been searched or excluded.
        r=L.reconstruct_dual_fixed_support([{0:F(1)}],{0:F(1)},[0],[0],[],[1,2],time_limit=5)
        self.assertEqual(r['status'],'uncertified',r)
        self.assertFalse(r['certified'])
        self.assertEqual(r['diagnostics']['leaf_elimination']['exact_support_weights'],['1','-1'])

    def test_checkpoint_precedes_native_and_is_detached(self):
        saved=[]
        diagnostics={}
        real=L.N.exact_support_solution
        def native(*args,**kwargs):
            self.assertEqual(saved[-1]['status'],'prepared_remaining_system')
            self.assertNotIn('reduced_solution',saved[-1])
            return real(*args,**kwargs)
        with patch.object(L.N,'exact_support_solution',side_effect=native):
            answer=L.exact_support_solution([{0:F(1)}],{0:F(4)},[0],
                diagnostics=diagnostics,on_checkpoint=saved.append)
        self.assertEqual(answer,[F(4)])
        self.assertEqual(saved[0]['status'],'prepared_remaining_system')
        self.assertEqual(saved[-1]['status'],'full_original_equality_verified')
        self.assertNotIn('reduced_solution',saved[0])
        saved[0]['pivots'][0]['rhs']='999'
        self.assertEqual(diagnostics['leaf_elimination']['pivots'][0]['rhs'],'4')

    def test_callback_failure_stops_native(self):
        def fail(receipt):raise OSError('checkpoint unavailable')
        with patch.object(L.N,'exact_support_solution',side_effect=AssertionError('must not run')):
            with self.assertRaisesRegex(RuntimeError,'checkpoint callback failed'):
                L.exact_support_solution([{0:F(1)}],{0:F(4)},[0],on_checkpoint=fail)


if __name__=='__main__':unittest.main()
