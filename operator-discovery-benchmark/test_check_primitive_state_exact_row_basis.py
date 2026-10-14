import ast
import copy
from fractions import Fraction as F
import inspect
import time
import unittest
import primitive_state_exact_row_basis as producer
import check_primitive_state_exact_row_basis as checker


class IndependentBasisTests(unittest.TestCase):
    def fixture(self,rows=None,rhs=None,n=3,**limits):
        rows=[{0:F(1),1:F(1)},{1:F(1),2:F(1)},{0:F(1),1:F(2),2:F(1)},{}] if rows is None else rows
        rhs=list(map(F,[2,3,5,0] if rhs is None else rhs))
        selected,targets,receipt=producer.reduce_rows(rows,rhs,n,deadline=time.monotonic()+10,**limits)
        return rows,rhs,n,selected,targets,receipt

    def test_exact_nonproportional_dependency_and_complete_counts(self):
        args=self.fixture();out=checker.verify_rows(*args)
        self.assertTrue(out['reduction_authorized']);self.assertEqual(out['retained_rows'],2)
        self.assertTrue(out['all_original_augmented_rows_replayed']);self.assertFalse(out['infeasibility_proved'])
        self.assertEqual(out['counts'],args[-1]['counts'])
        self.assertGreater(out['independent_audit_work_reserve'],out['audit_operations'])

    def test_signed_fraction_zero_and_sparse_pivot_order(self):
        for rows,rhs in [([{0:F(0)},{0:F(-2),1:F(1,3)},{0:F(6),1:F(-1)}],[0,-4,12]),
                         ([{2:F(1)},{0:F(1),2:F(2)},{0:F(3),1:F(1),2:F(6)},{1:F(1)}],[2,5,17,2])]:
            self.assertTrue(checker.verify_rows(*self.fixture(rows,rhs))['verified'])

    def test_augmented_rhs_contradiction_never_dropped(self):
        args=self.fixture([{0:F(1)},{0:F(1)},{},{}],[1,2,0,3],n=1)
        out=checker.verify_rows(*args)
        self.assertTrue(out['inconsistent_augmented_pivots']);self.assertEqual(out['augmented_rank'],2)
        self.assertFalse(out['infeasibility_proved'])
        args[-1]['inconsistent_augmented_pivots']=[]
        with self.assertRaises(ValueError):checker.verify_rows(*args)

    def test_every_complete_receipt_binding(self):
        original=self.fixture()
        edits=dict(source_hash='bad',row_order=list(reversed(original[-1]['row_order'])),retained_indices=[],pivot_columns=[],
            augmented_rank=1,coefficient_consistency='inconsistent',variable_mapping='projected',objective_mapping='projected',
            cone_mapping='projected',original_rows=3,variables=2,complete=False,augmented_rhs_column=4)
        for key,value in edits.items():
            args=copy.deepcopy(original);args[-1][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):checker.verify_rows(*args)
        for key in original[-1]['counts']:
            args=copy.deepcopy(original);args[-1]['counts'][key]+=1
            with self.subTest(count=key),self.assertRaises(ValueError):checker.verify_rows(*args)

    def test_transcript_omissions_coefficients_and_normalization(self):
        original=self.fixture()
        for mode in ('missing-row','row-order','missing-step','wrong-step','noncanonical-text','normalization','new-pivot'):
            args=copy.deepcopy(original);tape=args[-1]['transcript']
            if mode=='missing-row':tape.pop()
            elif mode=='row-order':tape[0]['source_row']=tape[1]['source_row']
            elif mode=='missing-step':next(r for r in tape if r['steps'])['steps'].pop()
            elif mode=='wrong-step':next(r for r in tape if r['steps'])['steps'][0][1]='7'
            elif mode=='noncanonical-text':next(r for r in tape if r['steps'])['steps'][0][1]='+1'
            elif mode=='normalization':next(r for r in tape if r['normalization'])['normalization']='9'
            else:next(r for r in tape if r['pivot_column']is not None)['pivot_column']=3
            with self.subTest(mode=mode),self.assertRaises(ValueError):checker.verify_rows(*args)

    def test_selected_are_original_rows_and_rhs(self):
        args=self.fixture();args[3][0]={0:F(99)}
        with self.assertRaises(ValueError):checker.verify_rows(*args)
        args=self.fixture();args[4][0]+=1
        with self.assertRaises(ValueError):checker.verify_rows(*args)
        args=self.fixture();args[3][0][0]=1.0
        with self.assertRaises(ValueError):checker.verify_rows(*args)
        args=self.fixture();args[4][0]=2.0
        with self.assertRaises(ValueError):checker.verify_rows(*args)
        args=self.fixture();args[3].reverse()
        with self.assertRaises(ValueError):checker.verify_rows(*args)

    def test_unknown_limits_never_license_reduction(self):
        for options in [dict(max_operations=1),dict(max_source_cells=1),dict(max_live_cells=1),dict(max_fill_cells=1),
                        dict(max_receipt_bytes=256),dict(max_coefficient_bits=1)]:
            args=self.fixture([{0:F(2),1:F(3)}],[1],**options)
            out=checker.verify_rows(*args)
            self.assertTrue(out['verified']);self.assertFalse(out['reduction_authorized']);self.assertFalse(out['complete'])
            self.assertIsNone(args[3]);self.assertIsNone(args[4])
            args=list(args);args[3]=[];args[4]=[]
            with self.assertRaises(ValueError):checker.verify_rows(*args)

    def test_unknown_deadline_and_partial_resource_metadata(self):
        rows=[{0:F(1)}];rhs=[F(0)]
        selected,targets,receipt=producer.reduce_rows(rows,rhs,1,deadline=time.monotonic()-1)
        out=checker.verify_rows(rows,rhs,1,selected,targets,receipt)
        self.assertEqual(out['reason'],'deadline')
        receipt['complete']=True
        with self.assertRaises(ValueError):checker.verify_rows(rows,rhs,1,None,None,receipt)

    def test_independent_limits_source_exactness_and_identity_scope(self):
        args=self.fixture()
        for limits in [dict(max_audit_operations=1),dict(max_audit_cells=1),dict(max_receipt_bytes=256),dict(max_coefficient_bits=1)]:
            with self.assertRaises((OverflowError,ValueError)):checker.verify_rows(*args,**limits)
        with self.assertRaises(TimeoutError):checker.verify_rows(*args,deadline=time.monotonic()-1)
        for coordinate in (True,3):
            bad=self.fixture();bad[0][0]={coordinate:F(1)}
            with self.assertRaises(ValueError):checker.verify_rows(*bad)
        bad=self.fixture();bad[0][0][0]=1.0
        with self.assertRaises(ValueError):checker.verify_rows(*bad)
        bad=self.fixture();bad[-1]['certified']=True
        with self.assertRaises(ValueError):checker.verify_rows(*bad)
        bad=self.fixture();bad[-1]['limits']['max_operations']=450000001
        with self.assertRaises(ValueError):checker.verify_rows(*bad)

    def test_empty_rows_and_independent_source_no_producer_imports(self):
        self.assertEqual(checker.verify_rows(*self.fixture([],[],n=1))['augmented_rank'],0)
        modules=[]
        for node in ast.walk(ast.parse(inspect.getsource(checker))):
            if isinstance(node,ast.Import):modules.extend(n.name for n in node.names)
            elif isinstance(node,ast.ImportFrom):modules.append(node.module)
        self.assertNotIn('primitive_state_exact_row_basis',modules)
        self.assertFalse(any(name in modules for name in ['numpy','scipy','cvxpy','clarabel']))

if __name__=='__main__':unittest.main()
