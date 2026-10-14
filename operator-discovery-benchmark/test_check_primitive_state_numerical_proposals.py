import copy
import time
import unittest
from fractions import Fraction as F
import check_primitive_state_numerical_proposals as C


class IndependentNumericalAuditTests(unittest.TestCase):
    def fixture(self):
        rows = [{0:F(2),1:F(-4)}, {0:F(-6),1:F(12)}, {}, {}, {1:F(1)}, {1:F(2)}]
        rhs = [F(8),F(-24),F(0),F(3),F(1),F(3)]
        reduced = [rows[i] for i in (0,3,4,5)]
        targets = [rhs[i] for i in (0,3,4,5)]
        receipt = dict(schema='primitive-state-exact-row-compression-v1',
            original_hash=C.digest(dict(rows=[[[j,str(q)] for j,q in sorted(p.items())] for p in rows],rhs=list(map(str,rhs)),variables=2)),
            original_rows=6,variables=2,retained_indices=[0,3,4,5],row_representative=[0,0,None,1,2,3],
            row_multiplier=['1','-3','0','1','1','1'],row_scales=['8','3','1','3'],variable_mapping='identity',
            inconsistent_zero_rows=[3],operations=23,cells=12,
            limits=dict(max_operations=200000000,max_cells=4000000,max_coefficient_bits=4096))
        return rows,rhs,2,reduced,targets,receipt

    def test_exact_signed_augmented_rows(self):
        args=self.fixture()
        out=C.verify_transformation(*args)
        self.assertTrue(out['verified'])
        self.assertFalse(out['certified'])
        self.assertFalse(out['exact_admission'])

    def test_every_receipt_binding(self):
        edits={'original_hash':'wrong','original_rows':5,'variables':3,'retained_indices':[0,3,4],
               'row_representative':[0,0,None,None,2,3],'row_multiplier':['1','3','0','1','1','1'],
               'row_scales':['4','3','1','3'],'variable_mapping':'permuted','inconsistent_zero_rows':[],
               'operations':21,'cells':13}
        for key,value in edits.items():
            with self.subTest(key=key):
                args=list(self.fixture());args[-1][key]=value
                with self.assertRaises(ValueError): C.verify_transformation(*args)

    def test_matrix_and_target_complete(self):
        for mode in ('coefficient','target','missing'):
            args=list(self.fixture());args[3]=copy.deepcopy(args[3]);args[4]=args[4][:]
            if mode=='coefficient':args[3][0].pop(1)
            elif mode=='target':args[4][0]=F(7)
            else:args[3].pop();args[4].pop()
            with self.assertRaises(ValueError):C.verify_transformation(*args)

    def test_coefficient_and_resource_bounds(self):
        with self.assertRaises(TimeoutError):C.verify_transformation(*self.fixture(),deadline=time.monotonic()-1)
        with self.assertRaises(OverflowError):C.verify_transformation(*self.fixture(),max_audit_operations=1)
        with self.assertRaises(OverflowError):C.verify_transformation(*self.fixture(),max_audit_cells=1)
        with self.assertRaises(OverflowError):C.verify_transformation(*self.fixture(),max_coefficient_bits=2)
        args=list(self.fixture());args[-1]['limits']['max_cells']=4000001
        with self.assertRaises(ValueError):C.verify_transformation(*args)

    def test_no_implicit_coordinates_or_float_proof(self):
        for value in ({0:1.0},[1.0],[1.0,float('nan')],[1.0,True]):
            with self.assertRaises(ValueError):C.verify_complete_vector(value,2)
        diag=dict(attempts=[dict(solver='CLARABEL',status='optimal')],sdp_status='optimal')
        self.assertTrue(C.verify_proposal_diagnostics(diag,[1.0,2.0],2)['verified'])
        diag['certified']=True
        with self.assertRaises(ValueError):C.verify_proposal_diagnostics(diag,[1.0,2.0],2)

    def test_explicit_failures_and_support(self):
        for diag in (dict(attempts=[dict(solver='highs',status=4)],solver_status=4),
                     dict(attempts=[dict(solver='CLARABEL',error='failure')],solver_error='failure'),
                     dict(attempts=[],reason='inconsistent exact zero row')):
            self.assertTrue(C.verify_proposal_diagnostics(diag,None,2)['verified'])
        with self.assertRaises(ValueError):C.verify_proposal_diagnostics(dict(attempts=[]),None,2)
        d=dict(attempts=[dict(solver='highs',status=0)],solver_status=0,support=[1])
        self.assertTrue(C.verify_proposal_diagnostics(d,[1],2,proposal_kind='dual')['verified'])
        with self.assertRaises(ValueError):C.verify_proposal_diagnostics(d,[0],2,proposal_kind='dual')
        d['solver_status']=4
        with self.assertRaises(ValueError):C.verify_proposal_diagnostics(d,[1],2,proposal_kind='dual')

    def test_independent_primal_PSD_layout(self):
        cols=[{(0,):F(1)}, {(0,):F(-1)}, {(0,):F(2)}, {(1,):F(1)}]
        rows,rhs,n,layout=C.rebuild_primal_system(cols,{(0,):F(3)},[(0,),(1,)],(1,0),1,{'K':2})
        self.assertEqual(rows,[{0:F(1),1:F(-1),2:F(2)},{3:F(1)}])
        self.assertEqual(rhs,[F(3),F(0)])
        self.assertEqual(layout,[('K',0,0,1),('K',0,1,2),('K',1,1,3)])
        with self.assertRaises(ValueError):C.rebuild_primal_system(cols,{(0,):F(3)},[(0,)],(1,0),1,{'K':2})
        with self.assertRaises(ValueError):C.rebuild_primal_system(cols,{(0,):F(3)},[(0,),(1,)],(1,0),1,{'K':1})

    def test_independent_dual_signed_and_slack_coordinates(self):
        rows,rhs,n=C.rebuild_dual_system([{(0,):F(2)},{(1,):F(-3)}],{(0,):F(1)},[(0,),(1,)],[0],[1])
        self.assertEqual(n,5)
        self.assertEqual(rows,[{1:F(-3),3:F(3)},{0:F(2),2:F(-2),4:F(-1)},{0:F(1),2:F(-1)}])
        self.assertEqual(rhs,[F(0),F(0),F(-1)])
        with self.assertRaises(ValueError):C.rebuild_dual_system([{(0,):F(2)}],{},[(0,)],[],[])

if __name__=='__main__':unittest.main()
