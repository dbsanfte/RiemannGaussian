import unittest
from fractions import Fraction as F
import time
import check_primitive_state_triangular_restoration as C


class ExactRestorationTests(unittest.TestCase):
    def budget(self,**kw):return C.EXACT._Budget(kw.get('deadline'),kw.get('operations',1000000),1000000,kw.get('bits',4096))
    def test_psd_positive_and_singular(self):
        for a in ([[F(2),F(1)],[F(1),F(2)]],[[F(1),F(1)],[F(1),F(1)]],[[F(0),F(0)],[F(0),F(2)]]):
            self.assertTrue(C.exact_psd(a,self.budget())['psd'])
    def test_negative_witness_original_coordinates(self):
        for a in ([[F(1),F(2)],[F(2),F(1)]],[[F(0),F(1)],[F(1),F(100)]],[[F(-1),F(0)],[F(0),F(2)]]):
            out=C.exact_psd(a,self.budget());self.assertFalse(out['psd'])
            v=list(map(F,out['witness']));value=sum(v[i]*a[i][j]*v[j] for i in range(2) for j in range(2))
            self.assertEqual(str(value),out['quadratic_value']);self.assertLess(value,0)
    def test_descending_column_not_insertion_order(self):
        basis=[{1:F(1),2:F(2),3:F(5)},{0:F(1),1:F(3),3:F(7)}]
        self.assertEqual(C.backsubstitute(basis,[F(99),F(99),F(1)],3,self.budget()),[F(-2),F(3),F(1)])
    def test_no_inconsistent_pivot_or_missing_seed(self):
        with self.assertRaises(ValueError):C.backsubstitute([{2:F(1)}],[F(0),F(0)],2,self.budget())
        with self.assertRaises(ValueError):C.backsubstitute([],[F(0)],2,self.budget())
    def test_limits_and_deadline_are_unknown_exceptions(self):
        with self.assertRaises(OverflowError):C.exact_psd([[F(1),F(1,128)],[F(1,128),F(1)]],self.budget(bits=4))
        with self.assertRaises(TimeoutError):C.exact_psd([[F(1)]],self.budget(deadline=time.monotonic()-1))
        with self.assertRaises(OverflowError):C.exact_psd([[F(1)]],self.budget(operations=1))
    def test_psd_symmetry_and_canonical_rationals(self):
        with self.assertRaises(ValueError):C.exact_psd([[F(1),F(0)],[F(1),F(1)]],self.budget())
        with self.assertRaises(ValueError):C.rational('2/2',self.budget())

class FullRestorationTests(unittest.TestCase):
    def fixture(self,negative=False):
        import primitive_state_triangular_restoration as P
        import primitive_state_equation_projection as PROJ
        import primitive_state_exact_row_basis as BASIS
        domain=[(0,)];shape=[1,1];offset=3;n=363;specs={'full_child':15,'full_parent':15,'storage_K':15}
        columns=[{} for _ in range(n)];columns[0]={(0,):F(1)};lhs={(0,):F(1)}
        retained,recipes,_=C.derive_projection(shape,offset,specs,n)
        rows,rhs,projection=PROJ.project_equations(columns,lhs,domain,retained,recipes,deadline=time.monotonic()+30)
        _,_,basis= BASIS.reduce_rows(rows,rhs,len(retained),deadline=time.monotonic()+30)
        cache={'original':dict(columns=[[[0,str(col[(0,)])]] if col else [] for col in columns],rhs=['1'],monomials=[[0]],shape=shape,offset=offset,specs=[[k,v] for k,v in sorted(specs.items())],selected_original_indices=[0])}
        vector=[0.0]*n
        if negative:vector[offset]=-1.0
        trace={'original_vector':vector}
        receipt=P.restore(cache,trace,basis,projection,deadline=time.monotonic()+30)
        return cache,trace,basis,projection,receipt
    def test_complete_restoration_full_cones(self):
        out=C.verify_restoration(*self.fixture())
        self.assertTrue(out['restoration_verified']);self.assertTrue(out['finite_candidate_feasible'])
        self.assertEqual(out['original_variables'],363)
    def test_restored_affine_candidate_rejected_by_exact_psd(self):
        out=C.verify_restoration(*self.fixture(True));self.assertTrue(out['restoration_verified'])
        self.assertFalse(out['finite_candidate_feasible']);self.assertFalse(out['exact_candidate_checks']['psd_blocks']['storage_K']['psd'])
    def test_rehashed_seed_and_candidate_tampering(self):
        import copy
        args=self.fixture()
        for key in ('seed_projected_vector','restored_projected_vector','candidate_original_vector'):
            bad=list(args);bad[-1]=copy.deepcopy(args[-1]);bad[-1][key][0]='2'
            if key=='candidate_original_vector':bad[-1]['candidate_hash']=C.digest(bad[-1][key])
            with self.assertRaises(ValueError):C.verify_restoration(*bad)
    def test_projection_coefficient_identity_not_just_recipe_label(self):
        args=list(self.fixture());args[0]['original']['columns'][2]=[[0,'1']]
        args[-1]['input_bindings']['cache']=C.digest(args[0])
        with self.assertRaises(ValueError):C.verify_restoration(*args)
    def test_forged_ldl_and_failure_witness(self):
        import copy
        for negative in (False,True):
            args=list(self.fixture(negative));args[-1]=copy.deepcopy(args[-1])
            report=args[-1]['diagnostics']['psd'][-1]
            if negative:report['witness']['value']='-2'
            else:report.update(rank=1,weights=['1'],vectors=[['1']+['0']*14])
            with self.assertRaises(ValueError):C.verify_restoration(*args)
    def test_fast_rejection_is_explicitly_limited(self):
        args=self.fixture(True);out=C.verify_candidate_rejection(args[-1],3,dict(args[0]['original']['specs']))
        self.assertTrue(out['explicit_candidate_rejected']);self.assertFalse(out['restoration_verified'])
        self.assertFalse(out['all_original_equations_checked']);self.assertFalse(out['infeasibility_proved'])
        with self.assertRaises(ValueError):C.verify_candidate_rejection(self.fixture()[4],3,dict(args[0]['original']['specs']))
    def test_bound_resource_counts_cannot_be_promoted(self):
        args=list(self.fixture());args[-1]['counts']['operations']=125000001
        with self.assertRaises(ValueError):C.verify_restoration(*args)
    def test_partial_never_promoted(self):
        args=list(self.fixture());r=args[-1];r.update(status='unknown',complete=False,reason='bit cap')
        out=C.verify_restoration(*args);self.assertFalse(out['restoration_verified']);self.assertIsNone(out['finite_candidate_feasible'])

if __name__=='__main__':unittest.main()
