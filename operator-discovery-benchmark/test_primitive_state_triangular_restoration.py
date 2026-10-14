from fractions import Fraction as F
import time
import unittest
import primitive_state_triangular_restoration as P

class RestorationTests(unittest.TestCase):
    def budget(self,**kw):return P.Budget(time.monotonic()+10,**kw)
    def test_out_of_order_inserted_pivots(self):
        # First pivot is column2; later minimum-column pivot0 contains column2.
        rows=[{2:F(2)},{0:F(3),2:F(4)}];rhs=[F(10),F(26)]
        tape=dict(complete=True,coefficient_consistency='consistent',inconsistent_augmented_pivots=[],retained_indices=[0,1],pivot_columns=[2,0],augmented_rank=2,transcript=[dict(source_row=0,basis_index=0,pivot_column=2,normalization='2',steps=[]),dict(source_row=1,basis_index=1,pivot_column=0,normalization='3',steps=[])])
        budget=self.budget();normalized,pivots,_=P.retained_replay(rows,rhs,3,tape,budget)
        x=P.back_substitute(normalized,pivots,[F(0)]*3,3,budget);self.assertEqual(x,[F(2),F(0),F(5)])
    def test_backsub_order_not_insertion(self):
        # Triangular rows can retain larger future pivot coordinates.
        budget=self.budget();x=P.back_substitute([{2:F(1),3:F(5)},{0:F(1),2:F(2),3:F(12)}],[2,0],[F(0)]*3,3,budget)
        self.assertEqual(x,[F(2),F(0),F(5)])
    def test_zero_psd_and_singular_positive(self):
        self.assertTrue(P.exact_psd([[F(0),F(0)],[F(0),F(1)]],self.budget())['psd'])
        self.assertTrue(P.exact_psd([[F(1),F(1)],[F(1),F(1)]],self.budget())['psd'])
        self.assertFalse(P.exact_psd([[F(0),F(1)],[F(1),F(0)]],self.budget())['psd'])
        self.assertFalse(P.exact_psd([[F(1),F(2)],[F(2),F(1)]],self.budget())['psd'])
    def test_exact_original_equality_and_sign_diagnostics(self):
        budget=self.budget();d=P.candidate_diagnostics([{0:F(2),1:F(3)}],[F(1)],[F(-1),F(1)],2,{},budget)
        self.assertEqual(d['equality_mismatch_count'],0);self.assertEqual(d['negative_scalar_count'],1);self.assertFalse(d['candidate_cone_checks_pass'])
    def test_caps_and_tape_rejection(self):
        with self.assertRaises(OverflowError):self.budget(max_operations=1).charge(2)
        with self.assertRaises(OverflowError):self.budget(max_bits=2).q(F(8))
        with self.assertRaises(TimeoutError):P.Budget(time.monotonic()-1).charge()
        with self.assertRaises(ValueError):P.back_substitute([{0:F(2)}],[0],[F(1)],1,self.budget())
    def test_quotient_lift_changes_objective_preserves_aggregation(self):
        retained=list(range(1597))+list(range(1597,1837));y=[F(0)]*1224 # construct research retained via actualrecipe
        import primitive_state_equation_projection as Q
        retained,_=Q.full15_recipes([366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957);y=[F(0)]*len(retained);positions={j:i for i,j in enumerate(retained)}
        y[positions[366]]=F(-2);y[positions[1597]]=F(3);y[positions[1717]]=F(-1)
        x=P.canonical_lift(y,retained,[366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957,self.budget())
        self.assertEqual(x[366:368],[F(0),F(2)]);self.assertEqual(x[1597],0);self.assertEqual(x[1837],3);self.assertEqual(x[1717],11);self.assertEqual(x[1597]+x[1837],3);self.assertEqual(x[1717]-4*x[1837],-1)
    def test_complete_research_layout_tiny_source(self):
        cache,trace,basis,projection=fixture()
        result=P.restore(cache,trace,basis,projection,deadline=time.monotonic()+10)
        self.assertTrue(result['complete']);self.assertEqual(result['candidate_original_vector'][0],'2');self.assertTrue(result['diagnostics']['candidate_cone_checks_pass']);self.assertFalse(result['certified'])
        limited=P.restore(cache,trace,basis,projection,deadline=time.monotonic()+10,max_operations=1)
        self.assertFalse(limited['complete']);self.assertEqual(limited['status'],'unknown');self.assertIsNone(limited['candidate_original_vector'])


def fixture():
    import primitive_state_equation_projection as Q
    specs={'full_child':15,'full_parent':15,'storage_K':15};retained,recipes=Q.full15_recipes([366,613],1597,specs,1957)
    columns=[[] for _ in range(1957)];columns[0]=[[0,'1']]
    cache=dict(original=dict(columns=columns,rhs=['2'],monomials=[[0]],shape=[366,613],offset=1597,specs=[[name,n] for name,n in sorted(specs.items())]))
    trace=dict(original_vector=[1.]+[0.]*1956)
    import primitive_state_exact_row_basis as B
    projected,rhs,projection=Q.project_equations([{(0,):F(1)}]+[{} for _ in range(1956)],{(0,):F(2)},[(0,)],retained,recipes,deadline=time.monotonic()+10)
    _,_,basis=B.reduce_rows(projected,rhs,len(retained),deadline=time.monotonic()+10)
    return cache,trace,basis,projection
