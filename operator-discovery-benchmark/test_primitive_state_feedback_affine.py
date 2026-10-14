from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import primitive_state_feedback_affine as P

def budget(**kw):return P.Budget(time.monotonic()+30,**kw)

def tiny_complete_inputs(kind='independent'):
    """Full declared dimensions, tiny exact source; no research input access."""
    retained,recipes=P.full15_recipes([366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957)
    cols=[{}for _ in range(1957)]
    for i,j in enumerate(retained[:779]):cols[j][i]=F(1)
    for omitted,recipe in recipes.items():
        for j,c in recipe.items():
            for i,q in cols[j].items():cols[omitted][i]=cols[omitted].get(i,F(0))+c*q
    cache={'original':dict(columns=[[[i,str(q)]for i,q in sorted(c.items())if q]for c in cols],rhs=['0']*5641,monomials=[[i]for i in range(5641)],shape=[366,613],offset=1597,specs=[['full_child',15],['full_parent',15],['storage_K',15]])}
    projection=dict(complete=True,retained_indices=retained,recipes=[[j,[[k,str(q)]for k,q in sorted(r.items())]]for j,r in sorted(recipes.items())])
    tape=dict(complete=True,coefficient_consistency='consistent',inconsistent_augmented_pivots=[],variables=1224,original_rows=5641,pivot_columns=list(range(779)),retained_indices=list(range(779)),augmented_rank=779,transcript=[dict(source_row=i,pivot_column=i,basis_index=i,steps=[],normalization='1')for i in range(779)]+[dict(source_row=i,pivot_column=None,basis_index=None,steps=[],normalization=None)for i in range(779,5641)])
    seed=dict(complete=True,candidate_original_vector=['0']*1957)
    selected=retained[800]if kind=='independent'else retained[0]
    row={selected:F(1)}
    for omitted,recipe in recipes.items():
        v=recipe.get(selected,F(0))
        if v:row[omitted]=v
    necessary=dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,entries=[dict(index=j,coefficient=str(q))for j,q in sorted(row.items())],rhs='0'if kind=='redundant'else'1')
    return cache,projection,tape,seed,necessary

class CoreTests(unittest.TestCase):
    def test_all_pivots_even_after_leading_free_and_insertion_order(self):
        chart={2:{2:F(1),3:F(2),4:F(7)},0:{0:F(1),1:F(3),2:F(5),4:F(11)}}
        result,new,r=P.reduce_feedback({0:F(2),1:F(1),2:F(20),3:F(1)},F(25),chart,4,budget())
        self.assertEqual(result,'independent');self.assertEqual(r['multipliers'],[[0,'2'],[2,'10']]);self.assertEqual(r['residual_terms'],[[1,'-5'],[3,'-19'],[4,'-67']]);self.assertEqual(new,{1:F(1),3:F(19,5),4:F(67,5)})
        augmented={**chart,1:new};x=P.back_substitute(augmented,[F(0),F(0),F(0),F(2)],4,budget());self.assertEqual(x[3],2)
        for row in augmented.values():self.assertEqual(sum(q*x[j]for j,q in row.items()if j<4),row.get(4,0))
    def test_redundant_and_contradictory_never_rhs_pivot(self):
        chart={1:{1:F(1),2:F(3)}}
        c,n,r=P.reduce_feedback({1:F(2)},F(6),chart,2,budget());self.assertEqual(c,'redundant');self.assertIsNone(n)
        c,n,r=P.reduce_feedback({1:F(2)},F(7),chart,2,budget());self.assertEqual(c,'inconsistent');self.assertIsNone(r['chosen_pivot']);self.assertEqual(r['residual_terms'],[[2,'1']])
    def test_generic_forward_backsub_and_caps(self):
        rows=[{2:F(2)},{0:F(3),2:F(4)}];rhs=[F(6),F(15)]
        tape=dict(complete=True,coefficient_consistency='consistent',inconsistent_augmented_pivots=[],variables=3,original_rows=2,pivot_columns=[2,0],retained_indices=[0,1],augmented_rank=2,transcript=[dict(source_row=0,pivot_column=2,basis_index=0,steps=[],normalization='2'),dict(source_row=1,pivot_column=0,basis_index=1,steps=[[0,'4']],normalization='3')])
        chart,_=P.replay_retained(rows,rhs,3,tape,budget());self.assertEqual(P.back_substitute(chart,[0,7,0],3,budget()),[F(1),F(7),F(3)])
        with self.assertRaises(OverflowError):P.reduce_feedback({1:F(1)},F(2),{},2,budget(max_operations=1))
        with self.assertRaises(ValueError):P.Budget(float('nan'))
        with self.assertRaises(OverflowError):budget(max_bits=8).q('1/'+str(1<<200))
        with self.assertRaises(ValueError):budget().q('1/0')
    def test_signed_pairs_and_storage_offdiagonal(self):
        retained,recipes=P.full15_recipes([366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957);x=[F(0)]*1957
        x[366]=F(2);x[367]=F(7);x[1598]=F(3);x[1718]=F(5);x[1838]=F(11)
        y=P.aggregate_seed(x,retained,recipes,budget());v=dict(zip(retained,y));self.assertEqual(v[366],-5);self.assertEqual(v[1598],14);self.assertEqual(v[1718],-39)
        lift=P.canonical_lift(y,retained,budget());self.assertEqual(lift[366:368],[F(0),F(5)]);self.assertEqual(lift[1598],0);self.assertEqual(lift[1838],14);self.assertEqual(lift[1718],17)
    def test_exact_psd_singular_cross_and_negative_witness(self):
        self.assertTrue(P.exact_psd([[F(0),F(0)],[F(0),F(2)]],budget())['psd'])
        for a in ([[F(0),F(1)],[F(1),F(100)]],[[F(1),F(2)],[F(2),F(1)]]):
            d=P.exact_psd(a,budget());self.assertFalse(d['psd']);w=list(map(F,d['witness']['vector']));value=sum(w[i]*a[i][j]*w[j]for i in range(2)for j in range(2));self.assertEqual(str(value),d['witness']['quadratic_value']);self.assertLess(value,0)
    def test_full_synthetic_chart_repair_without_hash(self):
        with patch('hashlib.sha256',side_effect=AssertionError('no hashing')):
            chart,out=P.build(*tiny_complete_inputs(),deadline=time.monotonic()+30)
        self.assertTrue(out['complete'],out.get('reason'));self.assertEqual(out['classification'],'independent');self.assertEqual(len(chart['free_indices']),444);self.assertEqual(len(chart['old_free_indices']),445);self.assertEqual(out['coefficient_rank'],780);self.assertEqual(out['augmented_rank'],780);self.assertEqual(out['free_dimension'],444);self.assertTrue(out['diagnostics']['affine_equalities_satisfied']);self.assertFalse(out['candidate_admitted'])
    def test_full_synthetic_redundant_contradiction_and_unknown(self):
        chart,out=P.build(*tiny_complete_inputs('redundant'),deadline=time.monotonic()+30);self.assertTrue(out['complete']);self.assertEqual(len(chart['free_indices']),445)
        chart,out=P.build(*tiny_complete_inputs('inconsistent'),deadline=time.monotonic()+30);self.assertTrue(out['complete']);self.assertIsNone(chart);self.assertFalse(out['chart_available']);self.assertEqual((out['coefficient_rank'],out['augmented_rank'],out['free_dimension']),(779,780,None));self.assertIsNone(out['candidate_original_vector'])
        chart,out=P.build(*tiny_complete_inputs(),deadline=time.monotonic()+30,max_operations=10);self.assertIsNone(chart);self.assertFalse(out['complete']);self.assertIsNone(out['candidate_original_vector'])
    def test_source_dependencies_and_feedback_complete_check(self):
        args=tiny_complete_inputs();args[0]['original']['columns'][367]=[[0,'1']]
        chart,out=P.build(*args,deadline=time.monotonic()+30);self.assertFalse(out['complete']);self.assertIn('omitted-column',out['reason'])
        args=tiny_complete_inputs();args[4]['entries'].append(dict(index=1837,coefficient='1'))
        chart,out=P.build(*args,deadline=time.monotonic()+30);self.assertFalse(out['complete']);self.assertIn('dependency',out['reason'])

if __name__=='__main__':unittest.main()
