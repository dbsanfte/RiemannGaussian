"""Synthetic cached charts only; no real publication map/seed/norm evaluation."""
import copy
from fractions import Fraction as F
import time
import unittest
import primitive_state_feedback_cone_search as P
import check_primitive_state_feedback_cone_search as C

def pb(**kw):return P.Budget(time.monotonic()+30,**kw)
def cb(**kw):return C.Budget(time.monotonic()+30,**kw)
def fixture():
    retained,recipes=P.EXACT.full15_recipes([366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957)
    old=[j for j in range(780)if j!=148];free=list(range(780,1224));oldfree=[148]+free
    new={148:F(1),**{j:F(1)for j in range(780,861)}}
    c=F(1)+F(1,1<<535);center=[F(0)]*1224;center[780]=c;center[148]=-c
    chart=dict(schema=P.EXACT.CHART_SCHEMA,width=1224,original_width=1957,classification='independent',old_rank=779,new_rank=780,retained_indices=retained,old_pivots=old,old_free_indices=oldfree,pivot_columns=list(range(780)),free_indices=free,normalized_rows=[dict(pivot=p,source_row=p,terms=[[p,'1']])for p in old],appended_row=dict(pivot=148,source_row='feedback',terms=[[j,str(q)]for j,q in sorted(new.items())]))
    x=P.EXACT.canonical_lift(center,retained,pb())
    affine=dict(schema='primitive-state-feedback-affine-v1',complete=True,status='complete',classification='independent',free_dimension=444,coefficient_rank=780,augmented_rank=780,chart_available=True,candidate_projected_vector=list(map(str,center)),candidate_original_vector=list(map(str,x)),preserved_free_indices=free)
    full={retained[j]:q for j,q in new.items()}
    for omitted,recipe in recipes.items():
        q=sum((v*full.get(i,F(0))for i,v in recipe.items()),F(0))
        if q:full[omitted]=q
    necessary=dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,X=7,assignment=[2*n+1 for n in range(1,28)],layout=dict(n_variables=1957),entries=[dict(index=i,coefficient=str(q))for i,q in sorted(full.items())],zero_coordinates=[i for i in range(1957)if i not in full],rhs='0')
    normalized={p:{p:F(1)}for p in old}
    kind,row,reduction=C.AFFINE.reduce_feedback([full.get(i,F(0))for i in retained],F(0),normalized,cb());affine['reduction']=reduction
    columns=[[]for _ in range(1957)]
    for p in old:columns[retained[p]]=[[p,'1']]
    for omitted,recipe in recipes.items():
        cols={}
        for j,q in recipe.items():
            for i,text in columns[j]:cols[i]=cols.get(i,F(0))+q*F(text)
        columns[omitted]=[[i,str(q)]for i,q in sorted(cols.items())if q]
    cache=dict(original=dict(shape=[366,613],offset=1597,specs=[['full_child',15],['full_parent',15],['storage_K',15]],columns=columns,rhs=['0']*5641,monomials=[[i]for i in range(5641)]))
    records=[dict(index=k,free_index=j,exponent=0,scale='1')for k,j in enumerate(oldfree)]
    norms=dict(complete=True,status='scaled',records=records)
    review=dict(schema='primitive-state-feedback-affine-independent-review-v1',all_passed=True,status='AFFINE_UPDATED',chart_verified=True,candidate_equations_verified=True,independent_affine_check=dict(verified=True,complete=True,all_original_rows_replayed=True,projection_dependencies_verified=True,feedback_reduction_verified=True,normalized_chart_verified=True,new_rank=780,new_free_count=444))
    return chart,affine,norms,cache,necessary,review,c

class Soundness(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.chart,cls.affine,cls.norms,cls.cache,cls.necessary,cls.review,cls.c=fixture()
        cls.mapping,cls.setup=P.setup(cls.chart,cls.affine,cls.norms,deadline=time.monotonic()+30)
    def test_center_is_exact_even_when_mp_rounds(self):
        m=self.mapping;ctx=m['ctx'];x,diag,free=P.centered_forward(m,[ctx.zero]*444,pb())
        self.assertEqual(m['initial'][0],self.c)
        self.assertNotEqual(P.OLD.record_fraction(P.OLD.mp_record(free[0])),self.c)
        self.assertLess(abs(P.OLD.record_fraction(P.OLD.mp_record(free[0]))-self.c),F(1,10**40))
    def test_appended_row_direction_and_no_rhs_leak(self):
        m=self.mapping;ctx=m['ctx'];z=[ctx.zero]*444;z[0]=ctx.one
        x,diag,free=P.centered_forward(m,z,pb(),linear=True)
        self.assertEqual(x[148],-x[780]);self.assertEqual(x[780],m['scale_mp'][0])
        tampered=dict(m);tampered['converted']={p:dict(row)for p,row in m['converted'].items()};tampered['converted'][148][1224]=ctx.mpf(123)
        y,_,_=P.centered_forward(tampered,z,pb(),linear=True);self.assertEqual(x,y)
    def test_scaled_forward_adjoint_pairing(self):
        m=self.mapping;ctx=m['ctx'];d=[ctx.mpf((i%3)-1)for i in range(444)];g=[ctx.mpf((i%5)-2)for i in range(1224)]
        x,_,_=P.centered_forward(m,d,pb(),linear=True);a=P.J.scaled_adjoint(m,g,pb())
        self.assertEqual(P.OLD.dot(ctx,x,g,pb()),P.OLD.dot(ctx,d,a,pb()))
    def test_selective_support_and_strict_positive_scales(self):
        s=self.setup['selective_scaling'];self.assertEqual(s['affected_free_indices'],list(range(780,861)));self.assertEqual(len(s['unchanged_free_indices']),363)
        self.assertTrue(all(q>0 for q in self.mapping['scales']));self.assertFalse(s['column_norms_independently_verified'])
    def test_missing_appended_row_rejected(self):
        chart=copy.deepcopy(self.chart);chart['appended_row']['terms']=[]
        with self.assertRaises(ValueError):P.decode_chart(chart,self.affine,pb())
    def test_wrong_scale_coordinate_or_zero_rejected(self):
        for mutate in ('coordinate','zero'):
            norms=copy.deepcopy(self.norms)
            if mutate=='coordinate':norms['records'][0]['free_index']=780
            else:norms['records'][0]['scale']='0'
            with self.assertRaises(ValueError):P.reused_scales(norms,list(range(780,1224)),pb())
    def test_exact_endpoint_sum_exceeds_mp_precision(self):
        m=self.mapping;ctx=m['ctx'];z=[ctx.zero]*444;z[0]=ctx.power(2,-269)
        exact=self.c+m['scales'][0]*F(1,1<<269);free=list(m['initial']);free[0]=exact
        proposal=dict(schema=P.SCHEMA,complete=True,final_z_mp=[P.OLD.mp_record(v)for v in z],final_free_vector=list(map(str,free)))
        endpoint=P.exact_endpoint(m,proposal,self.cache,self.necessary,deadline=time.monotonic()+30)
        self.assertTrue(endpoint['complete']);self.assertEqual(F(endpoint['final_free_vector'][0]),exact)
        self.assertGreater(exact.numerator.bit_length(),269)
        self.assertEqual(F(endpoint['candidate_original_vector'][148]),-exact)
        self.assertEqual(endpoint['diagnostics']['new_equation_residual'],'0')
    def test_frobenius_offdiagonal_gradient(self):
        m=self.mapping;ctx=m['ctx'];x=[ctx.zero]*1224
        ci=m['C_indices'][1];pi=m['P_indices'][1];x[ci]=-ctx.one;x[pi]=4*ctx.one
        penalties,gradients,details=P.block_metrics(m,x,pb(),[ctx.one]*3,apply_adjoint=False)
        self.assertAlmostEqual(float(penalties[1]),0.5,places=12)
        self.assertAlmostEqual(float(gradients[1][ci]),-1.0,places=12)
        self.assertAlmostEqual(float(penalties[2]),0.0,places=12)
    def test_storage_H_gradient_contains_four_C_terms(self):
        m=self.mapping;ctx=m['ctx'];x=[ctx.zero]*1224
        ci=m['C_indices'][1];pi=m['P_indices'][1];x[pi]=-ctx.one
        penalties,gradients,details=P.block_metrics(m,x,pb(),[ctx.one]*3,apply_adjoint=False)
        self.assertAlmostEqual(float(penalties[2]),0.5,places=12)
        self.assertAlmostEqual(float(gradients[2][ci]),-4.0,places=12)
        self.assertAlmostEqual(float(gradients[2][pi]),-1.0,places=12)
    def test_fixed_step_expansion_and_cap(self):
        ctx=self.mapping['ctx']
        self.assertEqual(P.next_start_step(ctx,ctx.mpf('0.25'),pb()),ctx.mpf('0.5'))
        self.assertEqual(P.next_start_step(ctx,ctx.power(2,900),pb()),ctx.power(2,900))
        with self.assertRaises(ValueError):P.next_start_step(ctx,ctx.zero,pb())
    def test_accepted_step_expansion_in_tiny_real_trace(self):
        ctx=self.mapping['ctx']
        m=dict(ctx=ctx,width=1,free=[0],pivots=[],normalized={},converted={},initial=[F(-1)],parent_projected=[F(-1)],scales=[F(1)],scale_mp=[ctx.one],center_mp=[-ctx.one],center_projected_mp=[-ctx.one],scalar_indices=[0],C_indices=[],P_indices=[],gram_pairs=[],resident_cells=1,calibration={})
        proposal=P.propose(m,deadline=time.monotonic()+30,max_operations=4000000,max_trace_bytes=131072)
        self.assertTrue(proposal['complete'])
        accepted=proposal['iterations'][0];first=accepted['trials'][0]
        self.assertTrue(accepted['accepted'])
        expected=min(F(1<<900),2*P.OLD.record_fraction(first['step']))
        self.assertEqual(P.OLD.record_fraction(accepted['next_start_step']),expected)
        self.assertEqual(P.OLD.record_fraction(proposal['iterations'][1]['trials'][0]['step']),expected)
    def test_independent_checker_rejects_changed_appended_row(self):
        license=C.validate_chart(self.cache,self.chart,self.affine,self.necessary,self.review,cb())
        self.assertEqual(len(license.free),444);self.assertEqual(len(license.affected),81)
        chart=copy.deepcopy(self.chart);chart['appended_row']['terms'][-1][1]='2'
        with self.assertRaises(ValueError):C.validate_chart(self.cache,chart,self.affine,self.necessary,self.review,cb())
    def test_selective_norms_cannot_be_promoted_to_proof(self):
        license=C.validate_chart(self.cache,self.chart,self.affine,self.necessary,self.review,cb())
        C.verify_setup(license,self.norms,self.setup,cb())
        setup=copy.deepcopy(self.setup);setup['selective_scaling']['column_norms_independently_verified']=True
        with self.assertRaises(ValueError):C.verify_setup(license,self.norms,setup,cb())
    def test_reused_scales_follow_coordinate_not_record_position(self):
        norms=copy.deepcopy(self.norms)
        for index,record in enumerate(norms['records']):
            k=index%3;record['exponent']=k;record['scale']=str(F(1,1<<k))
        scales,records=P.reused_scales(norms,list(range(780,1224)),pb())
        self.assertEqual(scales[0],F(1,2))
        self.assertEqual(records[0]['free_index'],780)
        self.assertEqual(records[0]['index'],1)
    def test_setup_cap_has_no_partial_result(self):
        with self.assertRaises(OverflowError):P.setup(self.chart,self.affine,self.norms,deadline=time.monotonic()+30,max_operations=1000)
if __name__=='__main__':unittest.main()
