from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import primitive_state_feedback_cone_search as P

def synthetic_inputs():
    """Declared full chart/source dimensions, made only from tiny fixture data."""
    retained,recipes=P.EXACT.full15_recipes([366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957)
    old=[j for j in range(780)if j!=148];free=list(range(780,1224));affected=[*range(780,821),*range(984,1004),*range(1104,1124)]
    normalized={p:{p:F(1)}for p in old};normalized[0][148]=F(2)
    appended={148:F(1),**{j:F(1,2)for j in affected}}
    y=[F(0)]*1224;y[979]=F(-1);y[984]=F(-1);y[1104]=F(3);y[800]=F(1)+F(1,1<<500)
    allrows={**normalized,148:appended};b=P.Budget(time.monotonic()+30);y=P.EXACT.back_substitute(allrows,y,1224,b)
    chart=dict(schema=P.EXACT.CHART_SCHEMA,width=1224,original_width=1957,classification='independent',old_rank=779,new_rank=780,retained_indices=retained,old_pivots=old,old_free_indices=sorted(free+[148]),pivot_columns=sorted(old+[148]),free_indices=free,normalized_rows=[dict(pivot=p,source_row=i,terms=[[j,str(q)]for j,q in sorted(normalized[p].items())])for i,p in enumerate(old)],appended_row=dict(pivot=148,source_row='feedback',terms=[[j,str(q)]for j,q in sorted(appended.items())]))
    affine=dict(complete=True,classification='independent',free_dimension=444,coefficient_rank=780,augmented_rank=780,chart_available=True,candidate_projected_vector=list(map(str,y)),candidate_original_vector=list(map(str,P.EXACT.canonical_lift(y,retained,b))))
    norms=dict(complete=True,status='scaled',records=[dict(index=i,free_index=j,norm='0',exponent=0,scale='1')for i,j in enumerate(sorted(free+[148]))])
    columns=[{}for _ in range(1957)]
    for i,p in enumerate(old):
        for j,q in normalized[p].items():columns[retained[j]][i]=q
    for omitted,recipe in recipes.items():
        for j,c in recipe.items():
            for i,q in columns[j].items():columns[omitted][i]=columns[omitted].get(i,F(0))+c*q
    cache=dict(original=dict(columns=[[[i,str(q)]for i,q in sorted(col.items())if q]for col in columns],rhs=['0']*5641,monomials=[[i]for i in range(5641)],shape=[366,613],offset=1597,specs=[['full_child',15],['full_parent',15],['storage_K',15]]))
    row={retained[j]:q for j,q in appended.items()}
    for omitted,recipe in recipes.items():
        q=sum(c*row.get(j,F(0))for j,c in recipe.items())
        if q:row[omitted]=q
    necessary=dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,entries=[dict(index=j,coefficient=str(q))for j,q in sorted(row.items())],rhs='0')
    return chart,affine,norms,cache,necessary

def nonzero_tiny_mapping():
    ctx=P.OLD.context();width=241;free=[0,240];pivots=list(range(1,240));rows={p:{p:F(1)}for p in pivots};rows[120][width]=F(3)
    center=[F(0)]*width;center[0]=F(-1);center[120]=F(3);center[240]=F(-1)
    m=dict(ctx=ctx,width=width,free=free,pivots=pivots,normalized=rows,converted={p:{j:ctx.mpf(q.numerator)/q.denominator for j,q in r.items()}for p,r in rows.items()},parent_projected=center,initial=[center[j]for j in free],scales=[F(1),F(1)],scale_mp=[ctx.one,ctx.one],center_mp=[ctx.mpf(-1),ctx.mpf(-1)],center_projected_mp=[ctx.mpf(q.numerator)/q.denominator for q in center],scalar_indices=[240],C_indices=list(range(120)),P_indices=list(range(120,240)),gram_pairs=[(i,j)for i in range(15)for j in range(i,15)],resident_cells=1500,calibration=dict(passed=True,tolerance='1e-40'))
    return m

class CoreTests(unittest.TestCase):
    def test_selective_support_scales_center_and_hash_denial(self):
        args=synthetic_inputs()
        with patch('hashlib.sha256',side_effect=AssertionError('no hashing')):
            mapping,receipt=P.setup(*args[:3],deadline=time.monotonic()+30)
        self.assertTrue(receipt['complete']);self.assertEqual(len(receipt['selective_scaling']['updates']),81);self.assertEqual(len(receipt['selective_scaling']['unchanged_free_indices']),363);self.assertNotIn(148,mapping['free']);self.assertFalse(receipt['column_norms_independently_verified']);self.assertTrue(receipt['calibration']['passed']);self.assertLess(len(P.encoded(receipt)),8388608)
        i=mapping['free'].index(800);self.assertNotEqual(P.OLD.record_fraction(P.OLD.mp_record(mapping['center_mp'][i])),mapping['initial'][i]);self.assertEqual(mapping['initial'][i],F(1)+F(1,1<<500))
        records={r['free_index']:r for r in receipt['selective_scaling']['updates']};self.assertEqual(records[800]['scale'],'1/2');self.assertFalse(records[800]['numerical_zero']);self.assertGreater(F(records[984]['scale']),0);self.assertEqual(mapping['scales'][mapping['free'].index(823)],1)
    def test_rhs_excluded_centered_forward_and_adjoint(self):
        m=nonzero_tiny_mapping();b=P.Budget(time.monotonic()+30);ctx=m['ctx'];d=[ctx.mpf(2),ctx.mpf(3)]
        x,diag,_=P.centered_forward(m,d,b,linear=True);self.assertEqual(x[120],0);self.assertEqual(x[0],2);self.assertIn('homogeneous delta',diag['scope'])
        x,_,_=P.centered_forward(m,d,b);self.assertEqual(x[0],1);self.assertEqual(x[120],3);self.assertEqual(x[240],2)
        g=[ctx.mpf(j%5)for j in range(241)];left=P.OLD.dot(ctx,P.centered_forward(m,d,b,linear=True)[0],g,b);right=P.OLD.dot(ctx,d,P.J.scaled_adjoint(m,g,b),b);self.assertEqual(left,right)
    def test_exact_center_plus_increment_not_269bit_reround(self):
        args=synthetic_inputs();mapping,_=P.setup(*args[:3],deadline=time.monotonic()+30);ctx=mapping['ctx'];z=[ctx.zero]*444;i=mapping['free'].index(800);z[i]=ctx.power(2,-700)
        free=[c+D*P.OLD.record_fraction(P.OLD.mp_record(v))for c,D,v in zip(mapping['initial'],mapping['scales'],z)]
        proposal=dict(schema=P.SCHEMA,complete=True,final_z_mp=[P.OLD.mp_record(v)for v in z],final_free_vector=list(map(str,free)))
        endpoint=P.exact_endpoint(mapping,proposal,args[3],args[4],deadline=time.monotonic()+30)
        self.assertTrue(endpoint['complete'],endpoint.get('reason'));self.assertEqual(F(endpoint['final_free_vector'][i]),F(1)+F(1,1<<500)+mapping['scales'][i]*F(1,1<<700));self.assertGreater(F(endpoint['final_free_vector'][i]).numerator.bit_length(),269);self.assertTrue(endpoint['diagnostics']['affine_equalities_satisfied']);self.assertFalse(endpoint['candidate_admitted'])
    def test_nonzero_trace_budget_prefix_and_no_hidden_retry(self):
        proposal=P.propose(nonzero_tiny_mapping(),deadline=time.monotonic()+30,max_trace_bytes=100000)
        self.assertTrue(proposal['complete'],proposal.get('reason'));self.assertEqual(proposal['stop_reason'],'budget_stop');self.assertEqual(proposal['search']['gradient_iterations'],128);self.assertEqual(len(proposal['power_trace']),8);self.assertGreater(len(proposal['iterations']),0);self.assertLess(len(P.encoded(proposal)),100000);self.assertFalse(proposal['model_optimality_certified'])
        self.assertTrue(all(t['model']['model_consistent']for e in proposal['iterations']for t in e['trials']if 'model'in t))
        for e in proposal['iterations']:
            if e['accepted']:
                accepted=next(t for t in e['trials']if t.get('armijo_passed'));self.assertEqual(P.OLD.record_fraction(e['next_start_step']),min(F(1<<900),2*P.OLD.record_fraction(accepted['step'])))
    def test_fixed_step_growth_and_upper_cap(self):
        ctx=P.OLD.context();b=P.Budget(time.monotonic()+30)
        self.assertEqual(P.next_start_step(ctx,ctx.mpf(3),b),6);self.assertEqual(P.next_start_step(ctx,ctx.power(2,900),b),ctx.power(2,900))
    def test_setup_caps_and_complete_partition(self):
        args=synthetic_inputs()
        with self.assertRaises(OverflowError):P.setup(*args[:3],deadline=time.monotonic()+30,max_operations=100)
        args[0]['appended_row']['terms'].pop()
        with self.assertRaises(ValueError):P.setup(*args[:3],deadline=time.monotonic()+30)
        with self.assertRaises(ValueError):P.Budget(float('nan'))
    def test_exact_endpoint_rejects_incomplete_or_changed_free_export(self):
        args=synthetic_inputs();mapping,_=P.setup(*args[:3],deadline=time.monotonic()+30)
        endpoint=P.exact_endpoint(mapping,dict(schema=P.SCHEMA,complete=False),args[3],args[4],deadline=time.monotonic()+30);self.assertFalse(endpoint['complete']);self.assertIsNone(endpoint['candidate_original_vector'])

if __name__=='__main__':unittest.main()
