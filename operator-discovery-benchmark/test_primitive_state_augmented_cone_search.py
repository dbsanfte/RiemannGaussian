from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import primitive_state_augmented_cone_search as P
from test_primitive_state_feedback_cone_search import synthetic_inputs,nonzero_tiny_mapping

def augmented_inputs():
    chart,affine,norms,cache,row=synthetic_inputs()
    oldfree=chart['free_indices'];prior=dict(schema='primitive-state-backtracking-cone-map-v1',complete=True,free_indices=oldfree,scale_vector=['1']*444,normalizers=['17','19','23'])
    appended=[dict(pivot=780,source_case=0,terms=[[780,'1'],[781,'2'],[800,'3'],[1224,'7']]),dict(pivot=781,source_case=1,terms=[[781,'1'],[801,'4'],[1224,'11']])]
    extension=dict(complete=True,contradiction_row=None,old_rank=780,coefficient_rank=782,augmented_rank=782,free_count=442,appended_rows=appended)
    recovered=dict(complete=True,final_projected_vector=affine['candidate_projected_vector'],candidate_original_vector=affine['candidate_original_vector'])
    retained,recipes=P.EXACT.full15_recipes([366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957)
    rows=[row]
    for record in appended:
        projected={j:F(q)for j,q in record['terms']};full={retained[j]:q for j,q in projected.items()if j<1224}
        for omitted,recipe in recipes.items():
            q=sum(c*full.get(j,F(0))for j,c in recipe.items())
            if q:full[omitted]=q
        rows.append(dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,entries=[dict(index=j,coefficient=str(q))for j,q in sorted(full.items())],rhs=str(projected[1224])))
    return chart,affine,extension,recovered,prior,cache,rows

def tiny_mapping():
    m=nonzero_tiny_mapping();ctx=m['ctx'];z=[ctx.zero]*len(m['free']);x,_,_=P.centered_forward(m,z,P.Budget(time.monotonic()+30));m.update(warm_z=z,warm_forward_mp=x,warm_free=list(m['initial']),fixed_normalizers=[F(17),F(19),F(23)]);return m

class CoreTests(unittest.TestCase):
    def test_generic_coupled_chart_and_preserved_free(self):
        b=P.Budget(time.monotonic()+30)
        rows,pivots,free,affected=P.compose_chart([dict(pivot=0,terms=[[0,'1'],[2,'3']])],[dict(pivot=1,terms=[[1,'1'],[2,'2']]),dict(pivot=2,terms=[[2,'1'],[3,'4'],[4,'7']])],4,b)
        self.assertEqual(affected,[3]);seed=[F(0),F(0),F(0),F(5)];out=P.EXACT.back_substitute(rows,seed,4,b);self.assertEqual(out,[F(39),F(26),F(-13),F(5)])
        with self.assertRaises(ValueError):P.compose_chart([], [dict(pivot=1,terms=[[1,'1']]),dict(pivot=2,terms=[[1,'2'],[2,'1']])],4,b)
    def test_setup_and_exact_high_bit_center_endpoint(self):
        args=augmented_inputs()
        with patch('hashlib.sha256',side_effect=AssertionError('no hashing')):m,receipt,chart,center=P.setup(*args[:5],deadline=time.monotonic()+30)
        self.assertEqual(len(chart['normalized_rows']),782);self.assertEqual(len(m['free']),442);self.assertTrue(receipt['calibration']['passed']);self.assertEqual(receipt['normalizers'],['17','19','23']);self.assertEqual(receipt['selective_scaling']['affected_free_indices'],[800,801]);self.assertEqual(m['parent_projected'][800],F(1)+F(1,1<<500))
        z=[m['ctx'].zero]*442;z[m['free'].index(800)]=m['ctx'].power(2,-700);free=[c+D*P.OLD.record_fraction(P.OLD.mp_record(v))for c,D,v in zip(m['initial'],m['scales'],z)]
        proposal=dict(schema=P.SCHEMA,complete=True,final_z_mp=[P.OLD.mp_record(v)for v in z],final_free_vector=list(map(str,free)));end=P.exact_endpoint(m,proposal,args[5],args[6],deadline=time.monotonic()+30)
        self.assertTrue(end['complete'],end.get('reason'));self.assertTrue(end['diagnostics']['affine_equalities_satisfied']);self.assertEqual(end['diagnostics']['full_equations_checked'],5644);self.assertGreater(F(end['final_free_vector'][m['free'].index(800)]).numerator.bit_length(),269)
    def test_scalar_first_policy(self):
        b=P.Budget(time.monotonic()+30);x=[F(0)]*1957;x[4]=F(-1)
        with patch.object(P.EXACT,'exact_psd',side_effect=AssertionError('skip after scalar rejection')):d=P.scalar_first_diagnostics([{}]*1957,[F(0)],x,[],b)
        self.assertEqual(d['negative_scalar_count'],1);self.assertEqual(d['PSD_blocks_checked'],0);self.assertIsNone(d['PSD_failures']);self.assertEqual(d['psd_status'],'NOT_CHECKED_AFTER_SCALAR_REJECTION')
        x[4]=F(0);d=P.scalar_first_diagnostics([{}]*1957,[F(0)],x,[],b);self.assertEqual(d['PSD_blocks_checked'],3);self.assertEqual(d['psd_status'],'ALL_THREE_EXACT_BLOCKS_CHECKED')
    def test_power_and_budget_prefix(self):
        proposal=P.propose(tiny_mapping(),deadline=time.monotonic()+30,max_trace_bytes=100000)
        self.assertTrue(proposal['complete'],proposal.get('reason'));self.assertEqual(len(proposal['power_trace']),8);self.assertEqual(proposal['search']['armijo_trials'],12);self.assertEqual(proposal['stop_reason'],'budget_stop');self.assertEqual(proposal['initial_z_mp'],[[0,'0',0]]*2);self.assertFalse(proposal['candidate_admitted'])
    def test_caps_and_inherited_scale_partition(self):
        args=augmented_inputs();args[4]['scale_vector'].append('1')
        with self.assertRaises(ValueError):P.setup(*args[:5],deadline=time.monotonic()+30)
        with self.assertRaises(ValueError):P.Budget(float('nan'))
        with self.assertRaises(OverflowError):P.setup(*augmented_inputs()[:5],deadline=time.monotonic()+30,max_operations=20)

if __name__=='__main__':unittest.main()
