import copy
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import check_primitive_state_augmented_cone_search as C
import primitive_state_augmented_cone_search as P
from test_check_primitive_state_feedback_cone_search import licensed_inputs
from test_primitive_state_augmented_cone_search import tiny_mapping


def complete_inputs():
    cache,chart,affine,oldrow,norms,review024=licensed_inputs();b=C.Budget(time.monotonic()+30)
    retained,recipes=C.AFFINE.projection_layout(cache['original'])
    old={r['pivot']:{j:F(q)for j,q in r['terms']}for r in chart['normalized_rows']}
    for p,q in((160,780),(170,781)):old[q]=old.pop(p);old[q]={q:F(1)}
    chart['normalized_rows']=[dict(pivot=p,source_row=i,terms=[[j,str(q)]for j,q in sorted(row.items())])for i,(p,row)in enumerate(sorted(old.items()))]
    chart['old_pivots']=sorted(old);chart['old_free_indices']=[i for i in range(1224)if i not in old]
    oldappend={j:F(q)for j,q in chart['appended_row']['terms']};oldappend.pop(780);oldappend.pop(781);oldappend[160]=oldappend[170]=F(1,2)
    chart['appended_row']['terms']=[[j,str(q)]for j,q in sorted(oldappend.items())]
    rowfull={retained[j]:q for j,q in oldappend.items()}
    for omitted,recipe in recipes.items():
        q=sum(c*rowfull.get(j,F(0))for j,c in recipe.items())
        if q:rowfull[omitted]=q
    oldrow.update(entries=[dict(index=j,coefficient=str(q))for j,q in sorted(rowfull.items())],zero_coordinates=[j for j in range(1957)if j not in rowfull])
    allrows=dict(old);allrows[148]=oldappend
    chart['pivot_columns']=sorted(allrows);chart['free_indices']=[i for i in range(1224)if i not in allrows]
    seed=[F(q)for q in affine['candidate_projected_vector']];seed[780]=seed[781]=0
    y=C.AFFINE.backsubstitute(allrows,seed,b);x=C.AFFINE.lift(y,retained,b)
    _,pr,rhs=C.AFFINE.decode_feedback(oldrow,retained,recipes,b);_,_,red=C.AFFINE.reduce_feedback(pr,rhs,old,b)
    affine.update(candidate_projected_vector=list(map(str,y)),candidate_original_vector=list(map(str,x)),preserved_free_indices=chart['free_indices'],reduction=red)
    # Synthetic source contains every licensed old normalized row, repeated to5641.
    columns=[{}for _ in range(1957)]
    oldlist=list(old.values())
    for i in range(5641):
        for j,q in oldlist[i%779].items():columns[retained[j]][i]=q
    for omitted,recipe in recipes.items():
        for j,q in recipe.items():
            for i,v in columns[j].items():columns[omitted][i]=columns[omitted].get(i,F(0))+q*v
    cache['original']['columns']=[[[i,str(q)]for i,q in sorted(row.items())if q]for row in columns]
    constraints=[];rows=dict(allrows);reductions=[];appended=[]
    for index,p in enumerate((160,170)):
        projected={p:F(1),**{i:F(index+1,4)for i in range(800,898)},1224:F(index+7)}
        if index==0:projected[170]=F(2)
        full={retained[j]:q for j,q in projected.items()if j<1224}
        for omitted,recipe in recipes.items():
            v=sum(q*full.get(j,F(0))for j,q in recipe.items())
            if v:full[omitted]=v
        constraint=dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,X=9,assignment=[2*n+1 for n in range(1,36)]if index==0 else[(-1)**n*(n*n+1)for n in range(1,36)],layout=dict(n_variables=1957),entries=[dict(index=j,coefficient=str(q))for j,q in sorted(full.items())],zero_coordinates=[j for j in range(1957)if j not in full],rhs=str(projected[1224]))
        constraints.append(constraint);_,_,rec=C.reduce_constraint(constraint,rows,retained,recipes,index,b);reductions.append(rec);appended.append(dict(source_case=index,**rec['normalized_row']))
    extension=dict(complete=True,old_rank=780,coefficient_rank=782,augmented_rank=782,free_count=442,reductions=reductions,appended_rows=appended,contradiction_row=None,old_tape_replayed=False,formal_family_only=True)
    review027=dict(schema='primitive-state-fresh-identity-probe-independent-review-v1',all_passed=True,affine_extension=extension,necessary_formal_identity_constraints=constraints)
    report027=dict(schema=27,independent_audit_complete=True)
    recovered=dict(complete=True,final_projected_vector=list(map(str,y)),candidate_original_vector=list(map(str,x)))
    recovery=dict(all_passed=True,endpoint_verified=True,candidate_equations_verified=True,status='RECOVERED_SCALAR_REJECTED')
    prior=dict(schema='primitive-state-backtracking-cone-map-v1',complete=True,free_indices=chart['free_indices'],scale_vector=['1']*444,normalizers=['17','19','23'])
    return [cache,chart,affine,oldrow,review024,extension,constraints,review027,report027,recovered,recovery,prior]


def tiny_license(mapping,mapreceipt):
    license=C.CACHED._License();license.free=mapping['free'];license.parent_vector=mapping['parent_projected'];license.scales=mapping['scales'];license.pivots=mapping['pivots'];license.source=dict(shape=[0,0],offset=1);license.summary=dict(sparse_map_entries=sum(map(len,mapping['normalized'].values())));license.initial_z=[F(0)]*len(license.free);license.normalizers=mapping['fixed_normalizers'];license.setup=dict(calibration=mapreceipt['calibration']);return license

class Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.args=complete_inputs();a=cls.args
        cls.mapping,cls.map,cls.chart,cls.center=P.setup(a[1],a[2],a[5],a[9],a[11],deadline=time.monotonic()+30)
        cls.tiny=tiny_mapping();cls.tiny['calibration']['center_exact_reference_relative_error']='0';cls.proposal=P.propose(cls.tiny,deadline=time.monotonic()+30,max_trace_bytes=100000)
    def license(self):return C.augmented_license(*self.args,C.Budget(time.monotonic()+30))
    def test_complete_chart_repair_scales_and_no_hash(self):
        b=C.Budget(time.monotonic()+30)
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')):
            license=C.augmented_license(*self.args,b);r=C.verify_composed_artifacts(license,self.chart,self.center,b);s=C.verify_setup(license,self.map,b)
        self.assertTrue(r['verified']);self.assertEqual(len(license.rows),782);self.assertEqual(len(license.free),442);self.assertEqual(s['affected_coordinates'],98);self.assertFalse(s['column_norms_independently_verified'])
        self.assertEqual(license.parent_vector[800],F(1)+F(1,1<<500))
    def test_changed_delta_center_and_inherited_D_rejected(self):
        a=copy.deepcopy(self.args);a[5]['appended_rows'][0]['terms'][0][1]='2'
        with self.assertRaises(ValueError):C.augmented_license(*a,C.Budget(time.monotonic()+30))
        a=copy.deepcopy(self.args);a[11]['scale_vector'].append('1')
        with self.assertRaises(ValueError):C.augmented_license(*a,C.Budget(time.monotonic()+30))
        bad=copy.deepcopy(self.center);bad['initial_free_vector'][0]='3'
        with self.assertRaises(ValueError):C.verify_composed_artifacts(self.license(),self.chart,bad,C.Budget(time.monotonic()+30))
    def test_exact_endpoint_no_center_reround_and_scalar_first(self):
        m=self.mapping;z=[m['ctx'].zero]*442;z[m['free'].index(800)]=m['ctx'].power(2,-700)
        free=[c+D*P.OLD.record_fraction(P.OLD.mp_record(v))for c,D,v in zip(m['initial'],m['scales'],z)]
        proposal=dict(schema=P.SCHEMA,complete=True,final_z_mp=[P.OLD.mp_record(v)for v in z],final_free_vector=list(map(str,free)))
        endpoint=P.exact_endpoint(m,proposal,self.args[0],[self.args[3],*self.args[6]],deadline=time.monotonic()+30)
        self.assertTrue(endpoint['complete'],endpoint.get('reason'));b=C.Budget(time.monotonic()+30);license=self.license();C.verify_setup(license,self.map,b);full,rhs=C.original_system(license,b)
        result=C.verify_endpoint(license,proposal,endpoint,full,rhs,b);self.assertEqual(result['full_equations_checked'],5644);self.assertEqual(result['PSD_blocks_checked'],0);self.assertGreater(F(endpoint['final_free_vector'][m['free'].index(800)]).numerator.bit_length(),269)
        bad=copy.deepcopy(endpoint);bad['final_free_vector'][0]='99'
        with self.assertRaises(ValueError):C.verify_endpoint(license,proposal,bad,full,rhs,b)
    def test_authentic_nonzero_power_history_and_carry_tamper(self):
        p=self.proposal;license=tiny_license(self.tiny,p);r=C.verify_proposal_trace(license,p,C.Budget(time.monotonic()+30),max_trace_bytes=100000);self.assertGreater(r['accepted_iterations'],0);self.assertEqual(r['power_iterations'],8)
        bad=copy.deepcopy(p);bad['power_trace'][0]['vector'][1][0]=0
        with self.assertRaises(ValueError):C.verify_proposal_trace(license,bad,C.Budget(time.monotonic()+30),max_trace_bytes=100000)
        bad=copy.deepcopy(p);bad['iterations'][0]['next_start_step']=[0,'1',0]
        with self.assertRaises(ValueError):C.verify_proposal_trace(license,bad,C.Budget(time.monotonic()+30),max_trace_bytes=100000)
    def test_zero_power_operator_and_twelve_trial_policy(self):
        m=tiny_mapping();m['calibration']['center_exact_reference_relative_error']='0'
        with patch.object(P.B,'weighted_power_operator',side_effect=lambda mapping,d,normalizers,b:[mapping['ctx'].zero]*len(d)):
            p=P.propose(m,deadline=time.monotonic()+30,max_trace_bytes=20000)
        self.assertTrue(p['complete'],p.get('reason'));self.assertEqual(len(p['power_trace']),1)
        r=C.verify_proposal_trace(tiny_license(m,p),p,C.Budget(time.monotonic()+30),max_trace_bytes=20000);self.assertTrue(r['complete'])
    def test_generic_missing_pivot_and_scalar_gate(self):
        b=C.Budget(time.monotonic()+30)
        with self.assertRaises(ValueError):C.compose_chart([dict(pivot=1,terms=[[1,'1']])],[dict(pivot=2,terms=[[1,'3'],[2,'1']])],4,b)
        x=[F(0)]*1957;x[3]=F(-1)
        with patch.object(C.AFFINE,'exact_psd',side_effect=AssertionError('must skip')):r=C.scalar_first_endpoint([{}]*5641,[F(0)]*5641,[[F(0)]*1957 for _ in range(3)],[F(0)]*3,x,b)
        self.assertEqual(r['negative_scalar_count'],1);self.assertIsNone(r['PSD_failures'])
        with self.assertRaises(ValueError):C.scalar_first_endpoint([{}]*5641,[F(0)]*5641,[[F(0)]for _ in range(3)],[F(0)]*3,x,b)

if __name__=='__main__':unittest.main()
