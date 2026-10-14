import copy
from fractions import Fraction as F
from pathlib import Path
import time
import unittest
from unittest.mock import patch
import check_primitive_state_balanced_cone_search as C
import primitive_state_balanced_cone_search as P
from test_primitive_state_balanced_cone_search import fixture as producer_fixture


def fixture():
    mapping,mapreceipt,warmreceipt,cache,basis,projection,parent,base,warm,norms,oldproposal=producer_fixture()
    budget=C.EXACT.EXACT._Budget(None,10000000,10000000,4096);source=C.J.OLD.CACHE_CHECK.decode_original(cache,budget)
    pivots=mapping['pivots'];free=mapping['free'];basevec=list(map(F,base['final_projected_vector']));warmvec=list(map(F,warm['final_projected_vector']))
    summary=dict(normalized_basis_hash=parent['normalized_basis_hash'],rank=len(pivots),free_count=len(free),original_variables=len(source['columns']),original_rows=len(source['monomials']),projected_variables=len(basevec),retained_indices=projection['retained_indices'],pivot_columns=pivots,free_indices=free,sparse_map_entries=mapreceipt['sparse_map_entries'],parent_projected_hash=C.digest(base['final_projected_vector']),parent_free_hash=C.digest(base['final_free_vector']),parent_candidate_hash=base['candidate_hash'],base018_candidate_hash=base['candidate_hash'],base018_free_hash=C.digest(base['final_free_vector']),base_endpoint_hash=C.digest(base),warm_endpoint_hash=C.digest(warm),warm_proposal_hash=C.digest(oldproposal),warm_projected_hash=C.digest(warm['final_projected_vector']),warm_free_hash=C.digest(warm['final_free_vector']),warm_z_hash=C.digest(oldproposal['final_z_mp']),warm_candidate_hash=warm['candidate_hash'],norm_records_hash=norms['records_hash'])
    old=C.J.OLD._EndpointLicense(C.J.OLD._TOKEN,source,summary,basevec,pivots,free,{},cache=cache,basis=basis,projection=projection,parent_restoration=parent)
    jacobi=C.J._EndpointLicense(C.J._TOKEN,old,summary,basevec,{},base)
    lic=C._EndpointLicense(C._TOKEN,jacobi,summary,warmvec,[F(0)]*len(free),[F(1)]*len(free),norms,warm,oldproposal,{})
    return lic,mapping,mapreceipt,warmreceipt


def model_fixture(r=(F(6,5),F(11,10),F(1)),g=((1,0),(0,1),(-1,-1)),alpha=F(1)):
    ctx=P.OLD.context();b=P.EXACT.Budget(time.monotonic()+30,1000000)
    rr=[ctx.mpf(q.numerator)/q.denominator for q in map(F,r)];gg=[[ctx.mpf(F(q).numerator)/F(q).denominator for q in row]for row in g];a=ctx.mpf(alpha.numerator)/alpha.denominator
    direction,norm,m=P.simplex_model(ctx,rr,gg,a,b)
    budget=C.EXACT.EXACT._Budget(None,1000000,1000000,4096)
    r=[C.mp_fraction(P.OLD.mp_record(v),budget)for v in rr];g=[[C.mp_fraction(P.OLD.mp_record(v),budget)for v in row]for row in gg]
    return m,r,g,alpha


def nonzero_fixture():
    ctx=P.OLD.context();width=240;free=[0,120];pivots=[i for i in range(width)if i not in free];vector=[F(0)]*width;vector[0]=F(-1)
    normalized={p:{p:F(1)}for p in pivots};converted={p:{p:ctx.one}for p in pivots};pairs=[(a,b)for a in range(15)for b in range(a,15)]
    mapping=dict(ctx=ctx,width=width,free=free,pivots=pivots,normalized=normalized,converted=converted,resident_cells=width,initial=[F(-1),F(0)],center_mp=[-ctx.one,ctx.zero],scales=[F(1)]*2,scale_mp=[ctx.one]*2,warm_z=[ctx.zero]*2,warm_projected=vector,gram_pairs=pairs,C_indices=list(range(120)),P_indices=list(range(120,240)),scalar_indices=[],normalized_basis_hash='a'*64,base_endpoint_hash='b'*64,warm_endpoint_hash='c'*64,warm_proposal_hash='d'*64,norm_records_hash='e'*64,warm_setup_counts=dict(operations=1,peak_live_cells=1,fill_cells=0))
    summary=dict(normalized_basis_hash=mapping['normalized_basis_hash'],sparse_map_entries=len(pivots),base_endpoint_hash=mapping['base_endpoint_hash'],warm_endpoint_hash=mapping['warm_endpoint_hash'],warm_proposal_hash=mapping['warm_proposal_hash'])
    source=dict(shape=[0,0],offset=0)
    old=C.J.OLD._EndpointLicense(C.J.OLD._TOKEN,source,summary,vector,pivots,free,{})
    jacobi=C.J._EndpointLicense(C.J._TOKEN,old,summary,vector,{}, {})
    license=C._EndpointLicense(C._TOKEN,jacobi,summary,vector,[F(0)]*2,[F(1)]*2,dict(records_hash=mapping['norm_records_hash']),{}, {},{})
    return license,mapping


class BalancedIndependentTests(unittest.TestCase):
    def budget(self):return C.EXACT.EXACT._Budget(None,1000000,1000000,4096)
    def test_seven_face_interior_edge_and_degeneracy(self):
        for r,g,a in [(None,None,None),((2,1,0),((1,),(-1,),(0,)),F(1)),((1,1,1),((0,),(0,),(0,)),F(1))]:
            args=model_fixture()if r is None else model_fixture(r,g,a)
            _,_,out=C.verify_simplex_model(*args,self.budget());self.assertTrue(out['consistent']);self.assertFalse(out['model_optimality_certified'])
    def test_simplex_direction_gram_gap_and_choice_tampering(self):
        model,r,g,a=model_fixture()
        for change in ('weights','gram','direction','gap','choice','face','edge','det'):
            bad=copy.deepcopy(model)
            if change=='weights':bad['lambda_vector'][0]='-1'
            elif change=='gram':bad['gram'][0][0]=[0,'0',0]
            elif change=='direction':bad['direction'][0]=[0,'1',0]
            elif change=='gap':bad['model_gap']=[0,'1',0]
            elif change=='choice':bad['selected_candidate']=0
            elif change=='face':bad['candidates'][0]['face']=[2]
            elif change=='edge':bad['edge_data'][0]['unquantized_t']=[0,'0',0]
            else:bad['interior']['determinant_tolerance']=[0,'1',100]
            with self.assertRaises(ValueError):C.verify_simplex_model(bad,r,g,a,self.budget())
    def test_complete_zero_observed_defect_exact_endpoint(self):
        lic,mapping,m,w=fixture();proposal=P.propose(mapping,deadline=time.monotonic()+30);endpoint=P.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30)
        result=C.verify_search(lic,m,w,proposal,endpoint)
        self.assertTrue(result['endpoint_verified']);self.assertTrue(result['finite_candidate_feasible']);self.assertEqual(proposal['stop_reason'],'zero_initial_numerical_defect');self.assertFalse(result['block_gradients_certified'])
    def test_normalizers_warm_and_false_claims(self):
        lic,mapping,m,w=fixture();proposal=P.propose(mapping,deadline=time.monotonic()+30)
        for field,value in [('normalizers',['1','1','1']),('warm_endpoint_hash','0'*64),('initial_z_mp',[[0,'1',0]]*len(lic.free)),('model_optimality_certified',True),('block_gradients_certified',True)]:
            bad=copy.deepcopy(proposal);bad[field]=value
            with self.assertRaises(ValueError):C.verify_search(lic,m,w,bad)
        bad=copy.deepcopy(w);bad['new_column_responses']=1
        with self.assertRaises(ValueError):C.verify_search(lic,m,bad,proposal)
    def test_unknown_trace_and_strict_caps(self):
        lic,mapping,m,w=fixture()
        with self.assertRaises(OverflowError):P.propose(mapping,deadline=time.monotonic()+30,max_operations=1)
        with patch.object(P,'calibrate',side_effect=TimeoutError('synthetic interrupted')):
            proposal=P.propose(mapping,deadline=time.monotonic()+30)
        self.assertFalse(proposal['complete']);out=C.verify_search(lic,m,w,proposal);self.assertFalse(out['complete']);self.assertIsNone(out['finite_candidate_feasible'])
        for kw in ({'max_operations':1},{'max_trace_bytes':16777217},{'max_warm_bytes':True}):
            with self.assertRaises((ValueError,OverflowError)):C.verify_search(lic,m,w,proposal,**kw)
        with self.assertRaises(ValueError):C.load_verified_license('.',{})
    def test_nonzero_authentic_trace_and_budget_stop_tampering(self):
        lic,mapping=nonzero_fixture();proposal=P.propose(mapping,deadline=time.monotonic()+60,max_trace_bytes=100000)
        self.assertTrue(proposal['complete'],proposal.get('reason'));out=C.verify_proposal_trace(lic,proposal,max_trace_bytes=100000)
        self.assertGreater(out['accepted_iterations'],0);self.assertGreater(out['simplex_models_checked'],0)
        for key in ('initial_objective','normalizers','warm_endpoint_hash'):
            bad=copy.deepcopy(proposal)
            bad[key]=['1','1','1']if key=='normalizers'else ('0'*64 if key=='warm_endpoint_hash'else [0,'1',30])
            with self.assertRaises(ValueError):C.verify_proposal_trace(lic,bad,max_trace_bytes=100000)
        limited=proposal
        self.assertEqual(limited['stop_reason'],'budget_stop');self.assertGreater(C.verify_proposal_trace(lic,limited,max_trace_bytes=100000)['accepted_iterations'],0)
        bad=copy.deepcopy(limited);bad['budget_stop']['remaining_operations']+=1
        with self.assertRaises(ValueError):C.verify_proposal_trace(lic,bad,max_trace_bytes=100000)
    def test_controlled_reported_power_halving_and_failed_gap_prefix(self):
        # These injected numerical records exercise history checks; they do not
        # assert correctness of the reported power operator or gradients.
        lic,mapping=nonzero_fixture();metrics=P.block_metrics;calls=0
        def reject_first_report(m,x,budget,normalizers=None,apply_adjoint=True):
            nonlocal calls
            calls+=1;penalties,gradient,details=metrics(m,x,budget,normalizers,apply_adjoint=apply_adjoint)
            if calls==2:penalties=[2*b for b in normalizers]
            return penalties,gradient,details
        with patch.object(P,'block_metrics',side_effect=reject_first_report):proposal=P.propose(mapping,deadline=time.monotonic()+60,max_trace_bytes=100000)
        out=C.verify_proposal_trace(lic,proposal,max_trace_bytes=100000);self.assertTrue(proposal['complete']);self.assertGreater(len(proposal['iterations'][0]['trials']),1);self.assertGreater(out['finite_armijo_trials'],out['accepted_iterations'])
        lic,mapping=nonzero_fixture();ctx=mapping['ctx'];a=ctx.power(2,120)
        def reported_blocks(m,x,budget,normalizers=None,apply_adjoint=True):
            coords=[[ctx.zero]*m['width']for _ in range(3)]
            for row,q in zip(coords,(a,-2*a,a)):row[0]=q
            budget.charge(2*96*15**3)
            return [ctx.one]*3,coords,{}
        with patch.object(P,'block_metrics',side_effect=reported_blocks),patch.object(P,'weighted_power_operator',side_effect=lambda m,d,b,budget:list(d)):
            unknown=P.propose(mapping,deadline=time.monotonic()+60)
        self.assertFalse(unknown['complete']);self.assertEqual(unknown['iterations'][0]['trials'][0]['reason'],'fixed numerical model-gap consistency gate failed')
        result=C.verify_proposal_trace(lic,unknown);self.assertFalse(result['complete']);self.assertEqual(result['simplex_models_checked'],1)
        bad=copy.deepcopy(unknown);bad['status']='proposed';bad['complete']=True
        with self.assertRaises(ValueError):C.verify_proposal_trace(lic,bad)
    def test_authentic_failed_gap_raw_model_is_diagnostic(self):
        ctx=P.OLD.context();a=ctx.power(2,120);gradients=[[a],[-2*a],[a]]
        with self.assertRaises(P.ModelConsistencyError)as caught:P.simplex_model(ctx,[ctx.one]*3,gradients,ctx.one,P.EXACT.Budget(time.monotonic()+30,1000000))
        model=caught.exception.record;r=[F(1)]*3;g=[[F(1<<120)],[-F(1<<121)],[F(1<<120)]]
        with self.assertRaises(ValueError):C.verify_simplex_model(model,r,g,F(1),self.budget())
        _,_,out=C.verify_simplex_model(model,r,g,F(1),self.budget(),allow_inconsistent=True)
        self.assertFalse(out['consistent']);self.assertFalse(out['model_optimality_certified']);self.assertGreater(F(out['model_gap']),1)
    def test_actual020_binding_no_response_or_elimination_replay(self):
        import check_primitive_state_cone_jacobi_search_run as R
        names=set(R.INPUTS)|{C.MANIFEST,C.REPORT,*[C.PARENT+'/'+n for n in ['independent_verification.json','receipt.json','jobs/map.json','jobs/norms.json','jobs/proposal.json','jobs/endpoint.json','jobs/check.json','jobs/search-job.json']]}
        root=Path(C.__file__).resolve().parent;bindings={n:R.sha(root/n)for n in names}
        with patch.object(C.EXACT,'replay_normalized_rows',side_effect=AssertionError('no elimination')):
            lic=C.load_verified_license(root,bindings,deadline=time.monotonic()+60)
        self.assertEqual((lic.summary['rank'],lic.summary['free_count']),(779,445));self.assertEqual(lic.summary['publication'],'publication-020');self.assertGreater(max(q.numerator.bit_length()for q in lic.warm_vector),269)
        self.assertEqual([str(lic.parent_vector[i]+D*z)for i,D,z in zip(lic.free,lic.scales,lic.initial_z)],lic.warm_endpoint['final_free_vector'])
