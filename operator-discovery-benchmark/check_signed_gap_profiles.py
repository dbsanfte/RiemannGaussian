#!/usr/bin/env python3
"""Independent prime arithmetic, exact fits, anonymous estimates and replay."""
import argparse,subprocess,sys,tempfile
from pathlib import Path
from fractions import Fraction as Q
from math import factorial,lcm
from itertools import combinations
from functools import lru_cache
from stable_scale_report import BASE,read,sha,digest
from check_signed_control import independent_inverse
from check_divisor_dual import ceiling
from check_mellin_kernels import put


@lru_cache(maxsize=8192)
def ceilq(n,p):return ceiling(n,Q(p))


def den(p,q):
    if p['kind']=='power':return ceilq(q,p['power'])
    if p['kind']=='factorial':return factorial(q)
    if p['kind']=='exponential':return 2**ceilq(q,p['power'])
    return None


def const(law,q,d):
    k=law['kind']
    if k=='constant':return 1
    if k=='power':return 1+ceilq(q,law['power'])
    if k=='factorial':return factorial(q)
    if k=='exponential':return 2**ceilq(q,law['power'])
    if k=='denominator_power':return ceilq(d,law['power'])
    return None


def eps(p,q):return Q(p['epsilon']) if p['kind']=='fixed' else Q(1,den(p,q))


def parameters(p,X,q):
    e=eps(p['exponent_schedule'],q);law=p['constant_law']
    if law['kind']=='free_per_level':
        if str(q)not in p['fitted_constants']:return {'missing':True,'reason':'unobserved_level_constant_is_not_fitted','no_new_level_fit_counted_as_prediction':True}
        C=Q(p['fitted_constants'][str(q)])
    else:C=Q(p['fitted_coefficient'])*const(law,q,den(p['exponent_schedule'],q))
    root=ceilq(X,e);log=ceilq(X.bit_length(),p['log_power']);D=C*X*root*log
    return {'missing':False,'epsilon':str(e),'C':str(C),'root_ceiling':root,'log_ceiling':log,'D':str(D),'charged_defect_bound':str(4*X*D),'ordinary_energy_power':str(2+e),'log_power':p['log_power'],'scale_independent_constant':True}


def data(values,scales):
    M=[0];E=[0];Qn=[0]
    for n in range(1,len(values)):
        M.append(M[-1]+values[n]);E.append(E[-1]+M[-2]**2);Qn.append(Qn[-1]+values[n]**2)
    return [{'X':X,'energy':E[2*X]-E[X],'child_energy':E[4*X]-E[2*X],'signed_defect':E[4*X]-5*E[2*X]+4*E[X],'squarefree_count_through_4X':Qn[4*X]} for X in scales]


def audit_data(row,scales,counts):
    mu,_=independent_inverse(row['cutoff']);assert row['cutoff']==4*max(scales) and row['complete_inverse_sha256']==digest(mu) and row['rows']==data(mu,scales) and not row['producer_prime_or_factor_oracle_used'] and row['whole_signed_defect_retained'];counts['independent_actual_prime_inverse_coefficients']+=row['cutoff'];return mu


def generic(X):return sum_range_square(2*X,4*X)
def sum_range_square(L,U):return (U-1)*U*(2*U-1)//6-(L-1)*L*(2*L-1)//6


def audit_observations(p,source,levels,rows,counts):
    expected=[]
    for r in source['rows']:
        X=r['X'];Qn=r['squarefree_count_through_4X'];delta=r['signed_defect']
        for q in levels:
            pars=parameters(p,X,q);entry={'X':X,'level':q,'parameters':pars,'actual_signed_defect':delta,'Q_4X':Qn}
            if not pars['missing']:
                D=Q(pars['D']);entry.update({'exact_signed_nullspace_gap':str(D*Qn-delta),'exact_half_gap_margin':str(D*Qn/2-delta),'finite_half_gap_pass':D*Qn/2>=delta,
                    'positive_defect_requirement':str(Q(2*max(delta,0),X*pars['root_ceiling']*pars['log_ceiling']*Qn)),'charged_bound_over_generic':str(Q(pars['charged_defect_bound'])/generic(X)),
                    'global_signed_bound_proved':False,'finite_test_is_not_all_scale_certificate':True});counts['exact_signed_gap_observations']+=1
            else:counts['unseen_level_constants_retained_as_missing']+=1
            expected.append(entry)
    assert rows==expected


def fit(template,source,levels):
    p=dict(template);ratios={}
    for q in levels:
        e=eps(p['exponent_schedule'],q);items=[Q(2*max(r['signed_defect'],0),r['X']*ceilq(r['X'],e)*ceilq(r['X'].bit_length(),p['log_power'])*r['squarefree_count_through_4X']) for r in source['rows']];ratios[q]=max(items)
    if p['constant_law']['kind']=='free_per_level':p['fitted_constants']={str(q):str(Q(5,4)*ratios[q]+Q(1,2**64)) for q in levels}
    else:p['fitted_coefficient']=str(Q(5,4)*max(ratios[q]/const(p['constant_law'],q,den(p['exponent_schedule'],q)) for q in levels)+Q(1,2**64))
    return p


def minimums(dimensions):
    out=[]
    for m in dimensions:
        best={}
        for bits in range(1<<m):
            J=bits.bit_count();loss=sum((bits&((1<<t)-1)).bit_count()**2 for t in range(m));item=(loss,bits)
            if J not in best or item<best[J]:best[J]=item
        out.extend({'dimension':m,'mass':J,'anonymous_response':v[0],'minimizer_bits':v[1]} for J,v in sorted(best.items()))
    return out


def solve(A,b):
    n=len(b);T=[list(map(Q,row))+[Q(v)] for row,v in zip(A,b)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if T[i][j]),None)
        if pivot is None:return None
        T[j],T[pivot]=T[pivot],T[j];s=T[j][j];T[j]=[v/s for v in T[j]]
        for i in range(n):
            if i!=j:
                s=T[i][j];T[i]=[a-s*b for a,b in zip(T[i],T[j])]
    return [r[-1] for r in T]


def inference(rows,monomials,budget):
    cols=[[Q(r['mass']**i*r['dimension']**j) for i,j in monomials] for r in rows];y=[Q(r['anonymous_response']) for r in rows];fits=[]
    for size in range(1,budget+1):
        for support in combinations(range(len(monomials)),size):
            A=[[r[k] for k in support] for r in cols];G=[[sum(r[i]*r[j] for r in A) for j in range(size)] for i in range(size)];rhs=[sum(r[i]*v for r,v in zip(A,y)) for i in range(size)];z=solve(G,rhs)
            if z is None or any(not v for v in z):continue
            error=sum((v-sum(a*c for a,c in zip(r,z)))**2 for r,v in zip(A,y));fits.append({'terms':[[*monomials[k],str(c)] for k,c in zip(support,z)],'exact_squared_residual':str(error),'support_size':size,'expected_formula_supplied':False})
    return sorted(fits,key=lambda r:(Q(r['exact_squared_residual']),r['support_size'],len(str(r['terms'])),digest(r['terms'])))


def score(rows):
    valid=[r for r in rows if not r['parameters']['missing']];return {'finite_passes':sum(r['finite_half_gap_pass'] for r in valid),'finite_cases':len(valid),'missing_cases':len(rows)-len(valid),'max_charged_bound_over_generic':str(max((Q(r['charged_bound_over_generic']) for r in valid),default=Q(10**100))),'global_signed_bound_proved':False}


def key(p,score):return (-score['finite_passes'],Q(score['max_charged_bound_over_generic']),len(str(p['program'])),p['id'])


def check(d):
    spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');val=read(d/'validation.json');arc=read(d/'archive.json');queue=read(d/'proof_queue.json');seal=read(d/'seal.json');cases=read(d/'final_cases.json');final=read(d/'final_evaluation.json');checks={};counts={'independent_actual_prime_inverse_coefficients':0,'exact_signed_gap_observations':0,'unseen_level_constants_retained_as_missing':0}
    def passed(n):checks[n]=True;print('Verified',n,flush=True)
    from divisor_dual_report import summary as parent
    from divisor_dual_analytic_report import summary as analytic
    parent(spec['source_run']);analytic(spec['source_analytical_review'])
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/n)==h
    for n,h in spec['source_analytical_sha256'].items():assert sha(Path(spec['source_analytical_review'])/n)==h
    for n,h in seal['files'].items():assert sha(d/n)==h
    assert digest(spec)==seal['protocol_sha256']==batch['protocol_sha256']==queue['protocol_sha256']==final['protocol_sha256'] and all(batch['access_denials'].values()) and seal['selection_closed'] and not seal['final_cases_exist'] and cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json') and final['cases_sha256']==digest(cases)
    assert not set(cases['scales'])&set(spec['training_scales']+spec['validation_scales']) and not set(cases['new_levels'])&set(spec['training_levels']+spec['final_cases']['excluded_earlier_final_levels'])
    for f in spec['retained_failed_runs_are_development']:
        p=Path(f['run_directory']);assert sha(p/'failure.json')==f['failure_sha256']
        for n,h in f['files_sha256'].items():assert sha(p/n)==h
        assert not set(cases['scales'])&set(f['excluded_final_scales'])
    passed('frozen_sources_independent_prior_proof_feedback_isolated_worker_and_fresh_final')
    audit_data(batch['training_arithmetic'],spec['training_scales'],counts);audit_data(val['arithmetic'],spec['validation_scales'],counts);mu=audit_data(final['arithmetic'],cases['scales'],counts)
    passed('complete_independent_prime_arithmetic_and_exact_whole_signed_energy_at_all_splits')
    programs=batch['programs'];ids={r['id']:r for r in programs};assert len(ids)==len(programs)==len(spec['exponent_schedules'])*len(spec['constant_laws'])*len(spec['log_powers'])
    templates={digest({'exponent_schedule':s,'constant_law':c,'log_power':L,'arithmetic_model':'inverse_one'}) for s in spec['exponent_schedules'] for c in spec['constant_laws'] for L in spec['log_powers']};seen=set()
    for row in programs:
        p=row['program'];template={k:p[k] for k in ['exponent_schedule','constant_law','log_power','arithmetic_model']};seen.add(digest(template));assert p==fit(template,batch['training_arithmetic'],spec['training_levels']) and row['id']==digest(p);audit_observations(p,batch['training_arithmetic'],spec['training_levels'],row['training_observations'],counts)
    assert seen==templates
    byval={r['program_id']:r for r in val['program_results']};assert set(byval)==set(ids)
    for row in val['program_results']:audit_observations(ids[row['program_id']]['program'],val['arithmetic'],spec['validation_levels'],row['observations'],counts);assert row['score']==score(row['observations'])
    passed('every_exact_training_constant_fractional_profile_and_validation_signed_gap')
    for lead in arc['leads']:
        eligible=[p for p in programs if p['program']['exponent_schedule']==lead['exponent_schedule'] and p['program']['constant_law']['kind']==lead['constant_family']];chosen=min(eligible,key=lambda r:key(r,byval[r['id']]['score']));assert lead['program_id']==chosen['id'] and lead['score']==byval[chosen['id']]['score']
    selected={r['program_id'] for r in arc['leads']};assert len(arc['leads'])==len(spec['exponent_schedules'])*len({p['kind'] for p in spec['constant_laws']}) and selected=={r['program_id'] for r in queue['queue']} and queue['candidate_ids_frozen_before_final'] and not queue['final_data_used_for_selection']
    for row in queue['queue']:assert row['exact_program']==ids[row['program_id']]['program'] and row['validation_evidence']==byval[row['program_id']]['score'] and not row['global_bound_proved'] and not row['formula_changed_after_detection'] and row['new_level_constants_are_unknown']==(row['exact_program']['constant_law']['kind']=='free_per_level')
    passed('complete_diverse_archive_and_exact_candidate_proof_queue_frozen_before_final')
    responses=minimums(spec['anonymous_minimum_response_dimensions']);assert responses==batch['anonymous_minimum_responses'];fits=inference(responses,spec['minimum_feature_dictionary'],spec['minimum_sparse_support_budget']);f=batch['minimum_inference'];assert f['retained_fits']==fits and f['selected']==fits[0]==arc['minimum_lead']==queue['minimum_lead'] and not f['global_minimum_bound_proved']
    expected=minimums(cases['minimum_dimensions'])
    for r,w in zip(expected,final['fresh_minimum_observations']):
        pred=sum(Q(c)*r['mass']**i*r['dimension']**j for i,j,c in fits[0]['terms']);assert w==dict(r,predicted=str(pred),finite_pass=pred==r['anonymous_response'])
    assert len(expected)==len(final['fresh_minimum_observations']);counts['anonymous_sparse_fits_checked']=len(fits);counts['fresh_minimum_responses_checked']=len(expected)
    passed('independent_anonymous_minimum_tables_sparse_relation_search_and_protected_fresh_estimates')
    fake=final['counterfeit_arithmetic'];head=fake['shared_actual_prefix_through'];fm=mu[:head+1]+[1]*(len(mu)-head-1);assert head==4*max(spec['validation_scales']) and fake['shared_actual_prefix_sha256']==digest(mu[:head+1]) and fake['complete_inverse_sha256']==digest(fm) and fake['rows']==data(fm,cases['scales']) and not fake['actual_complete_inverse']
    c=sum(mu[:head+1])-head;assert c==fake['eventual_affine_offset']
    for r in fake['rows']:
        if r['X']>=head:assert r['signed_defect']==Q(28*r['X']**3-r['X'],3)-2*(c*c-c)*r['X']
    assert any(r['X']>=head for r in fake['rows']);levels=cases['seen_levels']+cases['new_levels'];assert {r['program_id'] for r in final['program_results']}==selected
    for row in final['program_results']:
        p=ids[row['program_id']]['program'];audit_observations(p,final['arithmetic'],levels,row['observations'],counts);audit_observations(p,fake,levels,row['counterfeit_observations'],counts);assert row['score']==score(row['observations'])
    passed('fresh_actual_signed_gap_predictions_unknown_level_constants_and_delayed_cubic_counterfeit')
    assert spec['global_calibration']['D_coefficient']=='16' and spec['global_calibration']['ordinary_energy_power']=='3' and not final['global_actual_critical_signed_gap_proved'] and not final['RH_proved'] and spec['uniform_RH_sufficient_signed_controls_verified']==arc['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[]
    with tempfile.TemporaryDirectory(prefix='signed-gap-profile-replay-') as td:
        p=Path(td);put(p/'protocol.json',spec);subprocess.run([sys.executable,str(BASE/'signed_gap_profile_search.py'),'worker','--run-dir',str(p)],cwd=BASE,check=True);replay={n:sha(p/n) for n in seal['files']};assert replay==seal['files']
    passed('exact_isolated_profile_fit_relation_inference_and_proof_queue_replay')
    put(d/'verification.json',{'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_signed_gap_profiles.py'),'final_sha256':sha(d/'final_evaluation.json'),'queue_sha256':sha(d/'proof_queue.json'),'checks':checks,'counts':counts,'all_passed':all(checks.values()),'replay_sha256':replay,
        'mathematical_audit_imports_production_code':False,'global_actual_critical_signed_gap_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False});print('Independent signed-gap profile audit',len(checks),'/',len(checks),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);check(p.parse_args().run_dir.resolve())
