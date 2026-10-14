#!/usr/bin/env python3
"""Independent exact divisor sums, Sylvester certificates and proof-queue audit."""
import argparse,random,subprocess,sys,tempfile
from functools import lru_cache
from pathlib import Path
from fractions import Fraction as Q
from math import gcd,lcm,isqrt
import flint
from stable_scale_report import BASE,read,sha,digest
from check_signed_control import independent_inverse
from check_mellin_kernels import put


def ceiling(n,p):
    """Independent exact ceiling with the declared integer/fraction split."""
    p=Q(p);k=p.numerator//p.denominator;r=p-k
    if not r:return n**k
    if r.numerator==1 and r.denominator>n.bit_length():return n**k*(1 if n==1 else 2)
    a,b=r.numerator,r.denominator
    target=n**a;lo,hi=0,n+1
    while hi-lo>1:
        mid=(hi+lo)//2
        if mid**b<=target:lo=mid
        else:hi=mid
    return n**k*(lo if lo**b==target else lo+1)


def weight(mask,n,N):
    k=mask['kind']
    if k=='constant':return mask['value']
    if k=='above':return int(n>mask['threshold'])
    if k=='residue':return int(n%mask['modulus']==mask['residue'])
    if k=='divisible_union':return int(any(n%b==0 for b in mask['bases']))
    if k=='square':return int(isqrt(n)**2==n)
    if k=='prefix':
        p=Q(mask['power']);lo,hi=0,N+1
        while hi-lo>1:
            mid=(lo+hi)//2
            if mid**p.denominator<=N**p.numerator:lo=mid
            else:hi=mid
        return int(n<=lo)
    raise ValueError('Unsupported independently checked mask')


@lru_cache(maxsize=128)
def direct_gram(mask_tuple,N):
    mask=__import__('json').loads(mask_tuple);G=[[0]*N for _ in range(N)]
    for k in range(1,N+1):
        w=weight(mask,k,N);assert w in [0,1]
        if not w:continue
        div=[n-1 for n in range(1,k+1) if k%n==0]
        for i in div:
            for j in div:G[i][j]+=1
    return G


def matrix(program,X,q):
    import json
    N=4*X;D=Q(program['diagonal_coefficient'])*(1+ceiling(q,program['level_power']))*X*ceiling(X,Q(1,q));Y=Q(program['Gram_coefficient'])*ceiling(X,program['Gram_power']);w1=weight(program['mask'],1,N)
    G=direct_gram(json.dumps(program['mask'],sort_keys=True),N);S=[]
    for i in range(1,N+1):
        row=[]
        for j in range(1,N+1):
            # Recover H from the actual two integration windows.
            H=sum(int(i<=t and j<=t) for t in range(2*X,4*X))-4*sum(int(i<=t and j<=t) for t in range(X,2*X))
            row.append(D*int(i==j)-H+Y*G[i-1][j-1])
        S.append(row)
    den=lcm(*(v.denominator for row in S for v in row));A=[[int(v*den) for v in row] for row in S]
    return {'D':str(D),'Y':str(Y),'unit_forcing_weight':w1,'charged_defect_bound':str(N*D+Y*w1),
        'ordinary_energy_power':str(max(2+Q(1,q),Q(program['Gram_power']) if w1 else 0)),'level_constant_may_grow':Q(program['level_power'])>0,'missing':False},A,den


def direct_inverse(f):
    f=list(map(Q,f));N=len(f)-1;v=[Q(0),Q(1)]+[Q(0)]*(N-1)
    for k in range(2,N+1):
        accum=sum((f[d]*v[k//d] for d in range(2,k+1) if k%d==0),Q(0));v[k]=-accum
    response=[sum((f[d]*v[k//d] for d in range(1,k+1) if k%d==0),Q(0)) for k in range(1,N+1)]
    return v,response


def family(p):
    w1=weight(p['mask'],1,4);r=Q(p['level_power']);gamma=Q(p['Gram_power']);admitted=p['arithmetic_model']=='inverse_one' and Q(p['diagonal_coefficient'])>0 and Q(p['Gram_coefficient'])>=0 and r>=0 and gamma>=0 and (not w1 or gamma<=2)
    return admitted,r==0 and admitted


def audit_matrix(row,program,counts,actual=None):
    X,q=row['X'],row['level'];c=row['certificate'];params,A,den=matrix(program,X,q);assert params==c['parameters'];N=len(A);cost=Q(params['charged_defect_bound']);upper=sum(n*n for n in range(2*X,4*X));assert Q(row['fully_charged_bound_over_generic'])==cost/upper
    counts['exact_matrix_cases']+=1
    if c.get('missing'):
        assert not c['finite_matrix_PSD'] and c['missing_not_counterexample'];counts['missing_native_certificates']+=1;return
    if c['finite_matrix_PSD']:
        assert c['status']=='finite_native_LDL_positive' and c['dimension']==N and len(c['pivot_balls'])==N and not c['global_critical_PSD_proved'] and not c['RH_proved']
        previous=1
        for k,b in enumerate(c['pivot_balls'],1):
            determinant=int(flint.fmpz_mat([r[:k] for r in A[:k]]).det());assert determinant>0
            pivot=flint.fmpq(determinant,previous*den);enclosure=flint.arb(b);assert enclosure>0 and enclosure.contains(pivot);previous=determinant;counts['exact_positive_Sylvester_minors']+=1
        assert c['global_PSD_proved']==(q==1 and Q(params['D'])>=8*X**2)
        if actual is not None:assert actual[X]<=cost;counts['actual_signed_defect_finite_bounds']+=1
        counts['finite_positive_matrices']+=1
    else:
        z=list(map(Q,c['counterexample']['vector']));assert len(z)==N
        zd=lcm(*(v.denominator for v in z));zi=[int(v*zd) for v in z]
        value=Q(sum(zi[i]*A[i][j]*zi[j] for i in range(N) for j in range(N)),den*zd*zd)
        assert value==Q(c['counterexample']['exact_quadratic_value'])<0 and c['counterexample']['rejects_candidate_matrix_not_actual_RH_inequality'];counts['exact_negative_quadratic_witnesses']+=1


def sort_key(score,p):return (-score['positive_matrix_cases'],Q(score['maximum_charged_bound_over_generic']),len(str(p['program'])),p['id'])


def check(d):
    spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');val=read(d/'validation.json');arc=read(d/'archive.json');queue=read(d/'proof_queue.json');seal=read(d/'seal.json');cases=read(d/'final_cases.json');final=read(d/'final_evaluation.json');checks={};counts={k:0 for k in ['exact_matrix_cases','exact_positive_Sylvester_minors','missing_native_certificates','finite_positive_matrices','exact_negative_quadratic_witnesses','actual_signed_defect_finite_bounds']}
    def passed(name):checks[name]=True;print('Verified',name,flush=True)
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    from critical_defect_report import summary as parent
    parent(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/n)==h
    assert digest(spec)==seal['protocol_sha256']==batch['protocol_sha256']==queue['protocol_sha256']==final['protocol_sha256'] and seal['selection_closed'] and not seal['final_cases_exist'] and all(batch['access_denials'].values())
    assert cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json') and final['cases_sha256']==digest(cases) and not set(cases['scales'])&set(spec['training_scales']+spec['validation_scales']) and not set(cases['levels'])&set(spec['training_levels'])
    for f in spec['retained_failed_runs_are_development']:
        p=Path(f['run_directory']);assert sha(p/'failure.json')==f['failure_sha256']
        for n,h in f['files_sha256'].items():assert sha(p/n)==h
        assert not set(cases['scales'])&set(f['excluded_final_scales'])
    passed('frozen_sources_isolated_worker_and_protected_fresh_evaluation')
    flint.ctx.prec=1024
    forcing=batch['forcing_calibrations'];N=spec['mask_response_cutoff'];targets=[]
    for f in forcing:
        inv,response=direct_inverse(f['input']);assert inv==list(map(Q,f['inverse'])) and response==list(map(Q,f['anonymous_response'])) and not f['prime_or_factor_oracle_used'];assert response==[1]+[0]*(N-1)
    targets=[int(all(Q(f['anonymous_response'][i])==0 for f in forcing)) for i in range(N)]
    for fit in batch['mask_inferences']:
        values=[weight(fit['mask'],n,N) for n in range(1,N+1)];assert fit['exact_squared_residual']==sum((v-y)**2 for v,y in zip(values,targets)) and not fit['operator_names_or_expected_mask_supplied'] and not fit['universal_response_pattern_claimed']
    expected=sorted(batch['mask_inferences'],key=lambda f:(f['exact_squared_residual'],f['description_length'],digest(f['mask'])));assert expected==batch['mask_inferences']
    for promotion in batch['promotions']:
        chosen=next(f for f in expected if not f['exact_squared_residual'] and f['mask']not in spec['baseline_masks']);assert promotion['mask']==chosen['mask'] and promotion['evidence']==chosen and promotion['all_index_mask_semantics_preserved'] and promotion['unit_forcing_charge']==weight(chosen['mask'],1,4)
    assert len(batch['promotions'])==len(batch['ablation_masks'])<=spec['mask_promotion_slots']
    passed('anonymous_generic_inverse_responses_mask_fitting_and_equal_slot_promotion')
    columns={name:[] for name in spec['kernel_feature_dictionary']};ys=[]
    import json
    for row in batch['kernel_response_observations']:
        N,i,j=row['dimension'],row['i'],row['j'];G=direct_gram(json.dumps({'kind':'constant','value':1},sort_keys=True),N);y=G[i-1][j-1];assert y==row['value'];ys.append(Q(y))
        values=[Q(N//lcm(i,j)),Q(N,lcm(i,j)),Q(N//gcd(i,j)),Q(N//max(i,j)),Q(N//min(i,j)),Q(i==j),Q(i==j==1),Q(1)]
        for name,v in zip(columns,values):columns[name].append(v)
    norm=sum(y*y for y in ys)
    for fit in batch['kernel_inferences']:
        xx=sum(x*x for x in columns[fit['feature']]);c=(sum(x*y for x,y in zip(columns[fit['feature']],ys))/xx).limit_denominator(64);error=sum((y-c*x)**2 for x,y in zip(columns[fit['feature']],ys))/norm
        assert Q(fit['coefficient'])==c and Q(fit['relative_squared_residual'])==error and not fit['expected_kernel_or_coefficient_supplied']
    best=batch['kernel_inferences'][0];assert batch['kernel_exact_admission']==(best['feature']=='floor(N/lcm(i,j))' and Q(best['coefficient'])==1 and Q(best['relative_squared_residual'])==0)
    passed('independent_direct_divisor_Grams_broad_kernel_fit_and_exact_counting_admission')
    programs=batch['programs'];ids={p['id']:p for p in programs};assert len(ids)==len(programs) and len(batch['profiles'])==spec['profiles_per_mask']
    for p in programs:
        assert p['id']==digest(p['program']);admitted,strong=family(p['program']);f=p['family_certificate'];assert f['admitted']==admitted and f.get('bounded_level_constants_would_imply_stronger_fixed_critical_bound')==strong and not f.get('global_RH_signed_premise_proved',False)
    for origin,masks in [('baseline',spec['baseline_masks']),('learned_zero_forcing_mask',[p['mask'] for p in batch['promotions']]),('equal_slot_random_mask',batch['ablation_masks'])]:
        found=[p for p in programs if p['origin']==origin];assert len(found)==len(masks)*len(batch['profiles'])
        assert {p['id'] for p in found}=={digest(dict(pr,mask=m)) for pr in batch['profiles'] for m in masks}
    passed('complete_program_provenance_balanced_rational_profiles_and_charged_cost_scope')
    for split,rows in [('training',batch['training_matrix_certificates']),('validation',val['matrix_certificates'])]:
        expected={(p['id'],X,q) for p in programs for X in spec[split+'_scales'] for q in spec[split+'_levels']};assert {(r['program_id'],r['X'],r['level']) for r in rows}==expected
        for row in rows:audit_matrix(row,ids[row['program_id']]['program'],counts)
        passed('every_'+split+'_native_positive_matrix_and_exact_negative_direction_independently_checked')
    byscore={r['program_id']:r for r in val['scores']}
    for p in programs:
        rows=[r for r in val['matrix_certificates'] if r['program_id']==p['id']];positive=[r for r in rows if r['certificate'].get('finite_matrix_PSD')];score=byscore[p['id']]
        assert score['positive_matrix_cases']==len(positive) and score['total_cases']==len(rows) and Q(score['maximum_charged_bound_over_generic'])==max((Q(r['fully_charged_bound_over_generic']) for r in positive),default=Q(10**100)) and not score['global_critical_PSD_proved']
    for mode,origin in [('primary','learned_zero_forcing_mask'),('promotion_disabled','equal_slot_random_mask')]:
        eligible=[p for p in programs if p['origin']in ['baseline',origin] and p['family_certificate']['admitted']]
        for power in spec['level_powers']:
            sub=[p for p in eligible if p['program']['level_power']==power]
            if sub:
                chosen=min(sub,key=lambda p:sort_key(byscore[p['id']],p));r=next(r for r in arc['matrix_leads'] if r['mode']==mode and r['level_power']==power);assert r['program_id']==chosen['id'] and r['validation_score']==byscore[chosen['id']]
        comparison=next(r for r in arc['ablation_comparison'] if r['mode']==mode);best=min(eligible,key=lambda p:sort_key(byscore[p['id']],p));assert comparison['best_program_id']==best['id'] and comparison['extra_profiles_per_mask']==len(batch['profiles']) and comparison['same_response_and_scalar_profile_budget']
    selected={r['program_id'] for r in arc['matrix_leads']};assert {r['program_id'] for r in queue['queue']}==selected and queue['candidate_ids_frozen_before_final'] and not queue['final_data_used_for_selection'] and queue['analytic_results_must_not_edit_frozen_candidates']
    for r in queue['queue']:
        p=ids[r['program_id']];assert r['exact_program']==p['program'] and r['validation_evidence']==byscore[p['id']] and r['RH_recovery_certificate']==p['family_certificate'] and not r['formula_changed_after_detection'] and r['proof_status']=='pending_separate_analytic_attempt' and r['missing_lemma']=='uniform PSD comparison for this exact template'
    passed('frozen_selection_equal_budget_ablation_and_exact_candidate_proof_queue')
    mu,M=independent_inverse(4*max(cases['scales']));assert mu==final['actual_mobius_prefix'];actual={X:sum(M[n]**2 for n in range(2*X,4*X))-4*sum(M[n]**2 for n in range(X,2*X)) for X in cases['scales']}
    assert final['actual_signed_defects']==[{'X':X,'exact_actual_signed_defect':actual[X]} for X in cases['scales']]
    rows=final['matrix_certificates'];expected={(pid,X,q) for pid in selected for X in cases['ordinary_scales'] for q in cases['levels']}|{(final['large_probe_program_id'],cases['large_probe_scale'],cases['levels'][0])};assert {(r['program_id'],r['X'],r['level']) for r in rows}==expected
    for row in rows:audit_matrix(row,ids[row['program_id']]['program'],counts,actual)
    counts['independent_prime_inverse_coefficients']=len(mu)-1
    passed('every_fresh_matrix_exact_actual_prime_arithmetic_and_whole_signed_defect_bound')
    c=arc['global_generic_calibration'];X,q=4,1;params,A,den=matrix(c['program'],X,q);assert Q(params['D'])>=8*X**2 and Q(c['program']['diagonal_coefficient'])>=4 and c['certificate']['global_PSD_proved'] and not c['certificate']['global_critical_PSD_proved']
    audit_matrix({'X':X,'level':q,'certificate':c['certificate'],'fully_charged_bound_over_generic':str(Q(params['charged_defect_bound'])/sum(n*n for n in range(2*X,4*X)))},c['program'],counts)
    controls=final['controls']
    for row in controls['finite_prime_row_controls']:
        P=row['bases'];v=row['values'];X=row['X'];assert len(v)==4*X+1
        for n in range(1,4*X+1):
            expected=1
            for p in P:
                if n%(p*p)==0:expected=0;break
                if n%p==0:expected=-expected
            assert v[n]==expected
            if any(n%p==0 for p in P):assert sum(v[d] for d in range(1,n+1) if n%d==0)==0
        mean=Q(1)
        for p in P:mean*=Q(p-1,p)**2
        prefix=[0]
        for value in v[1:]:prefix.append(prefix[-1]+value)
        R=4**len(P);assert all(abs(prefix[n]-mean*n)<=R for n in range(len(prefix)));defect=sum(prefix[n]**2 for n in range(2*X,4*X))-4*sum(prefix[n]**2 for n in range(X,2*X));error=24*mean*R*X**2+6*R**2*X
        assert defect==row['full_signed_defect'] and Q(row['linear_mean'])==mean and Q(row['positive_cubic_leading_coefficient'])==Q(28,3)*mean**2 and Q(row['all_scale_cubic_error_upper'])==error and abs(Q(defect)-Q(28,3)*mean**2*X**3)<=error
    f=controls['generic_large_inverse_control'];v,response=direct_inverse(f['input']);assert v==list(map(Q,f['inverse'])) and response==[1]+[0]*(len(v)-2) and max(abs(t) for t in v)>1 and all(controls['negative_controls'].values())
    passed('global_power_three_calibration_generic_norm_failure_and_all_scale_pruned_prime_row_barriers')
    assert not final['global_critical_matrix_PSD_proved'] and not final['RH_proved'] and spec['uniform_RH_sufficient_signed_controls_verified']==arc['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[]
    with tempfile.TemporaryDirectory(prefix='divisor-dual-replay-') as td:
        p=Path(td);put(p/'protocol.json',spec);subprocess.run([sys.executable,str(BASE/'divisor_dual_search.py'),'worker','--run-dir',str(p)],cwd=BASE,check=True);replay={n:sha(p/n) for n in seal['files']};assert replay==seal['files']
    passed('exact_isolated_detector_selection_and_proof_queue_replay')
    result={'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_divisor_dual.py'),'final_sha256':sha(d/'final_evaluation.json'),'proof_queue_sha256':sha(d/'proof_queue.json'),'checks':checks,'counts':counts,'all_passed':all(checks.values()),'replay_sha256':replay,
        'mathematical_audit_imports_production_code':False,'machine_formalized':False,'global_critical_matrix_PSD_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False};put(d/'verification.json',result);print('Independent divisor-dual verification',len(checks),'/',len(checks),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);check(p.parse_args().run_dir.resolve())
