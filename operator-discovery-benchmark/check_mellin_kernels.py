#!/usr/bin/env python3
"""Independent mathematics: factorized inverse, different complete-tail sums.

No producer mathematical module is imported. Deterministic discovery replay
runs separately; strict parent report loading is read-only provenance checking.
"""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, ceil, log2
from pathlib import Path
import subprocess, sys, tempfile
import flint
from stable_scale_report import BASE,read,sha,digest


def a(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def powq(x,p):
    p=Q(p)
    if not p:return flint.arb(1)
    if x==0 and p>0:return flint.arb(0)
    if not x>0:raise ValueError('Positive rational-power argument required')
    return (a(p)*x.log()).exp()


def put(path,data):
    import json
    Path(path).write_text(json.dumps(data,indent=2)+'\n')


def mu_by_factors(N):
    spf=[0]*(N+1)
    for p in range(2,N+1):
        if spf[p]:continue
        for n in range(p,N+1,p):
            if not spf[n]:spf[n]=p
    mu=[0,1]+[0]*(N-1)
    for n in range(2,N+1):
        t=n;v=1
        while t>1:
            p=spf[t];t//=p;v=-v
            if t%p==0:v=0;break
        mu[n]=v
    return mu


def Padd(P,R):
    out=P.copy()
    for ij,c in R.items():out[ij]=out.get(ij,Q(0))+c
    return {ij:c for ij,c in out.items() if c}


def Pmul(P,R):
    out={}
    for (i,j),c in P.items():
        for (r,h),d in R.items():out[(i+r,j+h)]=out.get((i+r,j+h),Q(0))+c*d
    return {ij:c for ij,c in out.items() if c}


def getpoly(rows):return {(int(i),int(j)):Q(c) for i,j,c in rows if Q(c)}


def pochhammer(m):
    coeff=[1]
    for t in range(m):
        nxt=[0]*(len(coeff)+1)
        for j,c in enumerate(coeff):nxt[j]+=t*c;nxt[j+1]+=c
        coeff=nxt
    return {(j,0):Q(c) for j,c in enumerate(coeff) if c}


def mellin_poly(K):
    out={}
    for m,j,c in K['terms']:
        term={(i,h+j):Q(c)*v for (i,h),v in pochhammer(m).items()}
        out=Padd(out,term)
    return out


def certificate_valid(Ks,cert):
    Ps=[mellin_poly(K) for K in Ks]
    assert [getpoly(p) for p in cert['numerator_polynomials']]==Ps
    if cert['kind']=='exact_bivariate_Bezout':
        As=list(map(getpoly,cert['multipliers']));assert len(As)==len(Ps)
        out={}
        for A,P in zip(As,Ps):out=Padd(out,Pmul(A,P))
        target=Pmul(pochhammer(cert['target_rising_order']),{(0,cert['target_dilation_power']):Q(1)})
        assert out==target==getpoly(cert['target_polynomial']) and target
        assert cert['all_height_no_common_zero'] and not cert['infinite_height_sampling_used']
        return True
    if cert['kind']=='strict_unit_disk_dominance':
        assert len(Ks)==1;terms=getpoly(Ks[0]['terms']);ms={m for m,j in terms};assert len(ms)==1
        m=next(iter(ms));h=min(j for i,j in terms);constant=terms[m,h]
        tail=sum(abs(c) for (i,j),c in terms.items() if j!=h)
        assert abs(constant)>=tail and constant and m==cert['moment'] and h==cert['dilation_power']
        assert Q(cert['constant'])==constant and Q(cert['tail_absolute_sum'])==tail and cert['all_height_no_common_zero']
        return True
    assert cert['kind']=='missing_bounded_certificate' and not cert['all_height_no_common_zero'] and not cert['counterexample_to_growth_bound']
    return False


def Pvalue(P,v,z):
    value=flint.acb(0)
    for (i,j),c in P.items():value+=a(c)*(v**i)*(z**j)
    return value


def tight_overlap(saved,value):
    p=flint.arb(saved)
    assert p.is_finite() and value.is_finite() and p.overlaps(value)
    assert p.rad()<=a(Q(1,2**65))*(1+abs(p))
    assert value.rad()<=a(Q(1,2**65))*(1+abs(value))


def independent_table(table,points,maximum_moment,maximum_dilation,counts):
    k,ell,b=map(Q,(table['k'],table['ell'],table['base']));original=table['resources'];N=original['cutoff']+17
    L=original['tail_Taylor_terms']+8
    precision=max(original['precision']+160,ceil(float(k+ell*(maximum_moment+L))*log2(N))+320)
    flint.ctx.prec=precision;mu=mu_by_factors(N);weights=[]
    sums=[flint.arb(0) for _ in range(L+maximum_moment)]
    for n in range(N,0,-1):
        if not mu[n]:continue
        t=powq(a(n),-ell);w=a(mu[n])*powq(a(n),-k);weights.append((w,t));v=w
        for j in range(len(sums)):sums[j]+=v;v*=t
    moments=[1/a(k+ell*j).zeta()-sums[j] for j in range(len(sums))]
    for j,old in enumerate(table['reciprocal_zeta_tail_moments']):
        adjustment=sum((a(mu[n])*powq(a(n),-k-ell*j) for n in range(original['cutoff']+1,N+1)),flint.arb(0))
        assert flint.arb(old).overlaps(moments[j]+adjustment);counts['independent_real_arithmetic_tail_moments']+=1
    rows={}
    for X in map(Q,points):
        Xe=powq(a(X),ell);Xk=powq(a(X),k)
        for j in range(maximum_dilation+1):
            r=b**j;c=a(r)*Xe
            for m in range(maximum_moment+1):
                prefix=flint.arb(0)
                for w,t in weights:
                    z=c*t;prefix+=w*(z**m)*(-z).exp()
                # Reverse Horner, a different tail prefix and eight additional terms.
                tail=flint.arb(0)
                for t in range(L-1,-1,-1):tail=tail*(-c)+moments[m+t]/factorial(t)
                tail*=c**m;w=k+ell*(m+L)
                error=c**(m+L)*powq(a(N),1-w)/(factorial(L)*a(w-1))
                value=Xk*(prefix+tail+flint.arb(0,error));key=f'{m}:{j}:{X}'
                tight_overlap(table['values'][key],value);rows[key]=value
                counts['independent_complete_infinite_atom_values']+=1
    # Original Taylor errors are recomputed without using its resource function.
    for row in table['tail_certificates']:
        m,j,X=row['moment'],row['dilation'],Q(row['scale']);L0=original['tail_Taylor_terms'];w=k+ell*(m+L0)
        E=powq(a(X),k)*(a(b**j)*powq(a(X),ell))**(m+L0)
        E*=powq(a(original['cutoff']),1-w)/(factorial(L0)*a(w-1))
        assert flint.arb(row['error_bound_ball']).overlaps(E);counts['independent_Taylor_remainder_bounds']+=1
    assert table['infinite_tail_included'] and table['coefficient_prefix_complete'] and not table['new_prime_distribution_bound_imported']
    return rows


def independent_global(K,params,gc,counts):
    k,ell,b=map(Q,params);flint.ctx.prec=512;W=flint.arb(0);J=flint.arb(0)
    def bound(m,r):
        A=Q(k-1)/ell+m
        integral=powq(a(r),Q(1-k)/ell)*a(A).gamma()/a(ell)
        exponent=k/ell+m
        peak=powq(a(r),-k/ell)*powq(a(exponent),exponent)*(-a(exponent)).exp()
        return integral+2*peak
    local=[]
    for m,j,c in K['terms']:
        r=b**j;first=bound(m,r);next_=bound(m+1,r);v=abs(Q(c))
        W+=a(v)*first;J+=a(v)*(a(k+ell*m)*first+a(ell)*next_)
        local.append((k+ell*m,a(v)*a(r**m)*a(k+ell*m).zeta()))
    tight_overlap(gc['constant_ball'],W);tight_overlap(gc['unit_increment_constant_ball'],J)
    for old,(p,v) in zip(gc['local_terms'],local):assert Q(old['power'])==p;tight_overlap(old['constant_ball'],v)
    assert not gc['RH_strength'] and not gc['signed_arithmetic_control_used'];counts['all_scale_weak_and_unit_certificates']+=1
    return W,J,local


@lru_cache(maxsize=None)
def env(eta,margin,nu,d,q,X):
    th=a(eta)+a(margin)*powq(a(q),-Q(nu))
    return (th*a(X).log()).exp()*powq((flint.arb.const_e()+a(X)).log(),Q(d))


def fkey(f):return (f['limit'],f['margin'],f['approach_power'],f['log_power'])


def check_comparison(rows,f,constants,qs,old):
    failures=[];unresolved=[];worst=(0,None);key=fkey(f)
    for i,values in enumerate(rows):
        for q in qs:
            for X,txt in values.items():
                value=abs(flint.arb(txt));B=a(constants[i][str(q)])*env(*key,q,X);case=f'{i}:{q}:{X}'
                if not value<=B:(failures if value>B else unresolved).append(case)
                ratio=float((value/B).upper())
                if ratio>worst[0]:worst=(ratio,case)
    assert failures==old['failures'] and unresolved==old['unresolved']
    assert old['finite_points_passed']==(not failures and not unresolved) and not old['uniform_signed_premise_proved']
    assert abs(old['maximum_ratio']-worst[0])<=1e-10*(1+worst[0])
    return sum(len(r) for r in rows)*len(qs)


def check_constants(values,f,qs,constants,spec):
    D=int(spec['constant_rule']['upward_denominator']);key=fkey(f)
    for q in qs:
        maximum=max((abs(flint.arb(v))/env(*key,q,X)).upper() for X,v in values.items())
        exact=Q(max(1,int((maximum*a(spec['constant_rule']['training_margin'])*D).ceil().fmpz())),D)
        assert Q(constants[str(q)])==exact


@lru_cache(maxsize=None)
def native_context(params,query):
    k,ell,b=map(Q,params);sigma,t=map(Q,query)
    v=(a(k)-flint.acb(a(sigma),a(t)))/a(ell)
    return v,(-v*a(b).log()).exp(),v.gamma()


def check_cost(Ks,cert,params,f,constants,qs,gcs,old,query,counts):
    k,ell,b=map(Q,params);sigma,t=map(Q,query)
    if not cert['all_height_no_common_zero']:
        assert old['status']=='missing_all_height_recovery_certificate' and old['best_log_cost'] is None;return
    v,z,G=native_context(tuple(params),tuple(query));Ps=[mellin_poly(K) for K in Ks]
    if cert['kind']=='exact_bivariate_Bezout':
        rhs=Pvalue(getpoly(cert['target_polynomial']),v,z);lower=(G*rhs).abs_lower()
        factors=[Pvalue(getpoly(P),v,z).abs_upper() for P in cert['multipliers']]
    else:lower=(G*Pvalue(Ps[0],v,z)).abs_lower();factors=[flint.arb(1)]
    assert lower>0;costs=[]
    for q,row in zip(qs,old['observers']):
        assert row['q']==q;gap=a(sigma)-a(f['limit'])-a(f['margin'])*powq(a(q),-Q(f['approach_power']))
        assert flint.arb(row['gap_ball']).overlaps(gap)
        if not gap>0:
            assert row['status']=='outside_this_observers_convergence_domain';counts['observers_outside_convergence_domain']+=1;continue
        d=ceil(Q(f['log_power']));L0=(flint.arb.const_e()+1).log()
        integral=sum((a(Q(factorial(d),factorial(j)*factorial(d-j)))*L0**(d-j)*factorial(j)/gap**(j+1)
            for j in range(d+1)),flint.arb(0))
        norms=[]
        for C,(W,J,local) in zip(constants,gcs):
            norm=sum((value/a(p-sigma) for p,value in local),flint.arb(0))+J/a(sigma)+a(C[str(q)])*integral
            norms.append(norm)
        cost=a(ell)*sum((factor*norm for factor,norm in zip(factors,norms)),flint.arb(0))/lower
        assert row['status']=='conditional_global_signed_bound_required' and not row['uniform_premise_verified']
        tight_overlap(row['Mellin_log_moment_ball'],integral)
        for txt,norm in zip(row['complete_transform_norm_balls'],norms):tight_overlap(txt,norm)
        assert flint.arb(row['native_denominator_lower_ball']).overlaps(lower)
        tight_overlap(row['conditional_reciprocal_zeta_bound_ball'],cost)
        assert flint.arb(row['native_gamma_ball']['real']).overlaps(G.real) and flint.arb(row['native_gamma_ball']['imag']).overlaps(G.imag)
        costs.append(float(cost.upper().log()));counts['fully_charged_native_Mellin_observers']+=1
    if costs:assert old['status']=='conditional' and abs(min(costs)-old['best_log_cost'])<1e-9
    else:assert old['status']=='no_tested_q_inside_this_observers_domain' and old['best_log_cost'] is None


def check(directory,replay=True):
    spec=read(directory/'protocol.json');seal=read(directory/'seal.json');batch=read(directory/'candidate_batch.json');arc=read(directory/'archive.json')
    final=read(directory/'final_evaluation.json');cases=read(directory/'final_cases.json');pc=read(directory/'parameter_cases.json')
    calibration=read(directory/'parameter_calibration.json');cs=read(directory/'calibration_seal.json');checks={};counts={k:0 for k in [
        'independent_complete_infinite_atom_values','independent_real_arithmetic_tail_moments','independent_Taylor_remainder_bounds',
        'all_scale_weak_and_unit_certificates','exact_all_height_bank_certificates','complete_frontier_hypotheses_checked',
        'fully_charged_native_Mellin_observers','observers_outside_convergence_domain','validation_comparisons',
        'fresh_final_comparisons','new_parameter_constants_calibrated_before_final_scales','counterfeit_finite_comparisons',
        'unit_increment_witnesses','weak_bound_witnesses','generic_signed_inverse_coefficients','generic_finite_atom_responses']}
    def passed(name):checks[name]=True;print('Verified',name,flush=True)
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(directory/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(directory/n)==h
    for dep in spec['named_calibration_dependencies']:assert sha(dep['path'])==dep['sha256'] and dep['imported_not_independently_reproved']
    source=Path(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    from mertens_limit_report import summary as parent
    parent(source);passed('frozen_source_parent_and_named_import_provenance')
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist_at_seal'] and not seal['parameter_cases_exist_at_seal']
    assert arc['selection_closed'] and not arc['final_data_used'] and batch['frozen_before_validation'] and batch['generation_uses_training_only']
    assert pc['seal_sha256']==digest(seal) and pc['generated_after_archive_seal'] and pc['no_final_scale_information_present']
    assert calibration['parameters_sha256']==digest(pc) and calibration['training_only'] and not calibration['final_scales_used']
    assert cs['archive_seal_sha256']==sha(directory/'seal.json') and cs['parameter_cases_sha256']==sha(directory/'parameter_cases.json')
    assert cs['parameter_calibration_sha256']==sha(directory/'parameter_calibration.json') and not cs['final_cases_exist_at_calibration_seal']
    assert cases['calibration_seal_sha256']==digest(cs) and cases['generated_after_calibration_seal']
    assert final['protocol_sha256']==digest(spec) and final['cases_sha256']==digest(cases) and final['calibration_seal_sha256']==digest(cs) and final['seal_sha256']==digest(seal)
    assert not set(pc['fresh_q'])&set(spec['training_q']+spec['validation_new_q'])
    for run in spec['retained_failed_runs_are_development']:
        d=Path(run['run_directory']);assert sha(d/'failure.json')==run['failure_sha256']
        for n,h in run['retained_files_sha256'].items():assert sha(d/n)==h
        for n,h in run['original_code_sha256'].items():
            if n in read(d/'protocol.json')['this_stage_source_files']:assert sha(d/'frozen_source'/n)==h
        assert not set(cases['integers'])&set(run['excluded_final_scales']) and not set(pc['fresh_q'])&set(run['excluded_final_q'])
    passed('archive_then_parameter_calibration_then_fresh_scale_seals')
    discovery=read(directory/'discovery_data.json');validation=read(directory/'validation_data.json')
    for denial in [discovery['worker_access_denials'],calibration['worker_access_denials']]:assert all(denial.values()) and len(denial)==4
    passed('generator_and_new_parameter_calibrator_isolation')
    independent={}
    for name,data,points in [('training',discovery,spec['training_points']),('validation',validation,spec['validation_points']),
        ('final',final['complete_arithmetic_data'],cases['points'])]:
        assert digest(mu_by_factors(data['cutoff']))==data['inverse_coefficient_sha256'] and data['all_infinite_tails_included']
        independent[name]={}
        for pid,table in data['tables'].items():
            independent[name][pid]=independent_table(table,points,spec['maximum_moment'],spec['maximum_dilation'],counts)
            print('Independent complete sums',name,table['k'],table['ell'],flush=True)
    passed('factorized_actual_inverse_and_changed_complete_tail_algorithms')
    ps={p['id']:p for p in batch['ablation_programs']+batch['programs']};bs={b['id']:b for b in batch['ablation_banks']+batch['banks']};gcs={}
    for pid,p in ps.items():gcs[pid]=independent_global(p['kernel'],p['parameters'],batch['global_certificates'][pid],counts)
    for b in bs.values():
        assert b['id']==digest({'members':b['member_ids']}) and b['member_ids']==sorted(b['member_ids'])
        good=certificate_valid([ps[i]['kernel'] for i in b['member_ids']],b['recovery_certificate'])
        if good:counts['exact_all_height_bank_certificates']+=1
    passed('global_unimodal_unit_bounds_and_exact_bivariate_recovery_identities')
    flint.ctx.prec=384
    for name,rows in [('training',batch['training_responses']),('validation',validation['program_responses']),('final',final['program_responses'])]:
        for pid,values in rows.items():
            p=ps[pid];table=independent[name][p['parameter_id']]
            for X,txt in values.items():
                value=sum((a(c)*table[f'{m}:{j}:{X}'] for m,j,c in p['kernel']['terms']),flint.arb(0))
                tight_overlap(txt,value)
    passed('all_signed_program_responses_recomputed_from_independent_complete_sums')
    qs=spec['training_q']+spec['validation_new_q']
    for c in batch['candidates']:
        b=bs[c['bank_id']];ids=b['member_ids'];f=c['frontier'];constants=c['illustrative_constants_by_member_and_q']
        assert Q(f['margin'])>0 and Q(f['approach_power'])>0 and Q(f['log_power'])>=0
        assert f['constant_quantifiers']=='for every q there exists finite C_q, for every integer N>=1'
        assert not f['constant_growth_in_q_restricted'] and not f['finite_parameter_grid_suffices'] and not f['uniform_signed_premise_proved']
        assert c['RH_sufficient_if_uniform']==(Q(f['limit'])<=Q(1,2) and b['recovery_certificate']['all_height_no_common_zero'])
        for i,C in zip(ids,constants):check_constants(batch['training_responses'][i],f,qs,C,spec)
        attempt=c['certificate_attempt']
        if Q(f['limit'])>=1:assert attempt['status']=='unconditional_weak_frontier_proved' and not attempt['RH_strength'] and not attempt['same_numerical_fitted_constants_proved']
        else:assert attempt['status']=='missing_uniform_signed_cancellation_certificate' and not attempt['counterexample_to_candidate'] and not attempt['RH_strength_uniform_estimate_proved']
        if Q(f['limit'])<=Q(1,2):check_cost([ps[i]['kernel'] for i in ids],b['recovery_certificate'],b['parameters'],f,constants,spec['training_q'],[gcs[i] for i in ids],c['recovery_cost'],spec['cost_query'],counts)
        counts['complete_frontier_hypotheses_checked']+=1
    passed('free_constant_cofinal_quantifiers_and_all_complete_hypothesis_costs')
    for c in validation['candidates']:
        ids=bs[c['bank_id']]['member_ids'];counts['validation_comparisons']+=check_comparison([validation['program_responses'][i] for i in ids],c['frontier'],c['illustrative_constants_by_member_and_q'],qs,c['validation'])
    passed('training_only_constants_and_held_out_validation_comparisons')
    newcs={r['candidate_id']:r['constants'] for r in calibration['illustrative_free_constants']};outcomes={o['candidate_id']:o for o in final['outcomes']};rule=spec['final_cases'];fqs=spec['training_q']+pc['fresh_q']
    for c in arc['archive']:
        ids=bs[c['bank_id']]['member_ids'];Cs=[]
        for i,old,new in zip(ids,c['illustrative_constants_by_member_and_q'],newcs[c['id']]):
            check_constants(batch['training_responses'][i],c['frontier'],pc['fresh_q'],new,spec)
            counts['new_parameter_constants_calibrated_before_final_scales']+=len(pc['fresh_q']);Cs.append(dict(old,**new))
        rows=[{str(n):final['program_responses'][i][str(n)] for n in cases['integers']+rule['boundary']} for i in ids]
        counts['fresh_final_comparisons']+=check_comparison(rows,c['frontier'],Cs,fqs,outcomes[c['id']])
    passed('fresh_q_constants_sealed_before_native_final_scale_evaluation')
    byc={c['id']:c for c in arc['archive']}
    for ctrl in final['counterfeit_controls']:
        c=byc[ctrl['candidate_id']];b=bs[c['bank_id']];ids=b['member_ids'];assert c['RH_sufficient_if_uniform']
        assert ctrl['analytic_status']=='globally_false_by_uncancelled_counterfeit_pole_at_one' and not ctrl['actual_arithmetic']
        H=Q(spec['counterfeit_tail_cutoff']);fake=[]
        for i in ids:
            k,ell,base=map(Q,ps[i]['parameters']);rows={}
            for n in cases['integers']+rule['boundary']:
                E=sum((a(abs(Q(cj)))*a(base**(j*m))*powq(a(n),k+ell*m)*powq(a(H),1-k-ell*m)/a(k+ell*m-1)
                    for m,j,cj in ps[i]['kernel']['terms']),flint.arb(0))
                rows[str(n)]=flint.arb(final['program_responses'][i][str(n)])+flint.arb(0,E)
                assert rows[str(n)].overlaps(flint.arb(ctrl['complete_counterfeit_enclosures'][ids.index(i)][str(n)]))
            fake.append(ctrl['complete_counterfeit_enclosures'][ids.index(i)])
        Cs=[dict(old,**new) for old,new in zip(c['illustrative_constants_by_member_and_q'],newcs[c['id']])]
        counts['counterfeit_finite_comparisons']+=check_comparison(fake,c['frontier'],Cs,fqs,ctrl)
        # Exact common-numerator certificate is nonzero at the counterfeit pole.
        cert=b['recovery_certificate'];assert cert['all_height_no_common_zero'];v=a((k-1)/ell);z=powq(a(base),-(k-1)/ell)
        if cert['kind']=='exact_bivariate_Bezout':assert Pvalue(getpoly(cert['target_polynomial']),flint.acb(v),flint.acb(z)).abs_lower()>0
        else:assert Pvalue(mellin_poly(ps[ids[0]]['kernel']),flint.acb(v),flint.acb(z)).abs_lower()>0
    passed('counterfeit_all_scale_pole_obstruction_separate_from_finite_successes')
    for row in final['unit_increment_checks']:
        i,n=row['program_id'],row['integer'];J=gcs[i][1]
        diff=abs(flint.arb(final['program_responses'][i][str(Q(n)+Q(rule['real_offset']))])-flint.arb(final['program_responses'][i][str(n)]))
        assert diff<=J*a(rule['real_offset']) and row['passed'];counts['unit_increment_witnesses']+=1
    for row in final['weak_bound_checks']:
        assert abs(flint.arb(final['program_responses'][row['program_id']][row['scale']]))<=gcs[row['program_id']][0]*a(row['scale']) and row['passed'];counts['weak_bound_witnesses']+=1
    passed('fresh_unit_and_weak_all_scale_bound_witnesses')
    for row in final['generic_inputs']:
        case=row['case'];f=list(map(Q,case['input']));g=list(map(Q,row['inverse']));N=len(f)-1
        for n in range(1,N+1):assert sum((f[d]*g[n//d] for d in range(1,n+1) if n%d==0),Q(0))==(1 if n==1 else 0);counts['generic_signed_inverse_coefficients']+=1
        k,ell,base=map(Q,case['parameters']);X=Q(case['scale'])
        for value in row['finite_atom_responses']:
            m,j=value['moment'],value['dilation'];total=flint.arb(0)
            for n in range(N,0,-1):
                y=a(base**j)*powq(a(X)/n,ell);total+=a(g[n])*powq(a(X)/n,k)*(y**m)*(-y).exp()
            tight_overlap(value['finite_response_ball'],total);counts['generic_finite_atom_responses']+=1
        assert not row['infinite_tail_claimed']
    passed('unrelated_rational_inputs_with_generic_finite_inverse_semantics')
    # Known-operator calibration occurs after discovery and has no winner assertion.
    calibration_K={'terms':[[0,0,'1']]};assert mellin_poly(calibration_K)=={(0,0):Q(1)}
    s=flint.acb(a(Q(3,2)),a(Q(1,3)));v=(2-s)/2
    # Independent integral of the kernel for the delta_1 input. This catches
    # the k-s sign, rational root reparametrization, and the factor 1/ell.
    integral=flint.acb.integral(lambda t,analytic:((2-s)*t-(2*t).exp()).exp(),-64,4,
        abs_tol=a(Q(1,2**100)),rel_tol=a(Q(1,2**100)),eval_limit=200000,depth_limit=50)
    lower_error=(-a(Q(1,2))*64).exp()/a(Q(1,2))
    upper_error=(a(8).exp()).gamma_upper(a(Q(1,4)))/2
    error=lower_error+upper_error
    integral+=flint.acb(flint.arb(0,error),flint.arb(0,error))
    assert integral.is_finite() and integral.overlaps(v.gamma()/2)
    assert not integral.overlaps(v.gamma())
    assert (a(Q(1,2))+a(Q(1,4))*powq(a(1013),-Q(1,1013))).is_finite()
    passed('separate_Riesz_calibration_and_unbounded_rational_root_semantics')
    replay_hashes={}
    if replay:
        with tempfile.TemporaryDirectory(prefix='mellin-kernel-replay-') as td:
            d=Path(td);put(d/'protocol.json',spec)
            subprocess.run([sys.executable,str(BASE/'mellin_kernel_search.py'),'worker','--run-dir',str(d)],check=True,cwd=BASE)
            replay_hashes={n:sha(d/n) for n in seal['files']}
            assert replay_hashes==seal['files']
        passed('deterministic_isolated_generation_adaptation_and_archive_replay')
    else:raise ValueError('A successful published verification requires replay')
    assert spec['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[] and not final['RH_proved']
    assert spec['not_autonomous_proof_invention'] and not spec['new_prime_distribution_estimate_imported']
    passed('RH_signed_uniform_gap_and_import_scopes_remain_explicit')
    result={'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_mellin_kernels.py'),
        'final_sha256':sha(directory/'final_evaluation.json'),'checks':checks,'all_passed':all(checks.values()),
        'counts':counts,'replay_sha256':replay_hashes,'uniform_RH_sufficient_signed_controls_verified':[],
        'RH_proved':False,'mathematical_proof_machine_formalized':False}
    put(directory/'verification.json',result);print('Independent verification',sum(checks.values()),'/',len(checks),flush=True)
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);args=p.parse_args()
    check(args.run_dir.resolve())


if __name__=='__main__':main()
