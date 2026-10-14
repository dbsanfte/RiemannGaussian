#!/usr/bin/env python3
"""Independent rectangular actual arithmetic, global bounds and zero auditing.

Never imports a producer mathematical module. Producer replay runs separately.
The rectangle is factorized for moments and evaluated explicitly for kernels.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,ceil,comb
from pathlib import Path
import subprocess,sys,tempfile
import flint
from stable_scale_report import BASE,read,sha,digest
from check_mellin_kernels import a,powq,put,mu_by_factors,tight_overlap,pochhammer
from check_lattice_synthesis import (root_check as frozen_root_check,companion_hermite,real_root_count,squarefree)


def overlap(txt,v):tight_overlap(txt,v)
def cp(saved,z):overlap(saved['real'],z.real);overlap(saved['imag'],z.imag)


def rectangular_table(table,points,counts):
    K,ell,r=map(Q,table['parameters']);R=K/ell;assert K>max(Q(1),1/r) and Q(table['rate'])==R
    L=table['Taylor_terms']+12;mmax=table['maximum_moment'];flint.ctx.prec=table['precision']+192;J,D=17,61;mu=mu_by_factors(D)
    js=[(powq(a(j),-K),powq(a(j),-ell)) for j in range(J,0,-1)]
    ds=[(powq(a(d),-r*K),powq(a(d),-r*ell),mu[d]) for d in range(D,0,-1)];sJ=[flint.arb(0) for _ in range(L+mmax)];sD={model:[flint.arb(0) for _ in range(L+mmax)] for model in ['inverse','unit']}
    for v,t in js:
        for h in range(L+mmax):sJ[h]+=v;v*=t
    for v,t,b in ds:
        for h in range(L+mmax):sD['inverse'][h]+=b*v;sD['unit'][h]+=v;v*=t
    tails={model:[] for model in sD}
    for h in range(L+mmax):
        w=K+ell*h;z,zr=a(w).zeta(),a(r*w).zeta()
        for model in tails:
            total=z/zr if model=='inverse' else z*zr;tails[model].append(total-sJ[h]*sD[model][h])
            if h<len(table['moments'][model]):overlap(table['moments'][model][h],total);counts['independent_full_moment_values']+=1
    values={model:{} for model in tails}
    for M in map(Q,points):
        c=a(R)*powq(a(M),r*ell);prefix={model:[flint.arb(0) for _ in range(mmax+1)] for model in tails}
        for basej,tj in js:
            for based,td,b in ds:
                z=c*tj*td;val=basej*based*(-z).exp();step=tj*td
                for m in range(mmax+1):prefix['inverse'][m]+=b*val;prefix['unit'][m]+=val;val*=step
        for m in range(mmax+1):
            scale=a(R).exp()*powq(a(M),r*(K+ell*m));w=K+ell*(m+L);error=scale*c**L*a(w).zeta()*a(r*w).zeta()/factorial(L)
            for model in tails:
                tail=flint.arb(0)
                for h in range(L-1,-1,-1):tail=-c*tail+tails[model][m+h]/factorial(h)
                value=scale*(prefix[model][m]+tail)+flint.arb(0,error);key=f'{m}:{M}'
                overlap(table['values'][model][key],value);values[model][key]=value;counts['independent_complete_rectangle_atoms']+=1
    for row in table['Taylor_error_balls']:
        m,M=row['moment'],Q(row['index_scale']);L0=table['Taylor_terms'];w=K+ell*(m+L0);error=a(R).exp()*powq(a(M),r*(K+ell*m))*(a(R)*powq(a(M),r*ell))**L0*a(w).zeta()*a(r*w).zeta()/factorial(L0)
        overlap(row['error_ball'],error);counts['independent_whole_series_Taylor_bounds']+=1
    assert table['all_infinite_arithmetic_positions_included'] and table['no_finite_lattice_substitution'] and not table['RH_input_used'] and not table['prime_oracle_used']
    return values


def converted_shape(c,params):
    K,ell,r=map(Q,params);R=K/ell
    return {'terms':[[m,str(Q(b)/R**m)] for m,b in c['terms']],'maximum_moment':c['maximum_moment'],'rate':str(R)}
def polynomial(c,params):
    cc=converted_shape(c,params);out=[Q(0)]*(c['maximum_moment']+1)
    for m,b in cc['terms']:
        for (j,h),v in pochhammer(m).items():out[j]+=Q(b)*v
    while len(out)>1 and out[-1]==0:out.pop()
    return out


def residues(p,counts):
    flint.ctx.prec=832;K,ell,r=map(Q,p['parameters']);R=K/ell;P=polynomial(p['shape'],p['parameters']);alpha=(K-1)/ell;value=sum((b*alpha**j for j,b in enumerate(P)),Q(0))
    I=a(R).exp()*powq(a(R),-alpha)*a(alpha).gamma()*a(value)/a(ell);A=I/a(r).zeta() if r!=1 else flint.arb(0)
    saved=p['residues'];assert list(map(Q,saved['Mellin_polynomial']))==P and saved['r_one_main_residue_is_exact_zero']==(r==1)
    overlap(saved['continuous_integral_ball'],I);overlap(saved['actual_main_ball'],A);counts['independent_exact_main_residues']+=1;return I,A


def ledger_check(profile,r):
    r=Q(r);expected={'inverse':{Q(1):1},'unit':{Q(1):1}}[profile['model']];expected[r]=expected.get(r,0)+(-1 if profile['model']=='inverse' else 1)
    assert profile['input_factors']==[['1',1],[str(r),-1 if profile['model']=='inverse' else 1]]
    assert profile['remaining_factors']==[[str(s),n] for s,n in sorted(expected.items()) if n]
    return not any(expected.values())


def bridge_check(p,counts):
    r=Q(p['parameters'][2]);b=p['zero_bridge'];kernel_check(p,counts)
    empty=ledger_check(b['arithmetic_profile'],r);kernel=b['kernel_certificate']['all_right_half_ordinary_zeros_preserved']
    if empty:assert r==1 and b['kind']=='exact_arithmetic_zero_erasure' and not b['RH_sufficient_if_uniform'] and not b['ordinary_zeta_information_preserved'];counts['independent_arithmetic_zero_erasure_rejections']+=1
    elif r<1 and kernel:
        if b['kind']=='finite_division_escape':
            J=b['worst_case_divisions'];assert r**J==Q(b['exact_final_r_power'])<=Q(1,2) and b['RH_sufficient_if_uniform'] and b['all_heights_and_multiplicities']
            if J>1:assert r**(J-1)>Q(1,2)
            for beta in [Q(5,8),Q(3,4),Q(7,8)]:assert beta/r**J>1
            counts['independent_finite_division_RH_bridges']+=1
        else:assert b['kind']=='missing_escape_resource' and not b['RH_sufficient_if_uniform']
    else:assert not b['RH_sufficient_if_uniform']
    assert not b['uniform_critical_estimate_proved'] and not b['sampled_zeta_zeros_used']


def kernel_check(p,counts):
    """A missing finite-box exclusion is valid evidence of missing coverage.

    The frozen checker suffices for exact real/strip certificates. Recheck
    disks here because an unavailable native zeta box can contain its pole.
    Such a box cannot certify zero exclusion, and must not abort discovery.
    """
    cert=p['zero_bridge']['kernel_certificate'];converted=converted_shape(p['shape'],p['parameters'])
    if 'root_disks' not in cert:
        return frozen_root_check({'shape':converted,'parameters':p['parameters'],'zero_bridge':cert},counts)
    flint.ctx.prec=768;K,ell,r=map(Q,p['parameters']);P=polynomial(p['shape'],p['parameters']);H=companion_hermite(P);roots,degree=real_root_count(P)
    assert list(map(Q,cert['Mellin_polynomial']))==P and [[Q(v) for v in row] for row in cert['Hermite_matrix']]==H
    assert not cert['Hermite_factorization']['positive_semidefinite'] and roots<degree
    S=squarefree(P);assert list(map(Q,cert['squarefree_polynomial']))==S;boxes=cert['root_disks'];all_safe=True
    for box in boxes:
        center=flint.acb(a(box['center'][0]),a(box['center'][1]));h=a(box['radius']);coeff=[]
        for j in range(len(S)):coeff.append(sum((a(value)*comb(k,j)*center**(k-j) for k,value in enumerate(S) if k>=j),flint.acb(0)))
        lo=coeff[1].abs_lower()*h;hi=coeff[0].abs_upper()+sum((value.abs_upper()*h**j for j,value in enumerate(coeff) if j>=2),flint.arb(0));assert lo>hi
        recorded_lo=flint.arb(box['Rouche_lower_ball']);recorded_hi=flint.arb(box['Rouche_upper_ball']);norm_lo=abs(coeff[1])*h;norm_hi=abs(coeff[0])+sum((abs(coeff[j])*h**j for j in range(2,len(S))),flint.arb(0))
        assert recorded_lo.lower()<=norm_lo.lower() and recorded_hi.upper()>=norm_hi.upper() and recorded_lo.lower()>recorded_hi.upper()
        rectangle=flint.acb(flint.arb(a(box['center'][0]),h),flint.arb(a(box['center'][1]),h));rho=a(r)*(a(K)-a(ell)*rectangle);cp(box['mapped_ordinary_root_box'],rho)
        outside=bool(rho.real.upper()<=a(Q(1,2)) or rho.real.lower()>=1);assert box['outside_ordinary_strip']==outside;safe=outside
        if not outside:
            zeta=rho.zeta();independent_safe=zeta.is_finite() and zeta.abs_lower()>0
            flint.ctx.prec=cert['native_certificate_precision'];h0=a(box['radius']);rect0=flint.acb(flint.arb(a(box['center'][0]),h0),flint.arb(a(box['center'][1]),h0));zeta0=(a(r)*(a(K)-a(ell)*rect0)).zeta()
            for key,value in [('real',zeta0.real),('imag',zeta0.imag)]:
                recorded=flint.arb(box['native_zeta_box'][key]);assert recorded.is_finite()==value.is_finite()
                if value.is_finite():overlap(box['native_zeta_box'][key],value)
            safe=bool(zeta0.is_finite() and zeta0.abs_lower()>0)
            if zeta0.is_finite():overlap(box['native_zeta_lower_ball'],zeta0.abs_lower())
            else:assert not flint.arb(box['native_zeta_lower_ball']).is_finite()
            if safe:assert independent_safe;counts['independent_native_operator_root_zeta_exclusions']+=1
            else:counts['independent_unavailable_native_operator_root_boxes']+=1
            flint.ctx.prec=768
        assert box['ordinary_zero_excluded']==safe;all_safe &=safe;counts['independent_Rouche_operator_root_disks']+=1
    disjoint=all(flint.acb(a(Q(b['center'][0])-Q(c['center'][0])),a(Q(b['center'][1])-Q(c['center'][1]))).abs_lower()>a(Q(b['radius'])+Q(c['radius'])) for b,c in __import__('itertools').combinations(boxes,2))
    complete=len(boxes)==len(S)-1 and disjoint;assert cert['all_polynomial_roots_covered']==complete and cert['disks_disjoint']==disjoint
    assert cert['all_right_half_ordinary_zeros_preserved']==(complete and all_safe)
    assert not cert['kernel_zero_free_halfplane_required'] and not cert['sampled_zeta_zero_grid_used'] and not cert['counterexample_to_growth_bound'];counts['independent_all_height_operator_bridges']+=1


def global_check(p,res,counts):
    flint.ctx.prec=832;K,ell,r=map(Q,p['parameters']);R=K/ell;gc=p['global_constants'];local=[]
    for m,b in p['shape']['terms']:
        w=K+ell*m;v=a(R).exp()*a(abs(Q(b)))*a(w).zeta()*a(r*w).zeta();local.append((r*w,v))
    for row,(w,v) in zip(gc['local_terms'],local):assert Q(row['power'])==w;overlap(row['coefficient_ball'],v)
    if r==1:assert not gc['global_ordinary_exponent_one_proved'];return None,None,local
    density=a(1/r).zeta()
    def atom(m):
        beta=(K-1/r)/ell+m
        return density*a(R).exp()*powq(a(R),-beta)*a(beta).gamma()*(a(K+ell*m)+a(ell*beta))/a(ell)
    B=sum((a(abs(Q(b)))*atom(m) for m,b in p['shape']['terms']),flint.arb(0));J=sum((a(abs(Q(b)))*(a(K+ell*m)*atom(m)+a(R*ell)*atom(m+1)) for m,b in p['shape']['terms']),flint.arb(0));A=abs(res[1]);weak=B+A;unit=a(r)*(J+A)
    overlap(gc['constant_ball'],weak);overlap(gc['unit_increment_constant_ball'],unit);assert gc['ordinary_exponent']=='1' and gc['global_ordinary_exponent_one_proved'] and not gc['RH_strength'];counts['independent_normalized_weak_and_unit_bounds']+=1
    return weak,unit,local


def rapid_check(p,counts):
    flint.ctx.prec=832;K,ell,r=map(Q,p['parameters']);R=K/ell
    for order,cert in p['rapid_certificates'].items():
        if not cert['global_premise_proved']:assert r!=1 and cert['status']=='missing_signed_profile_collapse';continue
        assert ledger_check(cert['profile_certificate'],r) and r==1 and cert['arithmetic_model']=='inverse' and not cert['RH_consequence'] and not cert['ordinary_zeta_information_preserved']
        C=flint.arb(0)
        for m,b in p['shape']['terms']:
            alpha=(K+Q(order))/ell+m;v=a(R).exp()*a(abs(Q(b)))*powq(a(R),-alpha)*powq(a(alpha),alpha)*(-a(alpha)).exp();C+=v
        overlap(cert['constant_ball'],C);assert cert['all_real_positive_scales'];counts['independent_signed_actual_global_rapid_certificates']+=1


def pole_check(p,counts):
    flint.ctx.prec=832;K,ell,r=map(Q,p['parameters']);R=K/ell;P=polynomial(p['shape'],p['parameters']);v=(K-1/r)/ell;pv=sum((c*v**j for j,c in enumerate(P)),Q(0));saved=p['late_tail_pole']
    assert saved['applies']==bool(pv)
    if pv:
        top=a(R).exp()*powq(a(R),-v)*a(v).gamma()*a(pv)/a(ell*r)
        if r!=1:top*=a(1/r).zeta()
        overlap(saved['leading_coefficient_ball'],top);assert abs(top)>0 and saved['pole_order']==(2 if r==1 else 1) and saved['globally_false_at_ordinary_limit_half'] and not saved['counterexample_to_actual_growth'];counts['independent_uncancelled_late_tail_poles']+=1


def observations(p,values,points,saved,res,counts):
    K,ell,r=map(Q,p['parameters']);R=K/ell;out={}
    for M in map(Q,points):
        raw={model:sum((a(c)*values[model][f'{m}:{M}'] for m,c in p['shape']['terms']),flint.arb(0)) for model in ['inverse','unit']}
        if p['arithmetic_backend']=='certified_single_support':
            assert r==1; y=powq(a(M),ell);direct=powq(a(M),K)*(a(R)*(1-y)).exp()*sum((a(c)*y**m for m,c in p['shape']['terms']),flint.arb(0));assert direct.overlaps(raw['inverse']);raw['inverse']=direct;counts['independent_compiled_support_equivalence_checks']+=1
        row={'actual_raw_ball':raw['inverse'],'actual_centered_ball':raw['inverse']-res[1]*powq(a(M),r),'unit_raw_ball':raw['unit']}
        for name,v in row.items():overlap(saved[str(M)][name],v);counts['independent_actual_and_unit_observations']+=1
        out[str(M)]=row
    return out


@lru_cache(maxsize=None)
def env0(eta,margin,nu,d,q,M):return powq(a(M),Q(eta))*((a(margin)/powq(a(q),Q(nu)))*a(M).log()).exp()*powq((flint.arb.const_e()+a(M)).log(),Q(d))
def env(f,q,M):return env0(f['limit'],f['margin'],f['approach_power'],f['log_power'],q,str(M))


def constants_check(rows,f,qs,Cs,spec,counts):
    flint.ctx.prec=832;D=int(spec['constant_rule']['upward_denominator']);margin=a(spec['constant_rule']['training_margin'])
    for q in qs:
        vals=[abs(flint.arb(row['actual_centered_ball']))/env(f,q,M) for M,row in rows.items()];top=max(vals,key=lambda v:float(v.upper()));uncert=max((v.rad() for v in vals),key=float);got=a(Cs[str(q)]);assert got>0 and abs(got-margin*top)<=4*margin*uncert+a(Q(4,D));counts['independent_training_only_constants']+=1


def comparisons(rows,f,Cs,qs,old,counts):
    flint.ctx.prec=832;bad=[];unresolved=[];worst=0
    for q in qs:
        for M,row in rows.items():
            V=abs(row['actual_centered_ball']);B=a(Cs[str(q)])*env(f,q,M)
            if not V<=B:(bad if V>B else unresolved).append(f'{q}:{M}')
            worst=max(worst,float((V/B).upper()));counts['independent_finite_inequalities']+=1
    assert old['failures']==bad and old['unresolved']==unresolved and old['finite_points_passed']==(not bad and not unresolved) and abs(old['maximum_ratio']-worst)<1e-10*max(1,worst)


@lru_cache(maxsize=None)
def observer(params,query):
    K,ell,r=map(Q,params);sig,t=map(Q,query);R=K/ell;s=flint.acb(a(sig/r),a(t/r));v=(a(K)-s)/a(ell)
    return v,a(R).exp()*v.gamma()*(-v*a(R).log()).exp()/a(ell*r),s.zeta().abs_lower()


def cost_check(p,c,Cs,qs,saved,res,gc,spec,counts):
    if Q(c['frontier']['limit'])!=Q(1,2):assert saved['best_log_cost'] is None;return
    if not p['zero_bridge']['RH_sufficient_if_uniform']:assert saved['status']=='missing_ordinary_zeta_recovery';return
    flint.ctx.prec=832;K,ell,r=map(Q,p['parameters']);sig,t=map(Q,spec['cost_query']);z=flint.acb(a(sig),a(t));v,base,numerator=observer(tuple(p['parameters']),tuple(spec['cost_query']));P=polynomial(p['shape'],p['parameters']);W=base*sum((a(c)*v**j for j,c in enumerate(P)),flint.acb(0));denom=W.abs_lower()
    if not denom>0 or not numerator>0:assert saved['status']=='observer_transform_or_numerator_zero';return
    weak,J,localterms=gc;local=sum((value/a(power-sig) for power,value in localterms),flint.arb(0));pole=abs(res[1])/(z-a(r)).abs_lower();unit=J/a(sig);f=c['frontier'];d=ceil(Q(f['log_power']));L0=(flint.arb.const_e()+1).log();costs=[]
    for q,row in zip(qs,saved['observers']):
        gap=a(sig)-a(f['limit'])-a(f['margin'])/powq(a(q),Q(f['approach_power']));overlap(row['gap_ball'],gap);assert row['q']==q
        if not gap>0:assert row['status']=='outside_observer_domain';continue
        integral=sum((a(comb(d,j))*L0**(d-j)*factorial(j)/gap**(j+1) for j in range(d+1)),flint.arb(0));cost=(local+pole+unit+a(Cs[str(q)])*integral)/denom/numerator
        for key,val in [('local_cost_ball',local),('pole_cost_ball',pole),('unit_cost_ball',unit),('transform_denominator_lower_ball',denom),('numerator_zeta_lower_ball',numerator),('conditional_reciprocal_bound_ball',cost)]:overlap(row[key],val)
        cp(row['transform_ball'],W);assert abs(row['log_cost']-float(cost.upper().log()))<1e-10 and not row['uniform_critical_premise_proved'];costs.append(row['log_cost']);counts['independent_charged_root_observers']+=1
    assert saved['best_log_cost']==min(costs,default=None)


def relation_check(records,discovery,spec,counts):
    for record in records:
        rel=record['relation'];values=discovery['tables'][record['parameter_id']]['moments'][record['decoded_model_after_fit']][:spec['moment_relation']['total_count']]
        if rel['coefficients'] is None:assert rel['status']=='rank_deficient' and not record['universal_certificate_admitted'];continue
        coeff=list(map(Q,rel['coefficients']));k=rel['order'];assert len(coeff)==k+1 and coeff[-1]==1
        def residual(indices):return max((float(abs(sum((a(c)*flint.arb(values[h+j]) for j,c in enumerate(coeff)),flint.arb(0))).upper()) for h in indices),default=0)
        train=residual(range(spec['moment_relation']['training_count']-k));val=residual(range(spec['moment_relation']['training_count'],len(values)-k));tol=float(Q(spec['moment_relation']['tolerance']));assert abs(train-rel['training_residual'])<1e-10 and abs(val-rel['validation_residual'])<1e-10
        assert rel['training_passed']==(train<=tol) and rel['validation_passed']==(val<=tol)
        if record['universal_certificate_admitted']:
            assert record['proof_certificate']['model']==record['decoded_model_after_fit']
            assert ledger_check(record['proof_certificate'],discovery['tables'][record['parameter_id']]['parameters'][2]) and sum(coeff)==0
            counts['independent_universal_inferred_moment_relations']+=1
        else:assert record['numeric_only_if_no_certificate']
        counts['independent_inferred_moment_relations']+=1


def check(d):
    spec=read(d/'protocol.json');seal=read(d/'seal.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');final=read(d/'final_evaluation.json');cases=read(d/'final_cases.json');pc=read(d/'parameter_cases.json');cal=read(d/'parameter_calibration.json');cs=read(d/'calibration_seal.json');checks={};counts=defaultdict(int)
    def passed(name):checks[name]=True;print('Verified',name,flush=True)
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    for dep in spec['named_calibration_dependencies']:assert sha(dep['path'])==dep['sha256']
    source=Path(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    from lattice_synthesis_report import summary as parent
    parent(source);passed('frozen_source_and_verified_parent_provenance')
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist_at_seal'] and not seal['parameter_cases_exist_at_seal'] and arc['selection_closed'] and not arc['final_data_used']
    assert batch['frozen_before_validation'] and batch['generation_uses_training_only'] and pc['seal_sha256']==sha(d/'seal.json') and cal['parameters_sha256']==digest(pc) and cal['training_only'] and not cal['final_scales_used']
    for key,n in [('archive_seal_sha256','seal.json'),('parameter_cases_sha256','parameter_cases.json'),('parameter_calibration_sha256','parameter_calibration.json')]:assert cs[key]==sha(d/n)
    assert not cs['final_cases_exist_at_calibration_seal'] and cases['generated_after_calibration_seal'] and cases['calibration_seal_sha256']==digest(cs)
    assert final['cases_sha256']==digest(cases) and final['protocol_sha256']==digest(spec) and final['seal_sha256']==digest(seal) and final['calibration_seal_sha256']==digest(cs)
    assert not set(cases['integers'])&set(spec['parent_final_scales_excluded']) and not set(pc['fresh_q'])&set(spec['training_q']+spec['validation_new_q']+spec['parent_final_q_excluded'])
    for old in spec['retained_failed_runs_are_development']:
        fd=Path(old['run_directory']);assert sha(fd/'failure.json')==old['failure_sha256']
        for n,h in old['retained_files_sha256'].items():assert sha(fd/n)==h
        fs=read(fd/'protocol.json');assert fs['code_sha256']==old['original_code_sha256']
        for n in fs['this_stage_source_files']:assert sha(fd/'frozen_source'/n)==fs['code_sha256'][n]
        assert not set(cases['integers'])&set(old['excluded_final_scales']) and not set(pc['fresh_q'])&set(old['excluded_final_q'])
    passed('archive_fresh_parameter_calibration_and_final_scale_isolation')
    discovery=read(d/'discovery_data.json');validation=read(d/'validation_data.json')
    for denial in [discovery['worker_access_denials'],cal['worker_access_denials']]:assert len(denial)==6 and all(denial.values())
    assert not read(d/'source_forms.json')['prior_outcomes_supplied'];passed('worker_model_literature_outcome_network_and_final_access_denied')
    independent={}
    for name,data,points in [('training',discovery,spec['training_points']),('validation',validation,spec['validation_points']),('final',final['data'],cases['index_points'])]:
        independent[name]={i:rectangular_table(t,points,counts) for i,t in data['tables'].items()};assert data['all_infinite_arithmetic_positions_included']
    passed('independent_rectangle_actual_mu_and_complete_root_moments')
    ps={p['id']:p for p in batch['ablation_programs']+batch['programs']};res={};globals={}
    for i,p in ps.items():
        assert p['semantic_operator_id']==digest({'shape':p['shape'],'parameters':p['parameters']}) and p['id']==digest({'semantic_operator_id':p['semantic_operator_id'],'backend':p['arithmetic_backend']})
        terms=p['shape']['terms'];assert max(abs(Q(c)) for m,c in terms)==1 and Q(terms[-1][1])>0 and p['shape']['maximum_moment']==max(m for m,c in terms)
        res[i]=residues(p,counts);globals[i]=global_check(p,res[i],counts)
    passed('normalized_exact_main_poles_and_true_weak_unit_bounds')
    for p in ps.values():bridge_check(p,counts)
    passed('all_height_kernel_preservation_finite_zero_escape_and_arithmetic_erasure')
    for p in ps.values():rapid_check(p,counts);pole_check(p,counts)
    passed('signed_actual_global_profile_collapse_and_late_tail_pole_certificates')
    relation_check(batch['moment_relations'],discovery,spec,counts)
    for promotion in batch['arithmetic_promotions']:
        assert promotion['relation']['universal_certificate_admitted'] and promotion['relation']['decoded_model_after_fit']=='inverse' and promotion['preserves_all_scale_semantics'] and not promotion['RH_information_retained']
    compiled_contexts={promotion['parameter_id'] for promotion in batch['arithmetic_promotions']}
    for p in batch['programs']:
        assert (p['arithmetic_backend']=='certified_single_support')==(p['parameter_id'] in compiled_contexts)
    for promotion in batch['shape_promotions']:
        parent=ps[promotion['parent_id']];K,ell,r=map(Q,parent['parameters']);R=K/ell;lam=Q(promotion['lambda']);terms=defaultdict(Q)
        for m,value in parent['shape']['terms']:terms[m]+=(m-lam)*Q(value);terms[m+1]-=R*Q(value)
        terms={m:value for m,value in terms.items() if value};scale=max(map(abs,terms.values()));orientation=1 if terms[max(terms)]>0 else -1
        exact=[[m,str(orientation*value/scale)] for m,value in sorted(terms.items())]
        assert promotion['shape']['terms']==exact and promotion['admitted']==(max(terms)<=spec['maximum_moment'])
        counts['independent_exact_Euler_promotions']+=1
    assert len(batch['shape_promotions'])==spec['promotion_slots']*len(spec['parameters'])==arc['ablation_comparison']['proposal_slots']
    passed('anonymous_moment_relations_and_exact_arithmetic_grammar_promotion')
    native_obs={}
    for name,points,saved in [('training',spec['training_points'],batch['training_observables']),('validation',spec['validation_points'],validation['program_observables']),('final',cases['index_points'],final['program_observables'])]:
        native_obs[name]={i:observations(ps[i],independent[name][ps[i]['parameter_id']],points,rows,res[i],counts) for i,rows in saved.items()}
    passed('complete_actual_responses_and_compiled_signed_support_equivalence')
    validated={c['id']:c for c in validation['candidates']};candidates={c['id']:c for c in batch['candidates']}
    for c in batch['candidates']:
        p=ps[c['program_id']];f=c['frontier'];assert not f['constants_in_q_restricted'] and not f['finite_q_grid_suffices'] and Q(f['approach_power'])>0
        core={k:c[k] for k in ['program_id','frontier','constants']};assert c['id']==digest(core)
        rapid=Q(p['parameters'][2])==1;weak=Q(f['limit'])>=1 and globals[p['id']][0] is not None
        assert c['uniform_frontier_has_proved_constant_witness']==(rapid or weak) and c['RH_sufficient_if_uniform']==(Q(f['limit'])==Q(1,2) and p['zero_bridge']['RH_sufficient_if_uniform'])
        constants_check(batch['training_observables'][p['id']],f,spec['training_q']+spec['validation_new_q'],c['constants'],spec,counts)
        comparisons(native_obs['validation'][p['id']],f,c['constants'],spec['training_q']+spec['validation_new_q'],validated[c['id']]['validation'],counts)
        cost_check(p,c,c['constants'],spec['training_q'],c['recovery_cost'],res[p['id']],globals[p['id']],spec,counts)
    passed('free_cofinal_frontiers_training_only_constants_and_fully_charged_observers')
    calibrated={row['candidate_id']:row['constants'] for row in cal['illustrative_free_constants']};fresh=pc['fresh_q']
    for i,Cs in calibrated.items():constants_check(batch['training_observables'][candidates[i]['program_id']],candidates[i]['frontier'],fresh,Cs,spec,counts)
    for o in final['outcomes']:
        c=candidates[o['candidate_id']];p=ps[c['program_id']];Cs={**c['constants'],**calibrated[c['id']]};qs=spec['training_q']+spec['validation_new_q']+fresh;assert o['constants']==Cs
        comparisons(native_obs['final'][p['id']],c['frontier'],Cs,qs,o,counts);cost_check(p,c,Cs,qs,o['recovery_cost'],res[p['id']],globals[p['id']],spec,counts)
    passed('fresh_q_constants_sealed_before_complete_fresh_arithmetic_scales')
    for o in final['late_tail_controls']:
        c=candidates[o['candidate_id']];p=ps[c['program_id']];K,ell,r=map(Q,p['parameters']);R=K/ell;fake={};Bpower=spec['counterfeit_cutoff_binary_power']
        for M,row in native_obs['final'][p['id']].items():
            bound=sum((a(abs(Q(c0)))*a(R).exp()*powq(a(M),r*(K+ell*m))*a(K+ell*m).zeta()*((a(1-r*(K+ell*m))*Bpower)*a(2).log()).exp()/a(r*(K+ell*m)-1) for m,c0 in p['shape']['terms']),flint.arb(0))
            fake[M]=dict(row,actual_centered_ball=row['actual_centered_ball']+flint.arb(0,bound));overlap(o['fake_observables'][M]['actual_centered_ball'],fake[M]['actual_centered_ball']);counts['independent_full_late_tail_enclosures']+=1
        Cs={**c['constants'],**calibrated[c['id']]};comparisons(fake,c['frontier'],Cs,spec['training_q']+spec['validation_new_q']+fresh,o,counts)
        assert p['late_tail_pole']['applies'] and o['globally_false_uniform_target'] and not o['actual_arithmetic_counterexample']
    passed('invisible_full_counterfeit_tails_rejected_by_their_uncancelled_poles')
    for o in final['zero_erasure_controls']:
        p=ps[candidates[o['candidate_id']]['program_id']];assert Q(p['parameters'][2])==1 and o['actual_uniform_frontier_proved'] and o['false_RH_inference_rejected'] and o['arithmetic_erases_ordinary_zeros'] and not p['zero_bridge']['RH_sufficient_if_uniform']
    passed('true_signed_all_scale_control_does_not_imply_RH_when_zeta_is_erased')
    for row in final['signed_rapid_witnesses']:
        p=ps[row['program_id']];C=flint.arb(p['rapid_certificates'][row['order']]['constant_ball'])
        for M,v in native_obs['final'][p['id']].items():assert abs(v['actual_centered_ball'])<=C*powq(a(M),-Q(row['order']));counts['independent_signed_rapid_fresh_witnesses']+=1
        assert row['actual_inverse_arithmetic'] and not row['RH_consequence']
    for i,rows in native_obs['final'].items():
        if globals[i][0] is None:continue
        B,J,local=globals[i]
        for M,row in rows.items():assert abs(row['actual_centered_ball'])<=B*a(M);counts['independent_weak_global_bound_witnesses']+=1
        for M in cases['integers']:assert abs(rows[str(Q(M)+Q(spec['final_cases']['offset']))]['actual_centered_ball']-rows[str(M)]['actual_centered_ball'])<=J*a(spec['final_cases']['offset']);counts['independent_normalized_unit_increment_witnesses']+=1
    passed('fresh_signed_rapid_weak_and_normalized_unit_increment_witnesses')
    with tempfile.TemporaryDirectory(prefix='root-lattice-replay-') as td:
        t=Path(td);put(t/'protocol.json',spec);put(t/'source_forms.json',read(d/'source_forms.json'));subprocess.run([sys.executable,str(BASE/'root_lattice_search.py'),'worker','--run-dir',str(t)],check=True,cwd=BASE);replay={n:sha(t/n) for n in seal['files']};assert replay==seal['files']
    passed('deterministic_isolated_learning_promotion_ablation_and_archive_replay')
    assert spec['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[] and not final['RH_proved']
    passed('RH_completion_requires_actual_signed_control_with_ordinary_zero_recovery')
    result={'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_root_lattices.py'),'final_sha256':sha(d/'final_evaluation.json'),'checks':checks,'all_passed':all(checks.values()),
        'counts':dict(counts),'replay_sha256':replay,'mathematical_audit_imports_production_code':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,'machine_formalized':False}
    put(d/'verification.json',result);print('Independent verification',len(checks),'/',len(checks),flush=True);return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);args=p.parse_args();check(args.run_dir.resolve())
if __name__=='__main__':main()
