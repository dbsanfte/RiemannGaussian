#!/usr/bin/env python3
"""Independent full prime arithmetic, kernels, primitive products and proof scope."""
import argparse,subprocess,sys,tempfile
from pathlib import Path
from fractions import Fraction as Q
from math import gcd
import flint
from stable_scale_report import BASE,read,sha,digest
from check_signed_control import independent_inverse
from check_divisor_preconditioners import factors
from check_mellin_kernels import a,put,tight_overlap


def density(k):
    out=1/a(2).zeta();tau=1
    for p,e in factors(k):out*=a(p)/a(p+1);tau*=2
    return out,tau


def W(X,n):
    if n<=X:return -2*X
    if n<=2*X:return 4*n-6*X
    return max(0,4*X-n)


def whole(mu,M,X):
    A=sum(M[n]**2 for n in range(X,2*X));child=sum(M[n]**2 for n in range(2*X,4*X));D=sum(mu[n]**2*(2*X-max(X,n)) for n in range(1,2*X));D2=sum(mu[n]**2*(4*X-max(2*X,n)) for n in range(1,4*X))
    return {'X':X,'energy':A,'child_energy':child,'diagonal':D,'child_diagonal':D2,'signed_defect':child-4*A,'diagonal_defect':D2-4*D,'off_diagonal_defect':child-4*A-D2+4*D}


def power(X,p):return (a(Q(p))*a(X).log()).exp()


def audit_data(data,candidates,counts):
    mu,M=independent_inverse(data['cutoff']);assert mu==data['complete_coefficient_prefix'] and digest(mu)==data['divisor_inverse_sha256'] and not data['producer_prime_or_factor_oracle_used'];counts['full_independent_prime_inverse_coefficients']+=data['cutoff'];T=a(8).sqrt();J=a(Q(2,3))*(T-1);diag=3*J*(T+4);C0=6*J*(T+4)
    for row in data['rows']:
        X=row['whole']['X'];exact=whole(mu,M,X);assert row['whole']==exact;assert abs(exact['diagonal_defect'])<=diag*a(X)*a(X).sqrt();grid=row['projection_grid'];geometries=grid['primitive_geometries'];Bmax=max(r['shared_cutoff'] for r in grid['cutoff_rows']);expected={(s,r) for r in range(2,Bmax+1) for s in range(1,r) if gcd(s,r)==1 and mu[s]*mu[r]};assert {(g['a'],g['r']) for g in geometries}==expected
        for geo in geometries:
            s,r=geo['a'],geo['r'];k=s*r;local=0;number=0;c,tau=density(k);tight_overlap(geo['density_ball'],c);assert tau==geo['tau_radical']
            for common in range(1,4*X//r+1):
                lhs=mu[common*s]*mu[common*r];rhs=mu[s]*mu[r]*mu[common]**2*int(gcd(common,k)==1);assert lhs==rhs;counts['independent_primitive_prime_product_identities']+=1;w=W(X,common*r)
                if w:local+=2*rhs*w;number+=1
            assert local==geo['exact_signed_defect'] and number==geo['counted_geometries']
        for c in grid['cutoff_rows']:
            B=c['shared_cutoff'];subset=[g for g in geometries if g['r']<=B];projection=sum(g['exact_signed_defect'] for g in subset);cost=sum(((g['tau_radical']+2)/a(g['r']).sqrt() for g in subset),flint.arb(0));leading=sum((3*mu[g['a']]*mu[g['r']]*density(g['a']*g['r'])[0]/g['r'] for g in subset),flint.arb(0));bound=2*J*(T+4)*cost*a(X)*a(X).sqrt();coarse=C0*a(X*B)*a(X*B).sqrt()*(1+a(B).log())**2
            assert c['signed_projection_defect']==projection and c['primitive_geometry_count']==len(subset);tight_overlap(c['positive_density_cost_ball'],cost);tight_overlap(c['leading_coefficient_ball'],leading);tight_overlap(c['sharp_component_bound_ball'],bound);tight_overlap(c['coarse_component_bound_ball'],coarse)
            assert cost<=3*a(B)*a(B).sqrt()*(1+a(B).log())**2 and abs(projection)<=bound and bound<=coarse and c['all_scale_component_proved'] and not c['full_defect_bound_proved'];counts['all_scale_component_bound_witnesses']+=1
        for p,o in zip(candidates,row['candidate_observations']):
            assert o['candidate_id']==p['id'];beta=Q(p['beta']);B=o.get('semantic_cutoff') if o['missing'] else o['shared_cutoff']
            if B is not None:assert B**beta.denominator<=X**beta.numerator<(B+1)**beta.denominator
            if o['missing']:assert o['missing_not_counterexample'];continue
            c=next(c for c in grid['cutoff_rows'] if c['shared_cutoff']==B);residual=exact['off_diagonal_defect']-c['signed_projection_defect'];assert o['signed_projection_defect']==c['signed_projection_defect'] and o['signed_dense_residual_defect']==residual and o['whole_defect_reconstructed']==exact['signed_defect'];counts['exact_retained_dense_signed_residuals']+=1
        counts['whole_signed_energy_and_diagonal_defects']+=1
    return mu,M


def audit_estimates(data,estimates,candidates):
    for e in estimates:
        p=next(p for p in candidates if p['id']==e['candidate_id']);assert Q(3,2)*(1+Q(p['beta']))<=2 and not e['uniform_residual_premise_proved'] and e['finite_fit_is_not_full_defect_certificate'];ratios=[]
        for row in data['rows']:
            o=next(o for o in row['candidate_observations'] if o['candidate_id']==p['id'])
            if not o['missing']:ratios.append(float((a(max(o['signed_dense_residual_defect'],0))/(a(Q(e['constant']))*power(row['whole']['X'],2+Q(e['epsilon'])))).upper()))
        if 'maximum_finite_ratio'in e:
            value=max(ratios,default=None);assert value is None and e['maximum_finite_ratio'] is None or value is not None and abs(value-e['maximum_finite_ratio'])<=max(1,value)*2**-45;assert e['finite_pass']==(bool(ratios) and max(ratios)<=1)


def check(d):
    spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');validation=read(d/'validation.json');arc=read(d/'archive.json');seal=read(d/'seal.json');cases=read(d/'final_cases.json');final=read(d/'final_evaluation.json');checks={};counts={'full_independent_prime_inverse_coefficients':0,'independent_primitive_prime_product_identities':0,'all_scale_component_bound_witnesses':0,'exact_retained_dense_signed_residuals':0,'whole_signed_energy_and_diagonal_defects':0}
    def passed(name):checks[name]=True;print('Verified',name,flush=True)
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    from branch_center_report import summary as parent
    parent(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/n)==h
    assert seal['protocol_sha256']==digest(spec) and batch['protocol_sha256']==digest(spec) and all(batch['access_denials'].values()) and cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json') and final['cases_sha256']==digest(cases)
    for f in spec['retained_failed_runs_are_development']:
        p=Path(f['run_directory']);assert sha(p/'failure.json')==f['failure_sha256']
        for n,h in f['files_sha256'].items():assert sha(p/n)==h
        assert not set(cases['scales'])&set(f['excluded_final_scales'])
    passed('frozen_target_sources_isolated_worker_and_fresh_final_cases')
    candidates=batch['candidates'];powers=sorted({Q(n,k) for k in spec['cutoff_grammar_denominators'] for n in range(k+1)});assert [Q(p['beta']) for p in candidates]==powers
    for p in candidates:
        cert=p['certificate'];b=Q(p['beta']);assert p['id']==digest({'beta':str(b)}) and cert['admitted'] and Q(cert['component_power'])==Q(3,2)*(1+b) and cert['component_admits_every_positive_epsilon_critical_bound']==(Q(3,2)*(1+b)<=2) and not cert['global_full_signed_defect_proved'] and cert['dense_residual_still_required']
    selected=next(p for p in candidates if p['id']==arc['selected_component_candidate_id']);admitted=[p for p in candidates if p['certificate']['component_admits_every_positive_epsilon_critical_bound']];assert selected==max(admitted,key=lambda p:(Q(p['beta']),p['id']))
    assert arc['cofinal_recovery_certificate']['admitted'] and arc['cofinal_recovery_certificate']['all_heights_and_offcritical_multiplicities'] and not arc['cofinal_recovery_certificate']['critical_zero_simplicity_required'] and not arc['cofinal_recovery_certificate']['global_signed_defect_premise_proved'];passed('cofinal_RH_defect_quantifiers_and_exact_component_frontier_scope')
    flint.ctx.prec=768;audit_data(batch['training'],candidates,counts);passed('independent_complete_training_arithmetic_primitive_products_diagonal_and_residual')
    audit_data(validation['data'],candidates,counts);passed('independent_complete_validation_arithmetic_and_every_component_bound')
    mu,M=audit_data(final['data'],candidates,counts);passed('independent_fresh_full_prime_arithmetic_signed_defects_and_unremoved_dense_residual')
    for row in final['density_observations']:
        k=row['modulus'];y=Q(row['y']);c,tau=density(k);tight_overlap(row['density_ball'],c);tight_overlap(row['bound_ball'],(tau+2)*a(y).sqrt());count=sum(mu[n]**2 for n in range(1,y.numerator//y.denominator+1) if gcd(n,k)==1);assert count==row['count'] and tau==row['tau_radical'] and abs(a(count)-c*a(y))<=(tau+2)*a(y).sqrt()
    counts['coprime_squarefree_density_bound_witnesses']=len(final['density_observations']);passed('uniform_coprime_squarefree_density_at_fresh_moduli_and_fractional_scales')
    audit_estimates(batch['training'],batch['residual_estimates'],candidates);audit_estimates(validation['data'],validation['estimates'],candidates);audit_estimates(final['data'],final['residual_estimate_evaluations'],candidates)
    for e in batch['residual_estimates']:
        values=[]
        for row in batch['training']['rows']:
            o=next(o for o in row['candidate_observations'] if o['candidate_id']==e['candidate_id'])
            if not o['missing']:values.append(a(max(o['signed_dense_residual_defect'],0))/power(row['whole']['X'],2+Q(e['epsilon'])))
        target=max(values,key=lambda v:float(v.upper()))*a(Q(5,4));saved=a(Q(e['constant']));assert saved>=target.lower() and saved<=target.upper()+a(Q(2,2**64))
    passed('one_sided_fitted_residual_constants_and_fresh_finite_results_not_global_proofs')
    positive=[0]+[1]*(len(mu)-1);pm=[0]
    for x in positive[1:]:pm.append(pm[-1]+x)
    for row in final['positive_coefficient_controls']:
        X=row['whole']['X'];B=row['shared_cutoff'];assert row['whole']==whole(positive,pm,X) and row['whole']['signed_defect']==Q(28*X**3-X,3)==Q(row['analytic_full_defect_formula']);terms=0;pairs=0
        for r in range(2,B+1):
            count=sum(gcd(s,r)==1 for s in range(1,r));pairs+=count;terms+=2*count*sum(W(X,r*g) for g in range(1,4*X//r+1))
        assert terms==row['projection']['signed_defect'] and row['projection']['all_scale_absolute_defect_upper']==12*X*pairs and abs(terms)<=12*X*pairs
    passed('controlled_positive_projection_with_analytic_power_three_full_defect_counterexample')
    tail=final['delayed_tail_starts_after'];fake=mu[:tail+1]+[1]*(len(mu)-tail-1);fm=[0]
    for x in fake[1:]:fm.append(fm[-1]+x)
    for row in final['delayed_tail_controls']:assert row==whole(fake,fm,row['X'])
    assert fake[:tail+1]==mu[:tail+1] and any(fake[n]!=mu[n] for n in range(tail+1,len(mu))) and all(final['negative_controls'].values());passed('delayed_counterfeit_arithmetic_and_cutoff_cofinality_oracle_aliases_rejected')
    assert not final['global_full_signed_defect_proved'] and not final['RH_proved'] and spec['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==arc['uniform_RH_sufficient_signed_controls_verified']==[]
    with tempfile.TemporaryDirectory(prefix='critical-defect-replay-') as td:
        p=Path(td);put(p/'protocol.json',spec);subprocess.run([sys.executable,str(BASE/'critical_defect_search.py'),'worker','--run-dir',str(p)],cwd=BASE,check=True);replay={n:sha(p/n) for n in seal['files']};assert replay==seal['files']
    passed('exact_isolated_component_selection_and_residual_fit_replay')
    result={'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_critical_defects.py'),'final_sha256':sha(d/'final_evaluation.json'),'checks':checks,'counts':counts,'all_passed':all(checks.values()),'replay_sha256':replay,
        'mathematical_audit_imports_production_code':False,'machine_formalized':False,'full_signed_defect_bound_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False};put(d/'verification.json',result);print('Independent critical-defect verification',len(checks),'/',len(checks),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);check(p.parse_args().run_dir.resolve())
