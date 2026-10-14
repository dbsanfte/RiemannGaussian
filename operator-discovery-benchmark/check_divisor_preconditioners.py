#!/usr/bin/env python3
"""Independent factor arithmetic, contour constants and every-scale certificates."""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,comb
from pathlib import Path
import argparse,subprocess,sys,tempfile
import flint
from stable_scale_report import BASE,read,sha,digest
from check_mellin_kernels import a,powq,put,tight_overlap


def factors(n):
    out=[];p=2
    while p*p<=n:
        if n%p==0:
            e=0
            while n%p==0:n//=p;e+=1
            out.append((p,e))
        p+=1
    if n>1:out.append((n,1))
    return out


def mu(n):
    f=factors(n)
    return 0 if any(e>1 for p,e in f) else (-1)**len(f)


def prime_difference(order,n):
    f=factors(n)
    if not f:return flint.arb(0)
    out=flint.arb(0)
    for mask in range(1<<len(f)):
        divisor=1
        for j,(p,e) in enumerate(f):
            if mask>>j&1:divisor*=p
        v=a(n//divisor).log();out+=(-1)**mask.bit_count()*(powq(v,Q(order)) if n//divisor>1 else flint.arb(0))
    return out


def arithmetic(table,counts):
    flint.ctx.prec=table['precision']+192;values=[flint.arb(0)];order=Q(table['order'])
    assert order>0 and table['all_positive_rational_orders_supported'] and table['complete_finite_arithmetic'] and not table['prime_or_factor_oracle_used']
    for n in range(1,table['cutoff']+1):
        assert table['mu'][n]==mu(n);value=prime_difference(order,n);tight_overlap(table['values'][n],value);values.append(value);counts['independent_complete_prime_difference_coefficients']+=1
    return values


@lru_cache(maxsize=None)
def contour_gammas(K):
    flint.ctx.prec=832;eps=a(Q(1,2**200));corners=[flint.acb(a(Q(3,4)),a(Q(-1,4))),flint.acb(a(Q(5,4)),a(Q(-1,4))),flint.acb(a(Q(5,4)),a(Q(1,4))),flint.acb(a(Q(3,4)),a(Q(1,4)))];out=[]
    for j in range(K):
        v=flint.acb(0)
        for left,right in zip(corners,corners[1:]+corners[:1]):
            v+=flint.acb.integral(lambda z,analytic:(z.zeta()-1/(z-1))/(z-1)**(j+1),left,right,abs_tol=eps,rel_tol=eps,depth_limit=40,eval_limit=200000)
        value=v/flint.acb(0,2*flint.arb.pi());assert value.is_finite() and value.imag.contains(0);out.append((-1)**j*factorial(j)*value.real)
    return out


def certificate(cert,counts):
    flint.ctx.prec=832;k=cert['order'];G=contour_gammas(k)
    for saved,value in zip(cert['gamma_constants'],G):tight_overlap(saved,value);counts['independent_contour_harmonic_constants']+=1
    H=[]
    for r in range(k):
        row=[flint.arb(0) for _ in range(k+1)];row[r+1]=a(Q(1,r+1))
        for j in range(r+1):row[r-j]+=(-1)**j*comb(r,j)*G[j]
        H.append(row)
    P=[flint.arb(c) for c in cert['polynomial_coefficients']];b=flint.arb(cert['constant_term']);assert len(P)==k
    # Substitute the recorded polynomial into every coefficient constraint.
    for j in range(k+1):
        value=sum((P[r]*H[r][j] for r in range(k)),flint.arb(0))+(b if j==0 else 0);target=a((-1)**(k-j)*Q(factorial(k),factorial(j)))
        assert value.overlaps(target)
    # Independent Laurent inversion of (-1)^k*zeta^(k)/(s*zeta).
    # The analytic numerator contributes no principal part after division.
    Z=[flint.arb(1)]+[(-1)**j*G[j]/factorial(j) for j in range(k)]
    A=[Z[j]+(Z[j-1] if j else 0) for j in range(k)];inverse=[flint.arb(1)]
    for j in range(1,k):inverse.append(-sum((A[h]*inverse[j-h] for h in range(1,j+1)),flint.arb(0)))
    for r in range(k):
        assert P[r].overlaps(factorial(k)*inverse[k-r-1]/factorial(r));counts['independent_full_Mellin_principal_coefficients']+=1
    B=[Q(2*factorial(j))*sum((Q(1,factorial(h)) for h in range(j+1)),Q(0)) for j in range(k)];C=[sum((comb(r,j)*B[j] for j in range(r+1)),Q(0)) for r in range(k)]
    assert list(map(Q,cert['harmonic_error_constants']))==B and list(map(Q,cert['dilated_harmonic_error_constants']))==C
    bound=a(factorial(k)+1)+abs(b)+sum((abs(P[r])*a(C[r]) for r in range(k)),flint.arb(0));assert a(cert['residual_constant'])>bound
    J=sum(comb(k,j)*factorial(j) for j in range(k+1));assert cert['divisor_norm_constant']==2*J and cert['signed_error_constant']==2*J*cert['residual_constant']
    assert cert['arithmetic_model']=='inverse_one' and cert['actual_mobius_remainder_retained'] and cert['inverse_applied_before_absolute_envelope'] and not cert['ordinary_zeta_erased']
    assert cert['global_signed_premise_proved'] and cert['ordinary_exponent']=='1' and not cert['RH_strength'] and cert['first_derivative_recovers_every_ordinary_zero']==(k==1) and cert['higher_derivative_zero_recovery_is_unproved']==(k!=1)
    counts['independent_every_real_scale_signed_certificates']+=1;return P,b


def h(P,b,x):
    x=Q(x)
    if x<1:return flint.arb(0)
    return a(x)*sum((c*a(x).log()**j for j,c in enumerate(P)),flint.arb(0))+b


def witnesses(cert,values,points,counts):
    P,b=certificate(cert,counts);k=cert['order'];CR=cert['residual_constant'];out={}
    for x in map(Q,points):
        N=x.numerator//x.denominator;total=sum(values[1:N+1],flint.arb(0));H=h(P,b,x);res=[]
        for d in range(1,N+1):
            y=x/d;Y=y.numerator//y.denominator
            R=sum((a(n).log()**k for n in range(1,Y+1)),flint.arb(0))-sum((h(P,b,y/n) for n in range(1,Y+1)),flint.arb(0));res.append(mu(d)*R)
            assert abs(R)<=a(CR)*(1+a(y).log())**k;counts['independent_full_retained_remainder_terms']+=1
        rewrite=H+sum(res,flint.arb(0));assert total.overlaps(rewrite) and abs(total-H)<=a(cert['signed_error_constant'])*a(x)
        counts['independent_complete_signed_rewrites_and_global_witnesses']+=1;out[str(x)]={'sum':total,'main':H,'error':total-H}
    return out


def support(signature,order,values,counts):
    order=Q(order);m=order.numerator//order.denominator;integer=order.denominator==1
    assert signature['kind']==('integer_zero_tail' if integer else 'alternating_tail_after_threshold') and signature['threshold']==(m if integer else m+1)
    assert signature['sign_proved_for_every_integer_n'] and not signature['global_distribution_estimate_proved'] and signature['fractional_support_has_no_distinct_prime_cap']==(not integer)
    for n,value in enumerate(values[1:],1):
        r=len(factors(n));product=Q(1)
        for j in range(r):product*=order-j
        expected=0 if n==1 or product==0 else (1 if product>0 else -1)
        if expected==0:assert value.contains(0)
        else:assert (value>0 if expected>0 else value<0)
        counts['independent_all_index_support_witnesses']+=1


def check(d):
    spec=read(d/'protocol.json');seal=read(d/'seal.json');batch=read(d/'candidate_batch.json');validation=read(d/'validation.json');final=read(d/'final_evaluation.json');cases=read(d/'final_cases.json');checks={};counts=defaultdict(int)
    def passed(name):checks[name]=True;print('Verified',name,flush=True)
    for n,v in spec['code_sha256'].items():assert sha(BASE/n)==v
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,v in seal['files'].items():assert sha(d/n)==v
    source=Path(spec['source_run'])
    for n,v in spec['source_sha256'].items():assert sha(source/n)==v
    from root_lattice_report import summary as parent
    parent(source);passed('frozen_sources_and_verified_parent')
    assert seal['selection_closed'] and not seal['final_cases_exist'] and cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json') and final['cases_sha256']==digest(cases)
    assert not set(cases['integers'])&set(spec['parent_final_scales_excluded']) and all(batch['access_denials'].values()) and len(batch['access_denials'])==5
    for failed in spec['retained_failed_runs_are_development']:
        old=Path(failed['run_directory']);assert sha(old/'failure.json')==failed['failure_sha256']
        for n,v in failed['files_sha256'].items():assert sha(old/n)==v
        for n,v in read(old/'protocol.json')['code_sha256'].items():
            if n in spec['this_stage_source_files']:assert sha(old/'frozen_source'/n)==v
        assert not set(cases['integers'])&set(failed['excluded_final_scales'])
    passed('final_isolation_failed_run_retention_and_access_denial')
    data=final['tables'];values={q:arithmetic(t,counts) for q,t in data.items()};passed('actual_full_divisor_arithmetic_checked_by_prime_factor_differences')
    for q in spec['orders']:support(batch['sign_certificates'][q],q,values[q],counts)
    passed('fractional_all_distinct_prime_support_including_unbounded_alternating_tail')
    outcomes={}
    for k,cert in batch['completed_preconditioners'].items():
        result=witnesses(cert,values[k],cases['points'],counts);outcomes[k]=result
        for x,row in final['integer_observations'][k].items():
            for name,key in [('sum','sum_ball'),('main','main_ball'),('error','signed_error_ball')]:tight_overlap(row[key],result[x][name])
    passed('Cauchy_constants_completed_polynomials_full_signed_rewrites_and_global_bounds')
    for proposal in batch['learned_preconditioners']+batch['ablation_random_slots']:
        if proposal['coefficients'] is None:continue
        cert=proposal['proof_certificate'];ref=batch['completed_preconditioners'][str(proposal['order'])];P=[flint.arb(v) for v in ref['polynomial_coefficients']];b=flint.arb(ref['constant_term']);coeff=list(map(Q,proposal['coefficients']));degree=max(len(P)-1,len(coeff)-2);bound=a(ref['signed_error_constant'])+abs(b-a(coeff[-1]));deltas=[]
        for r in range(degree+1):
            delta=(P[r] if r<len(P) else flint.arb(0))-(a(coeff[r]) if r<len(coeff)-1 else flint.arb(0));deltas.append(delta);bound+=abs(delta)
        loss=max((r for r,v in enumerate(deltas) if v!=0),default=0)
        assert cert['log_degree']==loss and a(cert['bound_constant'])>bound and cert['polynomial_coefficients']==list(map(str,coeff[:-1])) and cert['constant_term']==str(coeff[-1])
        assert not cert['source_semantics_changed_by_proof'] and cert['reference_completion_used_only_for_bound'] and cert['actual_mobius_remainder_retained'] and not cert['RH_strength'];counts['independent_original_proposal_global_bounds']+=1
    assert read(d/'archive.json')['equal_completion_and_random_slots'] and len(batch['completion_promotions'])==len(batch['ablation_random_slots'])==spec['promotion_slots']
    passed('unmodified_learned_proposal_bounds_and_equal_budget_completion_ablation')
    for record in batch['anonymous_sign_fits']:
        q=record['decoded_order_after_fit'];sig=record['signature'];expected=batch['sign_certificates'][q]
        if record['universal_signature_admitted']:assert sig=={k:expected[k] for k in ['kind','threshold']}
        assert record['inputs_contained_order_or_prime_names'] is False
    passed('anonymous_sign_signature_inference_and_separate_universal_admission')
    for k,relation in batch['learned_bell_relations'].items():
        coeff=list(map(Q,relation['coefficients'])) if relation['coefficients'] is not None else None
        if coeff is None:continue
        for n in spec['validation_indices']+cases['bell_indices']:
            target=values[k][n];pred=sum((a(c)*feature(mon,n,values['1']) for mon,c in zip(relation['monomials'],coeff)),flint.arb(0));assert target.overlaps(pred) if relation['universal_admitted'] else True
            counts['independent_learned_convolution_relation_witnesses']+=1
        if relation['universal_admitted']:
            exact=[]
            for mon in relation['monomials']:
                assert sum(r+1 for r in mon)==int(k)
                den=1
                for r in set(mon):den*=factorial(r+1)**mon.count(r)*factorial(mon.count(r))
                exact.append(Q(factorial(int(k)),den))
            assert coeff==exact==[Q(v) for v in relation['symbolic_coefficients']]
    passed('learned_signed_convolution_identities_checked_on_complete_fresh_inputs')
    for record in final['generic_sequences']:
        assert record['generated_after_archive_seal'] and not record['prime_support_certificate_applies'];f=list(map(flint.arb,record['input']));N=len(f)-1;inv=[flint.arb(0) for _ in range(N+1)];inv[1]=flint.arb(1)
        for n in range(2,N+1):inv[n]=-sum((f[d]*inv[n//d] for d in range(2,n+1) if n%d==0),flint.arb(0))
        jets={}
        for k in spec['integer_completion_orders']:
            jets[str(k)]=[flint.arb(0)]+[sum((inv[d]*f[n//d]*a(n//d).log()**k for d in range(1,n+1) if n%d==0),flint.arb(0)) for n in range(1,N+1)]
            for old,value in zip(record['jets'][str(k)],jets[str(k)]):tight_overlap(old,value)
        for k,relation in batch['learned_bell_relations'].items():
            if not relation['universal_admitted']:continue
            for n in range(1,N+1):
                predicted=sum((a(c)*feature(mon,n,jets['1']) for mon,c in zip(relation['monomials'],relation['coefficients'])),flint.arb(0));assert predicted.overlaps(jets[k][n]);counts['independent_unrelated_generic_sequence_relations']+=1
    passed('unrelated_evaluator_owned_generic_sequences_validate_learned_operator_structure')
    for q,records in final['generic_differences'].items():
        for row in records:
            r=len(row['steps']);product=Q(1)
            for j in range(r):product*=Q(q)-j
            value=difference(q,row['base'],row['steps']);tight_overlap(row['value_ball'],value)
            assert value.contains(0) if product==0 else (value>0 if product>0 else value<0);counts['independent_fresh_generic_difference_geometries']+=1
    passed('all_order_generic_difference_signs_with_endpoint_and_fractional_controls')
    assert final['controls']['unit_type_alias_rejected'] and final['controls']['fractional_integer_support_alias_rejected'] and final['controls']['higher_derivative_RH_alias_rejected'] and final['controls']['incomplete_fractional_center_RH_alias_rejected']
    assert not final['RH_proved'] and final['uniform_RH_sufficient_signed_controls_verified']==[]
    passed('arithmetic_type_support_branch_and_ordinary_zero_recovery_scope')
    with tempfile.TemporaryDirectory(prefix='divisor-preconditioner-replay-') as td:
        p=Path(td);put(p/'protocol.json',spec);subprocess.run([sys.executable,str(BASE/'divisor_preconditioner_search.py'),'worker','--run-dir',str(p)],cwd=BASE,check=True);replay={n:sha(p/n) for n in seal['files']};assert replay==seal['files']
    passed('deterministic_isolated_learning_completion_promotion_and_ablation_replay')
    result={'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_divisor_preconditioners.py'),'final_sha256':sha(d/'final_evaluation.json'),'checks':checks,'all_passed':all(checks.values()),'counts':dict(counts),
        'replay_sha256':replay,'mathematical_audit_imports_production_code':False,'machine_formalized':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}
    put(d/'verification.json',result);print('Independent verification',len(checks),'/',len(checks),flush=True);return result


def feature(mon,n,lambda_values):
    if not mon:return a(int(n==1))
    if len(mon)==1:return lambda_values[n]*a(n).log()**mon[0]
    return sum((lambda_values[d]*a(d).log()**mon[0]*feature(mon[1:],n//d,lambda_values) for d in range(1,n+1) if n%d==0),flint.arb(0))


def difference(q,b,hs):
    hs=list(map(Q,hs));b=Q(b);out=flint.arb(0)
    for mask in range(1<<len(hs)):
        x=b+sum((h for j,h in enumerate(hs) if mask>>j&1),Q(0));out+=(-1)**(len(hs)-mask.bit_count())*(powq(a(x),Q(q)) if x else flint.arb(0))
    return out


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--run-dir',type=Path,required=True);check(p.parse_args().run_dir.resolve())
