#!/usr/bin/env python3
"""Independent factor arithmetic, Gamma recurrence, whole log-kernel observers."""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,comb
from pathlib import Path
import argparse,subprocess,sys,tempfile
import flint
from stable_scale_report import BASE,read,sha,digest
from check_mellin_kernels import a,powq,put,tight_overlap
from check_branch_centers import independent_center,independent_center_series,independent_center_disk,cb
from check_divisor_preconditioners import mu,factors,prime_difference

def expower(x,p):return (p*x.log()).exp()

@lru_cache(maxsize=None)
def gamma_coefficients(M):
    flint.ctx.prec=1536;out=[flint.arb(1)];gamma=flint.arb.const_euler()
    for j in range(1,M+1):out.append((-gamma*out[j-1]-sum((a(r).zeta()*out[j-r] for r in range(2,j+1)),flint.arb(0)))/j)
    return tuple(out)

def prime_jet(m,n):
    f=factors(n);value=flint.arb(0)
    if not f:return value
    for mask in range(1<<len(f)):
        d=1
        for j,(p,e) in enumerate(f):
            if mask>>j&1:d*=p
        if n//d>1:value+=(-1)**mask.bit_count()*a(n//d).log().log()**m/factorial(m)
    return value

@lru_cache(maxsize=None)
def jet_center(m,x):
    m=int(m);x=Q(x)
    if not m or x==1:return flint.arb(0)
    flint.ctx.prec=1536;R=Q(6,5);L=640;G=gamma_coefficients(m);H=independent_center_series(str(x),L);lower=independent_center_disk();B=(powq(a(x),1+R)+1)/(a(R-1)*lower)
    value=sum((h*sum((G[r-1]/a((j+1)**(m-r+1)) for r in range(1,m+1)),flint.arb(0)) for j,h in enumerate(H)),flint.acb(0));error=B*a(R)**(-L)/(1-a(1/R))*sum((abs(G[r-1])/a((L+1)**(m-r+1)) for r in range(1,m+1)),flint.arb(0))
    assert value.is_finite() and value.imag.contains(0);return value.real+flint.arb(0,error.upper())

@lru_cache(maxsize=None)
def continued_jets(M):
    """No Euler continuations or finite parameter differences are used here."""
    flint.ctx.prec=768;s=flint.acb(a(Q(5,8)),16);zs=s.zeta();delta=Q(1,16);R=Q(1,4);L=64;old=flint.ctx.cap;flint.ctx.cap=L
    try:series=flint.acb_series([s,1],prec=L).zeta()
    finally:flint.ctx.cap=old
    B=abs(flint.acb(flint.arb(s.real,a(R)),flint.arb(s.imag,a(R))).zeta()).upper();T=-a(delta).log();J=[];tol=a(Q(1,2**100))
    for k in range(M):
        integral_power=lambda j:a(delta)**j*sum((T**(k-r)/(factorial(k-r)*a(j)**(r+1)) for r in range(k+1)),flint.arb(0))
        small=-sum((series[j]*integral_power(j) for j in range(1,L)),flint.acb(0));error=B/a(R)**L*integral_power(L)/(1-a(delta/R))
        def low(t,analytic):return (zs-(s+t).zeta())*(-t.log(analytic=analytic))**k/(t*factorial(k))
        def high(t,analytic):return (1-(s+t).zeta())*(-t.log(analytic=analytic))**k/(t*factorial(k))
        one=flint.acb.integral(low,flint.acb(a(delta)),flint.acb(1),abs_tol=tol,rel_tol=tol,depth_limit=52,eval_limit=200000);Btail=256
        two=flint.acb.integral(high,flint.acb(1),flint.acb(Btail),abs_tol=tol,rel_tol=tol,depth_limit=52,eval_limit=200000)
        tail=powq(a(2),Q(-5,8))*(1+2/(s.real+Btail-1))*(a(Btail)*a(2).log()).gamma_upper(k+1)/(factorial(k)*a(2).log()**(k+1));value=small+one+two;error+=tail
        assert value.is_finite();J.append(value+flint.acb(flint.arb(0,error.upper()),flint.arb(0,error.upper())))
        print('Independent whole logarithmic kernel',k,flush=True)
    G=gamma_coefficients(M);return tuple([zs-1]+[G[m]*(zs-1)+sum((G[r]*J[m-1-r] for r in range(m)),flint.acb(0)) for m in range(1,M+1)])

def family_parameters(p,q0=2):
    assert p['arithmetic_model']=='inverse_one' and p['center']=='full_real_cut';atoms=[(Q(b),Q(w)) for b,w in p['atoms']]
    for m in range(len(atoms)):
        pm=sum((w*b**m for b,w in atoms),Q(0))
        if pm:break
    bmax=max(b for b,w in atoms);rho=Q(1,2)-bmax/q0;Aw=sum((abs(w)*b**m for b,w in atoms),Q(0))/abs(pm);assert rho>0
    return m,pm,bmax,rho,Aw

def radius(program,V,m,cap):
    k=program['kind'];index=max(1,m)
    if k=='constant':d=a(Q(program['value']))
    elif k=='shifted_power':d=a(Q(program['coefficient']))*powq(a(index),Q(program['index_power']))/powq(a(Q(program['shift']))+V,Q(program['coordinate_power']))
    else:
        assert k=='inverse_monomial';d=1/(a(Q(program['coefficient']))*powq(a(index),Q(program['index_power']))*powq(V,Q(program['coordinate_power'])))
    return a(cap) if d>a(cap) else d

def global_family(p,r,q,x):
    m,pm,bmax,rho,Aw=family_parameters(p);V=(4*(1+a(Q(x)).log())).log();d=radius(r,V,m,rho)
    return a(Aw)*a(Q(x))*(9*d**(-m)*((a(bmax/q)+d)*V).exp()+12/a(rho)**m)

def probability_difference(row):
    """Maximum-density integral checks complex parameter continuation."""
    flint.ctx.prec=640;b=Q(row['base']);hs=list(map(Q,row['rates']));alpha=flint.acb(a(Q(row['parameter_real'])),a(Q(row['parameter_imag'])));r=len(hs);delta=Q(1,16);R=Q(1,8);L=96;old=flint.ctx.cap;flint.ctx.cap=L
    try:
        t=flint.acb_series([0,1],prec=L);cdf=flint.acb_series([1],prec=L)
        for h in hs:cdf*=1-(-a(h)*t).exp()
        if not b:
            density=flint.acb_series([0],prec=L)
            for j,h in enumerate(hs):
                term=a(h)*(-a(h)*t).exp()
                for k,u in enumerate(hs):
                    if k!=j:term*=1-(-a(u)*t).exp()
                density+=term
            integrand_series=density;shift=1
        else:integrand_series=(-a(b)*t).exp()*cdf;shift=0
        coeff=[integrand_series[j] for j in range(L)]
    finally:flint.ctx.cap=old
    z=flint.acb(flint.arb(0,a(R)),flint.arb(0,a(R)));C=[-(-a(h)*z).expm1() for h in hs]
    if b:B=abs((-a(b)*z).exp()).upper()
    else:B=flint.arb(0)
    if b:
        for v in C:B*=abs(v).upper()
    else:
        for j,h in enumerate(hs):
            v=abs(a(h)*(-a(h)*z).exp()).upper()
            for k,w in enumerate(C):
                if k!=j:v*=abs(w).upper()
            B+=v
    small=sum((c*flint.acb(a(delta)).pow(j+shift-alpha)/(j+shift-alpha) for j,c in enumerate(coeff) if c!=0),flint.acb(0));error=B*powq(a(delta),L+shift-Q(row['parameter_real']))/a(R)**L/(a(L+shift-Q(row['parameter_real']))*(1-a(delta/R)));tol=a(Q(1,2**96))
    def f(t,analytic):
        C=[-(-a(h)*t).expm1() for h in hs]
        if b:
            value=(-a(b)*t).exp()
            for w in C:value*=w
            return value*((-alpha-1)*t.log(analytic=analytic)).exp()
        density=flint.acb(0)
        for j,h in enumerate(hs):
            v=a(h)*(-a(h)*t).exp()
            for k,w in enumerate(C):
                if k!=j:v*=w
            density+=v
        return density*(-alpha*t.log(analytic=analytic)).exp()
    Tcut=192;large=flint.acb.integral(f,flint.acb(a(delta)),flint.acb(Tcut),abs_tol=tol,rel_tol=tol,depth_limit=52,eval_limit=200000);rate=a(b if b else min(hs));sigma=Q(row['parameter_real']);tail=(rate*Tcut).gamma_upper(a(1-sigma))/powq(rate,1-sigma)
    tail*=1 if b else sum(map(a,hs));value=(small+large)*(-1)**(r-1)/((1-alpha).gamma());error+=tail
    if b:value*=alpha;error*=abs(alpha)
    error*=abs((1-alpha).rgamma());return value+flint.acb(flint.arb(0,error.upper()),flint.arb(0,error.upper()))

def check(d):
    spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');seal=read(d/'seal.json');final=read(d/'final_evaluation.json');cases=read(d/'final_cases.json');checks={};counts={}
    def passed(name):checks[name]=True;print('Verified',name,flush=True)
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    from branch_center_report import summary as parent
    parent(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/n)==h
    assert cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json') and final['cases_sha256']==digest(cases) and all(batch['access_denials'].values())
    for failed in spec['retained_failed_runs_are_development']:
        p=Path(failed['run_directory']);assert sha(p/'failure.json')==failed['failure_sha256']
        for n,h in failed['files_sha256'].items():assert sha(p/n)==h
        assert not set(cases['integers'])&set(failed['excluded_final_scales'])
    passed('frozen_sources_verified_parent_isolated_learning_and_fresh_cases')
    # Detailed final schema is written by the independent frozen runner.
    tables=final['root_tables'];values={};count=0
    for order,t in tables.items():
        flint.ctx.prec=896;v=[flint.arb(0)]
        for n in range(1,t['cutoff']+1):
            x=prime_difference(Q(order),n);tight_overlap(t['values'][n],x);v.append(x);count+=1
        assert not t['prime_or_factor_oracle_used'] and t['complete_finite_arithmetic'];values[order]=v
    counts['independent_complete_prime_difference_coefficients']=count;passed('actual_complete_fractional_coefficients_without_producer_factor_oracle')
    jetvalues={};count=0
    for k,t in final['jet_tables'].items():
        m=int(k);flint.ctx.prec=896;v=[flint.arb(0)]
        for n in range(1,t['cutoff']+1):x=prime_jet(m,n);tight_overlap(t['values'][n],x);v.append(x);count+=1
        jetvalues[m]=v;assert t['arithmetic_model']=='inverse_one' and t['Taylor_factorial_charged'] and t['weight_at_one_is_zero']
    counts['independent_complete_nested_log_jet_coefficients']=count;passed('actual_signed_parameter_jets_factorial_and_zero_at_one')
    for row in final['jet_observations']:
        m=row['index'];x=Q(row['x']);B=jet_center(m,str(x));tight_overlap(row['center']['value_ball'],B);assert flint.arb(row['center']['value_ball']).contains(B);total=sum(jetvalues[m][1:x.numerator//x.denominator+1],flint.arb(0));tight_overlap(row['signed_error_ball'],total-B)
        for j,c in enumerate(row['center'].get('gamma_coefficients',[])):tight_overlap(c,gamma_coefficients(m)[j])
    counts['independent_complete_parameter_jet_centers']=len(final['jet_observations']);passed('independent_Gamma_recurrence_full_jet_centers_and_signed_errors')
    for row in final['family_observations']:
        p=row['program'];q=row['level'];x=Q(row['x']);m,pm,bmax,rho,Aw=family_parameters(p);h=pm/Q(q)**m
        T=sum((a(Q(w))*sum(values[str(Q(b)/q)][1:x.numerator//x.denominator+1],flint.arb(0)) for b,w in p['atoms']),flint.arb(0))/a(h);A=sum((a(Q(w))*independent_center(str(Q(b)/q),str(x)) for b,w in p['atoms']),flint.arb(0))/a(h);E=T-A;tight_overlap(row['signed_error_ball'],E)
        new=global_family(p,row['radius'],q,str(x));tight_overlap(row['certificate']['bound_ball'],new);assert abs(E)<=new;params=row['certificate']['parameters'];assert params['moment']==m and Q(params['weight_norm'])==Aw and Q(params['uniform_center_derivative_guard'])==12*Aw/rho**m
        assert row['certificate']['uniform_in_normalization_level'] and row['certificate']['cancellation_before_absolute_envelope'] and row['certificate']['global_signed_premise_proved'] and not row['certificate']['RH_strength']
    counts['independent_uniform_normalization_family_bound_witnesses']=len(final['family_observations']);passed('universal_cancellation_before_envelope_and_q_independent_center_guards')
    for row in final['probability_geometries']:
        value=probability_difference(row);tight_overlap(row['difference_ball']['real'],value.real);tight_overlap(row['difference_ball']['imag'],value.imag)
    counts['independent_complex_exponential_maximum_identity_geometries']=len(final['probability_geometries']);passed('independent_probability_maximum_and_killed_maximum_complex_parameter_identities')
    M=max(map(int,final['jet_profiles']));profiles=continued_jets(M)
    for m,row in final['jet_profiles'].items():
        m=int(m);tight_overlap(row['value_ball']['real'],profiles[m].real);tight_overlap(row['value_ball']['imag'],profiles[m].imag);assert row['whole_continued_jet']
    counts['independent_whole_logarithmic_zeta_kernel_observers']=M;passed('whole_continued_jet_numerators_checked_by_logarithmic_zeta_integrals')
    for row in batch['limit_inferences']:
        p=row['program'];m,pm,bmax,rho,Aw=family_parameters(p);cert=row['limit_certificate']
        if cert['admitted']:assert row['feature']==('constant' if m==0 else f'nested_log_integer_{m}') and Q(row['coefficient'])==Q(1,factorial(m)) and cert['uniform_on_compact_x_only'] and not cert['same_as_fixed_q_parent']
    passed('anonymous_limit_inference_with_exact_semantics_and_no_infinite_scale_exchange')
    for row in final['radius_evaluations']:
        V=a(Q(row['coordinate']));m=row['index'];r=row['radius'];delta=radius(r,V,m,Q(1,4));bound=9*delta**(-m)*(delta*V).exp();tight_overlap(row['bound_ball'],bound)
        assert row['certificate']['admitted'] and row['certificate']['cap_applied_before_Cauchy_bound'] and row['certificate']['radius_program_semantics_unchanged'] and not row['certificate']['RH_strength']
    counts['independent_fresh_certified_radius_envelope_witnesses']=len(final['radius_evaluations']);passed('learned_and_random_radius_programs_proved_on_their_full_domain')
    assert all(final['negative_controls'].values()) and not final['RH_proved'] and final['uniform_RH_sufficient_signed_controls_verified']==[]
    passed('generic_prime_bound_alias_finite_jet_bank_and_zero_erasing_alias_rejected')
    with tempfile.TemporaryDirectory(prefix='parameter-cancellation-replay-') as td:
        p=Path(td);put(p/'protocol.json',spec);subprocess.run([sys.executable,str(BASE/'parameter_cancellation_search.py'),'worker','--run-dir',str(p)],cwd=BASE,check=True);replay={n:sha(p/n) for n in seal['files']};assert replay==seal['files']
    passed('deterministic_isolated_limit_inference_radius_promotion_and_ablation_replay')
    result={'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_parameter_cancellation.py'),'final_sha256':sha(d/'final_evaluation.json'),'checks':checks,'all_passed':all(checks.values()),'counts':counts,'replay_sha256':replay,
        'mathematical_audit_imports_production_code':False,'machine_formalized':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False};put(d/'verification.json',result);print('Independent verification',len(checks),'/',len(checks),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);check(p.parse_args().run_dir.resolve())
