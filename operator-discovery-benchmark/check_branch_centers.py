#!/usr/bin/env python3
"""Independent original-variable centers, fractional zeta integrals and scope."""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,comb,ceil
from pathlib import Path
import argparse,subprocess,sys,tempfile
import flint
from stable_scale_report import BASE,read,sha,digest
from check_mellin_kernels import a,powq,put,tight_overlap
from check_divisor_preconditioners import prime_difference,mu

def cb(z):return flint.acb(flint.arb(z['real']),flint.arb(z['imag']))
def overlap(z,w):tight_overlap(z['real'],w.real);tight_overlap(z['imag'],w.imag)
def regularized(z):return 1+(z-1)*flint.acb_series([z],prec=1).zeta(deflate=True)[0]
def scalar_c(q):return a(q+1).gamma()*(flint.arb.pi()*a(q)).sin()/flint.arb.pi()
def expower(x,p):return (p*x.log()).exp()


@lru_cache(maxsize=None)
def independent_center_series(x,L):
    """Formal scalar division, separate from the producer's series quotient."""
    flint.ctx.prec=1536;old=flint.ctx.cap;flint.ctx.cap=L
    try:zs=flint.acb_series([1,-1],prec=L).zeta(deflate=True);Z=[flint.acb(1)]+[-zs[j-1] for j in range(1,L)]
    finally:flint.ctx.cap=old
    den=[Z[j]-(Z[j-1] if j else 0) for j in range(L)];Lx=a(x).log();num=[flint.acb(a(x)-1)]+[flint.acb(a(x)*(-Lx)**j/factorial(j)) for j in range(1,L)];out=[]
    for j in range(L):out.append((num[j]-sum((den[k]*out[j-k] for k in range(1,j+1)),flint.acb(0)))/den[0])
    return tuple(out)


@lru_cache(maxsize=None)
def quadrature_center(q,x):
    q=Q(q);x=Q(x);flint.ctx.prec=512
    if x==1:return flint.arb(0)
    delta=Q(1,32);R=Q(1,4);L=96;z=flint.acb(flint.arb(1,a(R)),flint.arb(0,a(R)));lower=abs(regularized(z)).lower();assert lower>0
    B=(powq(a(x),1+R)+1)/((1-a(R))*lower)
    error=B*powq(a(delta),1-q)*powq(a(delta/R),L)/(a(1-q)*(1-a(delta/R)))
    small=sum((h*powq(a(delta),j+1-q)/a(j+1-q) for j,h in enumerate(independent_center_series(str(x),L))),flint.acb(0))
    logx=a(x).log()
    def f(v,analytic):
        u=1-v;w=u*logx/2
        return (-a(q)*v.log(analytic=analytic)).exp()*logx*w.exp()*(flint.acb(0,1)*w).sinc()/regularized(u)
    tol=a(Q(1,2**96));large=flint.acb.integral(f,flint.acb(a(delta)),flint.acb(1),abs_tol=tol,rel_tol=tol,depth_limit=50,eval_limit=200000)
    value=scalar_c(q)*(small+large);assert value.is_finite() and value.imag.contains(0)
    return value.real+flint.arb(0,(scalar_c(q)*error).upper())


@lru_cache(maxsize=None)
def independent_center_disk():
    flint.ctx.prec=512;L=80;old=flint.ctx.cap;flint.ctx.cap=L
    try:zs=flint.acb_series([1,-1],prec=L).zeta(deflate=True);Z=[flint.acb(1)]+[-zs[j-1] for j in range(1,L)]
    finally:flint.ctx.cap=old
    R=Q(6,5);outer=Q(2);box=flint.acb(flint.arb(1,a(outer)),flint.arb(0,a(outer)));B=abs(regularized(box)).upper()
    variation=sum((abs(Z[j])*a(R)**j for j in range(1,L)),flint.arb(0))+B*a(R/outer)**L/(1-a(R/outer));lower=(1-variation).lower();assert lower>0
    return lower


@lru_cache(maxsize=None)
def independent_center(q,x):
    q=Q(q);x=Q(x);flint.ctx.prec=512
    if x==1:return flint.arb(0)
    R=Q(6,5);L=640;lower=independent_center_disk();B=(powq(a(x),1+R)+1)/(a(R-1)*lower)
    H=independent_center_series(str(x),L);value=scalar_c(q)*sum((h/a(j+1-q) for j,h in enumerate(H)),flint.acb(0));error=scalar_c(q)*B*a(R)**(-L)/(a(L+1-q)*(1-a(1/R)))
    assert value.is_finite() and value.imag.contains(0);return value.real+flint.arb(0,error.upper())


@lru_cache(maxsize=None)
def independent_profile(q,sreal='5/8',simag='16'):
    """Fractional integral of WHOLE zeta, not an EM derivative implementation."""
    q=Q(q);flint.ctx.prec=512;s=flint.acb(a(Q(sreal)),a(Q(simag)));zs=s.zeta();delta=Q(1,16);R=Q(1,4);L=64;old=flint.ctx.cap;flint.ctx.cap=L
    try:series=flint.acb_series([s,1],prec=L).zeta()
    finally:flint.ctx.cap=old
    Zbox=flint.acb(flint.arb(s.real,a(R)),flint.arb(s.imag,a(R))).zeta();B=abs(Zbox).upper();assert B.is_finite()
    small=-sum((series[j]*powq(a(delta),j-q)/a(j-q) for j in range(1,L)),flint.acb(0))
    error=B*powq(a(delta),-q)*powq(a(delta/R),L)/(a(L-q)*(1-a(delta/R)))
    tol=a(Q(1,2**96))
    def low(t,analytic):return (zs-(s+t).zeta())*(-a(q+1)*t.log(analytic=analytic)).exp()
    def high(t,analytic):return (1-(s+t).zeta())*(-a(q+1)*t.log(analytic=analytic)).exp()
    one=flint.acb.integral(low,flint.acb(a(delta)),flint.acb(1),abs_tol=tol,rel_tol=tol,depth_limit=50,eval_limit=200000)
    Btail=256;two=flint.acb.integral(high,flint.acb(1),flint.acb(Btail),abs_tol=tol,rel_tol=tol,depth_limit=50,eval_limit=200000)
    tail=powq(a(2),-Q(sreal)-Btail)*(1+2/(s.real+Btail-1))*powq(a(Btail),-q-1)/a(2).log()
    value=scalar_c(q)*((zs-1)/a(q)+small+one+two);error=scalar_c(q)*(error+tail)
    assert value.is_finite();return value+flint.acb(flint.arb(0,error.upper()),flint.arb(0,error.upper()))


def parameter_certificate(program,certificate,counts):
    atoms=[(Q(b),Q(w)) for b,w in program['atoms']];assert program['arithmetic_model']=='inverse_one' and program['center']=='full_real_cut' and program['actual_mobius_arithmetic_retained'] and not program['ordinary_zeta_erased']
    assert len({b for b,w in atoms})==len(atoms) and atoms and all(0<b<1 and w for b,w in atoms)
    ps=[sum((w*b**m for b,w in atoms),Q(0)) for m in range(len(atoms))];m=next(i for i,p in enumerate(ps) if p);p=ps[m]
    if not certificate['admitted']:
        assert certificate['missing_not_counterexample'];return m,p
    assert certificate['first_nonzero_moment_order']==m and Q(certificate['first_nonzero_moment'])==p
    M=certificate['eventual_nonzero_moment_threshold'];b,w=max(atoms);left=abs(w)*b**M;right=sum((abs(v)*c**M for c,v in atoms if c<b),Q(0))
    assert left>right and Q(certificate['dominant_moment_left'])==left and Q(certificate['dominant_moment_right'])==right
    assert certificate['sum_weights_zero']==(m>0) and certificate['all_multiplicities_and_all_ordinary_heights'] and certificate['RH_if_cofinal_critical_signed_estimates']
    assert not certificate['global_signed_premise_proved'] and not certificate['ordinary_zeta_erased'] and not certificate['finite_q_success_is_uniform_premise']
    # Exact repeated dominance checks are witnesses; persistence is the proof
    # b_i/b_*<1. The entire-parameter and pole arguments are in the audit text.
    for j in range(M,M+10):assert abs(w)*b**j>sum((abs(v)*c**j for c,v in atoms if c<b),Q(0))
    counts['independent_cofinal_parameter_recovery_certificates']+=1;return m,p


def response_tables(tables,points,counts):
    out={};flint.ctx.prec=640
    for order,table in tables.items():
        q=Q(order);assert 0<q<1 and table['complete_finite_arithmetic'] and not table['prime_or_factor_oracle_used'];values=[flint.arb(0)]
        for n in range(1,table['cutoff']+1):
            value=prime_difference(q,n);tight_overlap(table['values'][n],value);assert table['mu'][n]==mu(n)
            if n>1:
                envelope=powq(a(n).log(),q);assert abs(value)<=envelope or abs(value).overlaps(envelope)
            else:assert value.contains(0)
            counts['independent_full_actual_prime_differences_and_Bernstein_bounds']+=1;values.append(value)
        prefix=[flint.arb(0)]
        for value in values[1:]:prefix.append(prefix[-1]+value)
        out[order]={}
        for x in points:
            xq=Q(x);out[order][x]=prefix[xq.numerator//xq.denominator]
    return out


def audit_observations(data,points,counts,check_centers=True):
    sums=response_tables(data['tables'],points,counts);out={}
    for order in data['tables']:
        out[order]={}
        for x in points:
            row=data['observations'][order][x];tight_overlap(row['sum_ball'],sums[order][x]);A=independent_center(order,x) if check_centers else flint.arb(row['center']['value_ball'])
            assert not row['center']['missing'] and row['center']['complete_branch_center'];tight_overlap(row['center']['value_ball'],A);assert flint.arb(row['center']['value_ball']).contains(A);E=sums[order][x]-A;tight_overlap(row['error_ball'],E)
            assert abs(E)<=a(Q(x))*(1+a(Q(x)).log()+4*a(2).log()*scalar_c(Q(order))/a(1-Q(order)))
            out[order][x]=E;counts['independent_complete_real_cut_center_observations']+=int(check_centers)
    return out


def check(d):
    spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');val=read(d/'validation.json');arc=read(d/'archive.json');seal=read(d/'seal.json');cases=read(d/'final_cases.json');final=read(d/'final_evaluation.json');checks={};counts=defaultdict(int)
    def passed(name):checks[name]=True;print('Verified',name,flush=True)
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    from divisor_preconditioner_report import summary as parent
    parent(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/n)==h
    for failed in spec['retained_failed_runs_are_development']:
        p=Path(failed['run_directory']);assert sha(p/'failure.json')==failed['failure_sha256']
        for n,h in failed['files_sha256'].items():assert sha(p/n)==h
        for n,h in read(p/'protocol.json')['code_sha256'].items():
            if n in spec['this_stage_source_files']:assert sha(p/'frozen_source'/n)==h
        assert not set(cases['integers'])&set(failed['excluded_final_scales'])
    passed('frozen_sources_verified_parent_and_failed_run_retention')
    assert seal['selection_closed'] and not seal['final_cases_exist'] and cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json') and final['cases_sha256']==digest(cases)
    assert cases['calibration_sha256']==sha(d/'final_constants.json') and cases['x_generated_after_constants'] and not set(cases['integers'])&set(spec['parent_final_scales_excluded'])
    assert all(batch['access_denials'].values()) and len(batch['access_denials'])==6 and arc['final_data_used'] is False
    passed('isolated_adaptation_fresh_levels_and_constants_before_fresh_scales')
    programs=batch['programs'];certs={p['id']:parameter_certificate(p['program'],p['recovery_certificate'],counts) for p in programs}
    assert len(batch['promotions'])==len(batch['ablation_slots'])==spec['promotion_slots']
    for row in batch['promotions']:
        parent=next(p for p in programs if p['id']==row['parent_id']);child=next(p for p in programs if p['id']==row['child_id']);m=certs[parent['id']][0];w={}
        for b,c in parent['program']['atoms']:
            b=Q(b);c=Q(c);w[b]=w.get(b,Q(0))+c;w[b/2]=w.get(b/2,Q(0))-2**m*c
        w={b:c for b,c in w.items() if c};actual=dict((Q(b),Q(c)) for b,c in child['program']['atoms']);ratio=actual[max(w)]/w[max(w)]
        assert all(actual[b]==ratio*c for b,c in w.items()) and len(actual)==len(w) and certs[child['id']][0]>m and not row['same_operator_as_parent']
        counts['independent_parameter_annihilator_promotions']+=1
    passed('universal_nonzero_moment_and_all_height_ordinary_zero_recovery')
    # The independent arithmetic and native center audit covers all protected
    # final observations; discovery data are additionally replayed exactly.
    calibrated=audit_observations(read(d/'final_constants.json')['data'],list(map(str,spec['training_points'])),counts)
    observations=audit_observations(final['data'],cases['points'],counts)
    orders=sorted(final['data']['tables'],key=Q)
    for order in [orders[0],orders[-1]]:
        anchor=quadrature_center(order,'32');tight_overlap(read(d/'final_constants.json')['data']['observations'][order]['32']['center']['value_ball'],anchor);counts['independent_original_variable_quadrature_anchors']+=1
    passed('complete_actual_arithmetic_and_original_variable_branch_centers')
    for p in programs:
        m,pm=certs[p['id']]
        for q in cases['levels']:
            h=pm/Q(q)**m;cert=final['weak_certificates'][p['id']][str(q)];K=sum((a(abs(Q(w)))*4*a(2).log()*scalar_c(Q(b)/q)/a(1-Q(b)/q) for b,w in p['program']['atoms']),flint.arb(0))/a(abs(h));C=K+sum((a(abs(Q(w))) for b,w in p['program']['atoms']),flint.arb(0))/a(abs(h))
            assert cert['global_signed_premise_proved'] and cert['all_real_x_ge_one'] and cert['ordinary_exponent']=='1' and cert['log_degree']=='1' and a(cert['constant'])>C and not cert['RH_strength'] and Q(cert['normalization'])==h
            tight_overlap(cert['derivative_guard_ball'],K)
            for x in cases['points']:
                E=sum((a(Q(w))*observations[str(Q(b)/q)][x] for b,w in p['program']['atoms']),flint.arb(0))/a(h);tight_overlap(final['responses'][p['id']][str(q)][x],E)
                assert abs(E)<=a(cert['constant'])*a(Q(x))*(1+a(Q(x)).log());counts['independent_normalized_family_signed_bound_witnesses']+=1
            counts['independent_all_real_scale_weak_family_certificates']+=1
    passed('normalization_all_real_scale_weak_bounds_and_interpolation_charges')
    profile_values={}
    for order,row in final['profile_observations'].items():
        value=independent_profile(order);overlap(row['value_ball'],value);profile_values[order]=value;assert row['whole_continuation_not_prefix_surrogate'] and row['entire_exponent_parameter'];counts['independent_fractional_zeta_integral_observers']+=1
    passed('whole_continuations_checked_by_independent_fractional_zeta_integrals')
    for p in programs:
        for q,obs in final['observers'][p['id']].items():
            q=int(q);h=certs[p['id']][1]/Q(q)**certs[p['id']][0];F=sum((a(Q(w))*profile_values[str(Q(b)/q)] for b,w in p['program']['atoms']),flint.acb(0))/a(h)
            if obs['missing']:assert obs['reason']=='full_profile_observer_unresolved';continue
            overlap(obs['normalized_full_profile_ball'],F);assert abs(F).lower()>0
            sourceF=cb(obs['normalized_full_profile_ball']);lower=flint.arb(obs['profile_modulus_lower_ball']);raw=abs(sourceF).lower()
            assert obs['profile_lower_rounding_bits']==160 and lower>0 and lower.upper()<raw and raw-lower<a(Q(3,2**160))
            s=flint.acb(a(Q(spec['observer_query']['s_real'])),a(Q(spec['observer_query']['s_imag'])));K=flint.arb(final['weak_certificates'][p['id']][str(q)]['derivative_guard_ball'])
            tight_overlap(obs['full_cut_center_mellin_upper_ball'],K/(abs(s)*abs(s.imag)));tight_overlap(obs['integer_to_real_guard_ball'],K/s.real)
            assert obs['conditional_on_global_signed_premise'] and obs['normalization_and_full_center_costs_charged'] and not obs['RH_proved'];counts['independent_charged_complete_profile_family_observers']+=1
    passed('all_normalization_center_and_gap_observer_costs_retained')
    for row in final['leading_only_controls']:
        p=next(p for p in programs if p['id']==row['program_id']);b,w=max((Q(b),Q(w)) for b,w in p['program']['atoms']);obs=row['analytic_obstruction']
        assert obs['all_scale_power_below_one_impossible'] and Q(obs['uncancelled_branch_exponent'])==1-b/row['level'] and obs['complete_center_is_not_rejected']
        counts['independent_leading_only_branch_obstructions']+=1
    assert all(final['type_controls'].values()) and not spec['semantic_denominator_cap'] and final['uniform_RH_sufficient_signed_controls_verified']==[] and not final['RH_proved']
    passed('incomplete_center_generic_alias_zero_family_and_finite_uniform_inferences_rejected')
    # The fit constants are independently reconstructed on evaluator-only
    # calibration points, with no access to their final-scale outcomes.
    constants=read(d/'final_constants.json')['estimates']
    for row in final['estimate_evaluations']:
        p=next(p for p in programs if p['id']==row['program_id']);q=row['level'];m,pm=certs[p['id']];h=pm/Q(q)**m;hyp=row['hypothesis'];theta=a(Q(hyp['eta']))+a(Q(hyp['epsilon']))/powq(a(q),Q(hyp['nu']));dlog=Q(hyp['log_degree']);envelope=lambda x:expower(a(Q(x)),theta)*powq((flint.arb.const_e()+a(Q(x))).log(),dlog)
        train=[sum((a(Q(w))*calibrated[str(Q(b)/q)][str(x)] for b,w in p['program']['atoms']),flint.arb(0))/a(h) for x in spec['training_points']]
        trained=max(float((abs(v)/envelope(str(x))).upper()) for x,v in zip(spec['training_points'],train));C=constants[row['estimate_id']]['constant'];assert C>=trained
        ratios=[float((abs(flint.arb(final['responses'][p['id']][str(q)][x]))/(a(Q(str(C)))*envelope(x))).upper()) for x in cases['points']]
        assert abs(max(ratios)-row['maximum_fresh_ratio'])<=1e-10*(1+max(ratios)) and row['finite_pass']==(max(ratios)<=1) and not row['global_signed_premise_proved'];counts['independent_frozen_fresh_estimate_evaluations']+=1
        cost=row['charged_observer_cost'];gap=a(Q(spec['observer_query']['s_real']))-theta
        if cost['missing']:
            if cost['reason']=='no_positive_mellin_gap':assert not gap>0
        else:
            assert gap>0;D=ceil(dlog);base=(flint.arb.const_e()+1).log();I=sum((a(comb(D,j))*base**(D-j)*factorial(j)/gap**(j+1) for j in range(D+1)),flint.arb(0));observer=final['observers'][p['id']][str(q)];s=flint.acb(a(Q(spec['observer_query']['s_real'])),a(Q(spec['observer_query']['s_imag'])))
            value=abs(s)*(flint.arb(observer['full_cut_center_mellin_upper_ball'])+a(Q(str(C)))*I+flint.arb(observer['integer_to_real_guard_ball']))/flint.arb(observer['profile_modulus_lower_ball'])
            tight_overlap(cost['gap_integral_ball'],I);tight_overlap(cost['gap_ball'],gap);tight_overlap(cost['value_ball'],value);assert abs(float(value.upper())-cost['value'])<=1e-10*(1+cost['value']);counts['independent_full_center_gap_and_normalization_costs']+=1
    passed('fresh_fit_constants_and_finite_estimates_without_uniform_promotion')
    with tempfile.TemporaryDirectory(prefix='branch-center-replay-') as td:
        p=Path(td);put(p/'protocol.json',spec);subprocess.run([sys.executable,str(BASE/'branch_center_search.py'),'worker','--run-dir',str(p)],cwd=BASE,check=True);replay={n:sha(p/n) for n in seal['files']};assert replay==seal['files']
    passed('deterministic_isolated_anonymous_learning_promotion_and_equal_slot_replay')
    result={'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_branch_centers.py'),'final_sha256':sha(d/'final_evaluation.json'),'checks':checks,'all_passed':all(checks.values()),'counts':dict(counts),'replay_sha256':replay,
        'mathematical_audit_imports_production_code':False,'machine_formalized':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False};put(d/'verification.json',result);print('Independent verification',len(checks),'/',len(checks),flush=True);return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);check(p.parse_args().run_dir.resolve())
