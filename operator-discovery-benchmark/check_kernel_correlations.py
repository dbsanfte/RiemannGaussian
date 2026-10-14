#!/usr/bin/env python3
"""Independent arithmetic, complete-tail Gram sums and zero-bridge audits.

Imports the preceding frozen independent checker, never a producer mathematics
module. Deterministic producer replay is isolated in a separate subprocess.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,ceil,log2
from pathlib import Path
import subprocess,sys,tempfile
import flint
from stable_scale_report import BASE,read,sha,digest
from check_mellin_kernels import (a,powq,put,mu_by_factors,independent_table,tight_overlap,
    certificate_valid,Pvalue,getpoly,mellin_poly,pochhammer,independent_global)


def overlap(txt,v):tight_overlap(txt,v)


def independent_squarefree(table,points,counts):
    k,ell,b=map(Q,(table['k'],table['ell'],table['base']));w0=2*k
    N0=table['cutoff'];N=N0+19;L=table['Taylor_terms']+8;mmax=table['maximum_moment']
    flint.ctx.prec=max(table['precision']+160,ceil(float(w0+ell*(L+mmax))*log2(N))+320)
    mu=mu_by_factors(N);weights=[];sums=[flint.arb(0) for _ in range(L+mmax)]
    for n in range(N,0,-1):
        if not mu[n]:continue
        weight=powq(a(n),-w0);step=powq(a(n),-ell);weights.append((weight,step));v=weight
        for j in range(len(sums)):sums[j]+=v;v*=step
    tails=[]
    for j,v in enumerate(sums):
        w=w0+ell*j;tail=a(w).zeta()/a(2*w).zeta()-v
        assert abs(tail)<=powq(a(N),1-w)/a(w-1);tails.append(tail)
        if j<len(table['tail_moment_balls']):
            adjustment=sum((a(mu[n]**2)*powq(a(n),-w) for n in range(N0+1,N+1)),flint.arb(0))
            overlap(table['tail_moment_balls'][j],tail+adjustment);counts['independent_squarefree_tail_moments']+=1
    rates=sorted({b**i+b**j for i in range(3) for j in range(3)})
    assert list(map(Q,table['rates']))==rates and table['all_infinite_squarefree_terms_included']
    assert table['all_moment_exponents_greater_than_one'] and w0>2
    values={}
    for X in map(Q,points):
        scale=powq(a(X),w0);xe=powq(a(X),ell)
        for r in rates:
            c=a(r)*xe
            for m in range(mmax+1):
                prefix=sum((weight*(c*step)**m*(-c*step).exp() for weight,step in weights),flint.arb(0))
                tail=flint.arb(0)
                for j in range(L-1,-1,-1):tail=(-c)*tail+tails[m+j]/factorial(j)
                w=w0+ell*(m+L);err=c**(m+L)*powq(a(N),1-w)/(a(w-1)*factorial(L))
                v=scale*(prefix+c**m*tail+flint.arb(0,err));key=f'{m}:{r}:{X}'
                overlap(table['values'][key],v);values[key]=v;counts['independent_complete_squarefree_atoms']+=1
    for row in table['tail_bounds']:
        m,r,X=row['moment'],Q(row['rate']),Q(row['scale']);L0=table['Taylor_terms'];w=w0+ell*(m+L0)
        error=powq(a(X),w0)*(a(r)*powq(a(X),ell))**(m+L0)*powq(a(N0),1-w)/(factorial(L0)*a(w-1))
        overlap(row['error_ball'],error);counts['independent_squarefree_Taylor_bounds']+=1
    return values


def expansion(Ks,H,b):
    """Four ordered matrix entries, unlike the producer's three products."""
    a0,h,c=map(Q,H['entries']);matrix=[[a0,h],[h,c]];out=defaultdict(Q)
    for i in range(2):
        for j in range(2):
            for m,t,v in Ks[i]['terms']:
                for n,u,w in Ks[j]['terms']:
                    r,s=b**t,b**u
                    out[m+n,r+s]+=matrix[i][j]*Q(v)*Q(w)*r**m*s**n/(r+s)**(m+n)
    return [[m,str(r),str(v)] for (m,r),v in sorted(out.items()) if v]


def metric_check(p,counts):
    H=p['metric'];a0,h,c=map(Q,H['entries']);det=a0*c-h*h
    assert max(abs(a0),abs(h),abs(c))==1 and Q(H['determinant'])==det
    positive=a0>=0 and c>=0 and det>=0
    assert H['positive_semidefinite']==positive and H['positive_definite']==(positive and det>0)
    if positive:
        R=list(map(lambda r:list(map(Q,r)),H['active_covectors']));ds=list(map(Q,H['positive_pivots']))
        assert ds and all(d>0 for d in ds) and len(R)==len(ds)==H['rank']
        reconstructed=[[sum((d*r[i]*r[j] for d,r in zip(ds,R)),Q(0)) for j in range(2)] for i in range(2)]
        assert reconstructed==[[a0,h],[h,c]]
    else:assert H['rank'] is None and H['active_covectors']==H['positive_pivots']==[]
    assert H['indefinite_is_not_a_counterexample_to_any_growth_bound']
    rows=expansion(p['kernels'],H,Q(p['parameters'][2]));assert rows==p['diagonal_terms'] and rows
    if p['kind']=='energy':
        rec=p['recovery']
        if not positive:
            assert rec['kind']=='indefinite_signed_observable_missing_coercive_recovery' and not rec['all_height_no_common_zero']
        else:
            active=[];pivots=[];vectors=[]
            for r,d in zip(R,ds):
                v=defaultdict(Q)
                for weight,K in zip(r,p['kernels']):
                    for m,j,c0 in K['terms']:v[m,j]+=weight*Q(c0)
                v={ij:w for ij,w in v.items() if w}
                if v:
                    active.append([[m,j,str(w)] for (m,j),w in sorted(v.items())]);pivots.append(d);vectors.append(r)
            assert [K['terms'] for K in rec['effective_kernels']]==active
            assert list(map(Q,rec['positive_pivots']))==pivots and [list(map(Q,r)) for r in rec['active_covectors']]==vectors
            valid=certificate_valid(rec['effective_kernels'],rec['certificate']);assert valid==rec['all_height_no_common_zero']
            counts['independent_all_height_effective_bank_certificates']+=valid
    counts['exact_metric_and_kernel_product_checks']+=1


@lru_cache(maxsize=None)
def diagonal_atom(k,ell,m,r):
    flint.ctx.prec=640;u=(2*k-1)/ell+m;v=(2*k-Q(1,2))/ell+m
    # Different grouping: the two Gamma terms are combined by Gamma recurrence.
    I=a(u).gamma()*powq(a(r),(1-2*k)/ell)/a(ell)
    U=a(v).gamma()*powq(a(r),(Q(1,2)-2*k)/ell)*(a(2*k+ell*m)+a(ell*v))/a(ell)
    return I,U


def diagonal_check(p,counts):
    k,ell,b=map(Q,p['parameters']);dc=p['diagonal_certificate'];I=flint.arb(0);U=flint.arb(0)
    for row,old in zip(p['diagonal_terms'],dc['components']):
        m,r,c=row;r,c=Q(r),Q(c);ii,uu=diagonal_atom(k,ell,m,r);I+=a(c)*ii;U+=a(abs(c))*uu
        assert old['moment']==m and Q(old['rate'])==r and Q(old['coefficient'])==c
        overlap(old['signed_integral_ball'],a(c)*ii);overlap(old['absolute_weighted_variation_ball'],a(abs(c))*uu)
    assert len(dc['components'])==len(p['diagonal_terms'])
    density=1/a(2).zeta();A=density*I;V=a(Q(5,2))*U
    for name,v in [('continuous_integral_ball',I),('weighted_variation_ball',U),('squarefree_density_ball',density),('main_coefficient_ball',A),('signed_remainder_constant_ball',V)]:overlap(dc[name],v)
    assert not dc['imported_prime_distribution_estimate'] and not dc['RH_strength_for_full_response']
    if p['metric']['positive_semidefinite']:assert I>0 and A>0
    counts['all_scale_signed_diagonal_certificate_checks']+=1
    return A,V


def pmul(P,R):
    out=[Q(0)]*(len(P)+len(R)-1)
    for i,c in enumerate(P):
        for j,d in enumerate(R):out[i+j]+=c*d
    while len(out)>1 and not out[-1]:out.pop()
    return out


def density_recovery_check(p,counts):
    rec=p['density_recovery'];rows=p['diagonal_terms'];rates={Q(r) for m,r,c in rows}
    assert not rec['counterexample_to_bound']
    if len(rates)!=1:
        assert rec['kind']=='multiple_rates_missing_recovery_certificate' and not rec['all_height_recovery'];return False
    P=[Q(0)]*(max(m for m,r,c in rows)+1)
    for m,r,c in rows:
        for (j,h),v in pochhammer(m).items():P[j]+=Q(c)*v
    while len(P)>1 and not P[-1]:P.pop()
    assert list(map(Q,rec['Mellin_polynomial']))==P
    R=list(map(Q,rec['remaining_polynomial']));rest=R
    for j in rec['peeled_nonpositive_roots']:
        assert type(j) is int and j>=0;rest=pmul(rest,[Q(j),Q(1)])
    assert rest==P
    k,ell,b=map(Q,p['parameters']);lower=(2*k-Q(1,2))/ell;assert Q(rec['strict_real_part_lower_bound'])==lower
    # Horner substitution, rather than the producer's binomial coefficient sum.
    translated=[Q(0)]
    for c in reversed(R):translated=pmul(translated,[lower,Q(1)]);translated[0]+=c
    while len(translated)>1 and not translated[-1]:translated.pop()
    shifted=[c/R[-1] for c in translated];assert list(map(Q,rec['shifted_monic_coefficients']))==shifted
    valid=len(R)<=3 and all(c>=0 for c in shifted) and shifted[-1]>0
    assert rec['all_height_recovery']==valid
    assert rec['kind']==('common_rate_exact_polynomial_strip_certificate' if valid else 'common_rate_missing_polynomial_certificate')
    if valid:assert rec['sufficient_limiting_density_exponent']=='1/4' and rec['zero_multiplicities_are_allowed']
    counts['exact_density_strip_certificates']+=valid
    return valid


@lru_cache(maxsize=None)
def positive_atom_bound(k,ell,r,m):
    flint.ctx.prec=640;u=(k-1)/ell+m;e=k/ell+m
    integral=powq(a(r),(1-k)/ell)*a(u).gamma()/a(ell)
    maximum=powq(a(r),-k/ell)*powq(a(e),e)*(-a(e)).exp()
    return integral+2*maximum


def density_constants(p,old=None,counts=None):
    k,ell,b=map(Q,p['parameters']);flint.ctx.prec=640;W=flint.arb(0);J=flint.arb(0);local=[]
    for m,r,c in p['diagonal_terms']:
        r,c=Q(r),Q(c);first=positive_atom_bound(2*k,ell,r,m);following=positive_atom_bound(2*k,ell,r,m+1);w=2*k+ell*m
        W+=a(abs(c))*first;J+=a(abs(c))*(a(w)*first+a(ell)*following)
        local.append((w,a(abs(c))*a(r**m)*a(w).zeta()/a(2*w).zeta()))
    J+=abs(flint.arb(p['diagonal_certificate']['main_coefficient_ball']))
    if old is not None:
        overlap(old['absolute_diagonal_bound_constant_ball'],W);overlap(old['density_unit_increment_constant_ball'],J)
        assert len(old['local_diagonal_terms'])==len(local)
        for row,(w,v) in zip(old['local_diagonal_terms'],local):assert Q(row['power'])==w;overlap(row['coefficient_ball'],v)
        assert old['all_real_scale_density_correction_growth_exponent']=='1/2' and old['RH_density_growth_exponent_unproved']=='1/4'
        counts['all_scale_density_unit_certificates']+=1
    return W,J,local


def independent_responses(p,atoms,points):
    return [{str(X):sum((a(c)*atoms[f'{m}:{j}:{X}'] for m,j,c in K['terms']),flint.arb(0)) for X in map(Q,points)} for K in p['kernels']]


def obs_check(p,old,atoms,diagonal,points,counts):
    f,g=independent_responses(p,atoms,points);aa,h,c=map(a,p['metric']['entries']);A=flint.arb(p['diagonal_certificate']['main_coefficient_ball']);out={}
    for X in map(Q,points):
        key=str(X);F,G=f[key],g[key]
        E=aa*F*F+2*h*F*G+c*G*G
        D=sum((a(v)*diagonal[f'{m}:{r}:{X}'] for m,r,v in p['diagonal_terms']),flint.arb(0));Z=D-A*a(X)
        for name,v in [('energy_ball',E),('diagonal_ball',D),('signed_off_diagonal_ball',E-D),('density_correction_ball',Z)]:overlap(old[key][name],v)
        out[key]={'E':E,'D':D,'Z':Z,'F':[F,G]};counts['independent_complete_Gram_observations']+=1
    return out


@lru_cache(maxsize=None)
def grow(kind,eta,margin,nu,d,q,X):
    flint.ctx.prec=512;th=a(eta)+a(margin)*powq(a(q),-Q(nu));exponent=2*th if kind=='energy' else th
    return (exponent*a(X).log()).exp()*powq((flint.arb.const_e()+a(X)).log(),Q(d))


def growth(c,q,X):
    f=c['frontier'];return grow(c['kind'],f['limit'],f['margin'],f['approach_power'],f['log_power'],q,str(X))


def fit_check(c,obs,Cs,qs,spec,counts):
    D=int(spec['constant_rule']['upward_denominator']);flint.ctx.prec=512
    for q in qs:
        # The fitted constant is specified from the serialized training enclosure,
        # already checked independently against complete arithmetic sums.
        ratios=[]
        for X,row in obs.items():
            v=abs(flint.arb(row['density_correction_ball'])) if c['kind']=='density' else flint.arb(row['energy_ball'])-a(1+Q(c['rho']))*flint.arb(row['diagonal_ball'])
            ratios.append((v/growth(c,q,X)).upper())
        maximum=max(flint.arb(0).upper(),*ratios)
        expected=Q(max(1,int((maximum*a(spec['constant_rule']['training_margin'])*D).ceil().fmpz())),D)
        # Endpoint arithmetic at higher precision can change the last quantization
        # cell. Check the defining upward rule within the recorded native radius.
        got=Q(Cs[str(q)]);delta=abs(a(got)-a(expected))
        uncertainty=max(((flint.arb(r['density_correction_ball']).rad() if c['kind']=='density' else
            flint.arb(r['energy_ball']).rad()+a(abs(1+Q(c['rho'])))*flint.arb(r['diagonal_ball']).rad())/growth(c,q,X)
            ).upper() for X,r in obs.items())
        assert delta<=a(2)*a(spec['constant_rule']['training_margin'])*uncertainty+a(Q(2,D))
        assert got>0;counts['independent_training_constant_checks']+=1


def comparison_check(c,obs,Cs,qs,old,counts):
    failures=[];unresolved=[];worst=0
    for q in qs:
        for X,row in obs.items():
            # saved intervals are validated by obs_check; this also checks exact
            # failure/unresolved bookkeeping rather than changing its thresholds.
            if 'energy_ball' in row:
                v=abs(flint.arb(row['density_correction_ball'])) if c['kind']=='density' else flint.arb(row['energy_ball'])-a(1+Q(c['rho']))*flint.arb(row['diagonal_ball'])
            else:v=abs(row['Z']) if c['kind']=='density' else row['E']-a(1+Q(c['rho']))*row['D']
            B=a(Cs[str(q)])*growth(c,q,X);key=f'{q}:{X}'
            if not v<=B:(failures if v>B else unresolved).append(key)
            worst=max(worst,max(0,float((v/B).upper())));counts['independent_finite_inequality_comparisons']+=1
    assert failures==old['failures'] and unresolved==old['unresolved']
    assert old['finite_points_passed']==(not failures and not unresolved) and not old['uniform_signed_premise_proved']
    assert old['point_comparisons']==len(obs)*len(qs) and abs(old['maximum_ratio']-worst)<=1e-9*(1+worst)


@lru_cache(maxsize=None)
def kernel_global(terms,k,ell,b):
    flint.ctx.prec=640;W=flint.arb(0);J=flint.arb(0);local=[]
    for m,j,c in terms:
        c=Q(c);r=b**j;v=positive_atom_bound(k,ell,r,m);following=positive_atom_bound(k,ell,r,m+1)
        W+=a(abs(c))*v;J+=a(abs(c))*(a(k+ell*m)*v+a(ell)*following)
        local.append((k+ell*m,a(abs(c))*a(r**m)*a(k+ell*m).zeta()))
    return W,J,local


@lru_cache(maxsize=None)
def observer_context(params,query):
    k,ell,b=map(Q,params);sigma,t=map(Q,query);flint.ctx.prec=640;s=flint.acb(a(sigma),a(t));v=(a(k)-s)/a(ell);z=(-v*a(b).log()).exp()
    return s,v,z,v.gamma()


def complex_overlap(old,z):overlap(old['real'],z.real);overlap(old['imag'],z.imag)


def cost_check(p,c,Cs,qs,old,spec,counts):
    kind=c['kind'];f=c['frontier'];eta=Q(f['limit']);threshold=Q(1,2) if kind=='energy' else Q(1,4)
    if eta!=threshold:
        assert old['observers']==[] and old['best_log_cost'] is None;return
    rec=p['recovery'] if kind=='energy' else p['density_recovery'];valid=rec['all_height_no_common_zero'] if kind=='energy' else rec['all_height_recovery']
    if not valid:assert old['best_log_cost'] is None and old['observers']==[];return
    query=spec[kind+'_cost_query'];k,ell,b=map(Q,p['parameters']);sigma,t=map(Q,query);flint.ctx.prec=640
    s=flint.acb(a(sigma),a(t));dc=p['diagonal_certificate'];A=flint.arb(dc['main_coefficient_ball']);V=flint.arb(dc['signed_remainder_constant_ball'])
    if kind=='energy':
        s,v,z,G=observer_context(tuple(p['parameters']),tuple(query));cert=rec['certificate']
        if cert['kind']=='exact_bivariate_Bezout':
            denominator=(G*Pvalue(getpoly(cert['target_polynomial']),v,z)).abs_lower();factors=[Pvalue(getpoly(P),v,z).abs_upper() for P in cert['multipliers']]
        else:denominator=(G*Pvalue(mellin_poly(rec['effective_kernels'][0]),v,z)).abs_lower();factors=[flint.arb(1)]
        globals_=[kernel_global(tuple(tuple(t) for t in K['terms']),k,ell,b) for K in rec['effective_kernels']]
        diagonal=a(max(1+Q(c['rho']),Q(0))).sqrt()*(A.sqrt()/a(sigma-Q(1,2))+V.sqrt()/a(sigma-Q(1,4)))
    else:
        v=(a(2*k)-s)/a(ell);P=flint.acb(0)
        for j,c0 in enumerate(rec['Mellin_polynomial']):P+=a(c0)*v**j
        G=v.gamma()*P*powq(a(rec['common_rate']),Q(0))*(-v*a(rec['common_rate']).log()).exp()/a(ell)
        denominator=G.abs_lower();zeta=s.zeta().abs_lower();W,J,local=density_constants(p)
        localcost=sum((value/a(w-sigma) for w,value in local),flint.arb(0));pole=abs(A)/(s-1).abs_lower();unit=J/a(sigma)
    assert denominator>0 and (kind=='energy' or zeta>0)
    assert len(old['observers'])==len(qs);logs=[];L0=(flint.arb.const_e()+1).log();d=ceil(Q(f['log_power'])/(2 if kind=='energy' else 1))
    for q,row in zip(qs,old['observers']):
        flint.ctx.prec=640;gap=a(sigma)-a(f['limit'])-a(f['margin'])*powq(a(q),-Q(f['approach_power']))
        assert row['q']==q;overlap(row['gap_ball'],gap)
        if not gap>0:
            assert row['status'].startswith('outside_');counts['independent_observer_out_of_domain']+=1;continue
        logmoment=sum((a(Q(factorial(d),factorial(j)*factorial(d-j)))*L0**(d-j)*factorial(j)/gap**(j+1) for j in range(d+1)),flint.arb(0))
        if kind=='energy':
            signed=a(Cs[str(q)]).sqrt()*logmoment;norms=[]
            for pivot,(W,J,local) in zip(rec['positive_pivots'],globals_):
                norms.append(sum((value/a(w-sigma) for w,value in local),flint.arb(0))+J/a(sigma)+(diagonal+signed)/a(pivot).sqrt())
            cost=a(ell)*sum((fac*norm for fac,norm in zip(factors,norms)),flint.arb(0))/denominator
            overlap(row['diagonal_density_cost_ball'],diagonal);overlap(row['signed_cost_ball'],signed)
            for txt,v0 in zip(row['full_effective_transform_norm_balls'],norms):overlap(txt,v0)
            complex_overlap(row['native_gamma_ball'],G);overlap(row['denominator_lower_ball'],denominator);overlap(row['conditional_reciprocal_bound_ball'],cost)
        else:
            ratio=(localcost+pole+unit+a(Cs[str(q)])*logmoment)/denominator;cost=ratio/zeta
            for name,value in [('local_diagonal_cost_ball',localcost),('pole_center_cost_ball',pole),('unit_cost_ball',unit),('transform_denominator_lower_ball',denominator),('native_numerator_zeta_lower_ball',zeta),('conditional_zeta_ratio_bound_ball',ratio),('conditional_reciprocal_zeta_2s_bound_ball',cost)]:overlap(row[name],value)
            complex_overlap(row['native_kernel_transform_ball'],G)
        logcost=float(cost.upper().log());assert abs(row['log_cost']-logcost)<=1e-9*(1+abs(logcost)) and not row['uniform_signed_premise_proved']
        logs.append(logcost);counts['independent_fully_charged_observers']+=1
    assert (old['best_log_cost'] is None and not logs) or abs(old['best_log_cost']-min(logs))<=1e-9*(1+abs(min(logs)))


def attempt_check(p,c,counts):
    f=c['frontier'];eta=Q(f['limit']);attempt=c['certificate_attempt'];k,ell,b=map(Q,p['parameters'])
    assert not f['constant_growth_in_q_restricted'] and not f['finite_parameter_grid_suffices']
    assert Q(f['margin'])>0 and Q(f['approach_power'])>0 and Q(f['log_power'])>=0
    if c['kind']=='energy':
        eligible=eta==Q(1,2) and p['recovery']['all_height_no_common_zero'];assert eta>=Q(1,2)
        if eta<1:
            assert attempt['status']=='signed_correlation_certificate_missing' and not attempt['off_diagonal_uniform_premise_proved']
        else:
            assert attempt['status']=='unconditional_energy_exponent_two_witness' and not attempt['RH_strength'] and not attempt['same_fitted_constants_proved']
            W=[kernel_global(tuple(tuple(t) for t in K['terms']),k,ell,b)[0] for K in p['kernels']];aa,h,cc=map(Q,p['metric']['entries'])
            Dc=abs(flint.arb(p['diagonal_certificate']['main_coefficient_ball']))+flint.arb(p['diagonal_certificate']['signed_remainder_constant_ball'])
            witness=a(abs(aa))*W[0]**2+2*a(abs(h))*W[0]*W[1]+a(abs(cc))*W[1]**2+a(abs(1+Q(c['rho'])))*Dc
            overlap(attempt['constant_ball'],witness)
    else:
        assert eta>=Q(1,4);eligible=eta==Q(1,4) and p['density_recovery']['all_height_recovery']
        assert attempt['uniform_premise_proved']==(eta>=Q(1,2))
        if eta>=Q(1,2):assert attempt['status']=='true_weak_density_frontier' and not attempt['same_fitted_constants_proved']
        else:assert not attempt['uniform_premise_proved']
    assert c['RH_sufficient_if_uniform']==eligible;counts['independent_frontier_scope_checks']+=1


def arithmetic_and_reflection(N,counts):
    flint.ctx.prec=640;mu=mu_by_factors(N);by_square=[0]*(N+1)
    for d in range(1,ceil(N**.5)+1):
        for n in range(d*d,N+1,d*d):by_square[n]+=mu[d]
    assert by_square[1:]==[v*v for v in mu[1:]]
    total=0;density=1/a(2).zeta()
    for n in range(1,N+1):
        total+=mu[n]**2
        assert abs(a(total)-density*n)<=a(Q(5,2))*a(n).sqrt()
    # The universal floor-bound reduction uses 1<=u<=2 and
    # 2u^2-5u+2=(2u-1)(u-2)<=0, including noninteger x.
    assert pmul([Q(-1),Q(2)],[Q(-2),Q(1)])==[Q(2),Q(-5),Q(2)]
    chains=[]
    for beta,height in [(Q(3,4),Q(17)),(Q(51,100),Q(2**20)),(Q(999,1000),Q(1,2**20))]:
        B,T=beta,height
        for j in range(36):
            assert Q(1,2)<B<1 and B-Q(2,3)==(-Q(1,2))**j*(beta-Q(2,3)) and T==height/2**j
            B,T=1-B/2,T/2;counts['exact_hypothetical_zero_reflection_steps']+=1
        chains.append({'initial_real_part':str(beta),'initial_height':str(height),'last_real_part':str(B),'last_height':str(T)})
    zeta=a(Q(2,3)).zeta();assert zeta<0
    counts['exact_square_divisor_inverse_coefficients']=N;counts['finite_squarefree_count_bound_checks']=N
    return {'hypothetical_reflection_chains':chains,'zeta_at_two_thirds_ball':zeta.str(55),
        'actual_zero_input_used':False,'all_height_argument':'multiplicity at rho/2, symmetry to 1-conjugate(rho)/2; accumulation at nonzero zeta(2/3)',
        'uniform_quarter_power_estimate_proved':False,'machine_formalized':False}


def generic_check(old,p,counts):
    case=old['case'];f=list(map(Q,case['input']));g=[Q(0)]*len(f);g[1]=1/f[1]
    for n in range(2,len(f)):
        g[n]=-sum((g[d]*f[n//d] for d in range(1,n) if n%d==0),Q(0))/f[1]
    assert list(map(Q,old['inverse']))==g
    k,ell,b=map(Q,p['parameters']);X=Q(case['scale']);flint.ctx.prec=640;vec=[]
    for n in range(1,len(g)):
        r=a(X)/n;y=powq(r,ell)
        vec.append([powq(r,k)*sum((a(c)*powq(a(b**j)*y,m)*(-a(b**j)*y).exp() for m,j,c in K['terms']),flint.arb(0)) for K in p['kernels']])
    H=list(map(a,p['metric']['entries']))
    def pair(v,w):return H[0]*v[0]*w[0]+H[1]*(v[0]*w[1]+v[1]*w[0])+H[2]*v[1]*w[1]
    E=flint.arb(0);D=flint.arb(0);C=flint.arb(0)
    for n,v in enumerate(vec,1):
        for m,w in enumerate(vec,1):
            term=a(g[n]*g[m])*pair(v,w);E+=term
            if n==m:D+=term
            else:C+=term
    for name,value in [('energy_ball',E),('diagonal_ball',D),('off_diagonal_ball',C)]:overlap(old[name],value)
    for i,txt in enumerate(old['response_balls']):overlap(txt,sum((a(g[n])*vec[n-1][i] for n in range(1,len(g))),flint.arb(0)))
    assert not old['infinite_tail_claimed'] and not old['squarefree_Euler_identity_claimed']
    counts['generic_inverse_coefficients']+=len(g)-1;counts['generic_direct_arithmetic_pair_terms']+=(len(g)-1)**2


def check(directory,replay=True):
    directory=Path(directory).resolve();spec=read(directory/'protocol.json');seal=read(directory/'seal.json');checks={};counts=defaultdict(int)
    for name,h in spec['code_sha256'].items():assert sha(BASE/name)==h
    for name in spec['this_stage_source_files']:assert sha(directory/'frozen_source'/name)==spec['code_sha256'][name]
    for name,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/name)==h
    from mellin_kernel_report import summary as parent_summary
    parent_summary(spec['source_run'])
    for name,h in seal['files'].items():assert sha(directory/name)==h
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist_at_seal'] and not seal['parameter_cases_exist_at_seal']
    forms=read(directory/'source_forms.json');assert not forms['growth_fits_archive_and_final_outcomes_supplied']
    parent=read(Path(spec['source_run'])/'candidate_batch.json')
    assert forms['programs']==[{k:p[k] for k in ['id','parameter_id','parameters','kernel']} for p in parent['programs']]
    assert forms['pairs']==[{k:g[k] for k in ['id','parameter_id','parameters','member_ids']} for g in parent['banks'] if len(g['member_ids'])==2]
    checks['source_integrity_and_forms_only_discovery']=True
    pc=read(directory/'parameter_cases.json');cal=read(directory/'parameter_calibration.json');cs=read(directory/'calibration_seal.json');cases=read(directory/'final_cases.json');final=read(directory/'final_evaluation.json')
    assert pc['seal_sha256']==sha(directory/'seal.json') and pc['generated_after_archive_seal'] and pc['no_final_scale_information_present']
    assert cal['parameters_sha256']==digest(pc) and cal['training_only'] and not cal['final_scales_used']
    assert cs['archive_seal_sha256']==sha(directory/'seal.json') and cs['parameter_cases_sha256']==sha(directory/'parameter_cases.json') and cs['parameter_calibration_sha256']==sha(directory/'parameter_calibration.json') and not cs['final_cases_exist_at_calibration_seal']
    assert cases['calibration_seal_sha256']==digest(cs) and cases['generated_after_calibration_seal'] and final['cases_sha256']==digest(cases)
    assert final['seal_sha256']==digest(seal) and final['calibration_seal_sha256']==digest(cs)
    excluded_q=set(spec['training_q']+spec['validation_new_q']+spec['parent_final_q_excluded'])|{q for r in spec['retained_failed_runs_are_development'] for q in r['excluded_final_q']}
    excluded_X=set(spec['parent_final_scales_excluded'])|{n for r in spec['retained_failed_runs_are_development'] for n in r['excluded_final_scales']}
    assert not set(pc['fresh_q'])&excluded_q and not set(cases['integers'])&excluded_X
    assert all(spec['final_cases']['range'][0]<=X<=spec['final_cases']['range'][1] for X in cases['integers'])
    checks['two_phase_seal_and_fresh_cases']=True
    replay_files={}
    if replay:
        with tempfile.TemporaryDirectory(prefix='gram-replay-') as temp:
            d=Path(temp);put(d/'protocol.json',spec);put(d/'source_forms.json',forms)
            subprocess.run([sys.executable,str(BASE/'kernel_correlation_search.py'),'worker','--run-dir',str(d)],check=True,cwd=BASE)
            for n,h in seal['files'].items():assert sha(d/n)==h;replay_files[n]=sha(d/n)
    checks['isolated_deterministic_discovery_replay']=replay and replay_files==seal['files']
    batch=read(directory/'candidate_batch.json');validation=read(directory/'validation_data.json');arc=read(directory/'archive.json');discovery=read(directory/'discovery_data.json')
    assert batch['protocol_sha256']==digest(spec) and batch['frozen_before_validation'] and batch['generation_uses_training_only']
    assert validation['candidate_batch_sha256']==sha(directory/'candidate_batch.json') and arc['selection_closed'] and not arc['final_data_used']
    assert all(discovery['worker_access_denials'].values()) and all(cal['worker_access_denials'].values()) and len(discovery['worker_access_denials'])==6
    checks['enforced_no_model_no_network_no_parent_outcome_access']=True
    ps={p['id']:p for p in batch['ablation_programs']+batch['programs']};contexts={}
    for p in ps.values():
        core={k:p[k] for k in ['kind','parameters','kernels','metric']};assert p['id']==digest(core)
        metric_check(p,counts);contexts[p['id']]=diagonal_check(p,counts)
        if p['kind']=='density':density_recovery_check(p,counts);density_constants(p,p['density_constants'],counts)
    checks['exact_signed_products_and_positive_singular_metrics']=True
    checks['native_all_scale_signed_diagonal_and_variation_certificates']=True
    checks['all_height_effective_bank_and_density_strip_certificates']=True
    reflection=arithmetic_and_reflection(final['complete_arithmetic_data']['cutoff'],counts)
    checks['square_divisor_arithmetic_and_reflection_cancellation_guard']=True
    independent_sets={}
    for label,data,points,oldobs in [('training',discovery,spec['training_points'],batch['training_observables']),
        ('validation',validation,spec['validation_points'],validation['program_observables']),
        ('fresh',final['complete_arithmetic_data'],cases['points'],final['program_observables'])]:
        assert data['inverse_coefficient_sha256']==digest(mu_by_factors(data['cutoff'])) and data['all_infinite_tails_included']
        atom_tables={};diagonal_tables={}
        for par,table in data['tables'].items():
            atom_tables[par]=independent_table(table['inverse'],points,2,2,counts)
            diagonal_tables[par]=independent_squarefree(table['squarefree'],points,counts)
        independent_sets[label]={i:obs_check(ps[i],obs,atom_tables[ps[i]['parameter_id']],diagonal_tables[ps[i]['parameter_id']],points,counts) for i,obs in oldobs.items()}
        print('Independent complete arithmetic',label,len(oldobs),'observables',flush=True)
    checks['independent_changed_cutoff_precision_and_Taylor_complete_tails']=True
    checks['complete_Gram_values_and_signed_cross_terms']=True
    byc={c['id']:c for c in batch['candidates']};vcs={c['id']:c for c in validation['candidates']}
    for c in batch['candidates']:
        p=ps[c['program_id']];core={k:c[k] for k in ['program_id','kind','frontier','rho','illustrative_constants_by_q']};assert c['id']==digest(core)
        attempt_check(p,c,counts);fit_check(c,batch['training_observables'][p['id']],c['illustrative_constants_by_q'],spec['training_q']+spec['validation_new_q'],spec,counts)
        cost_check(p,c,c['illustrative_constants_by_q'],spec['training_q'],c['recovery_cost'],spec,counts)
        comparison_check(c,validation['program_observables'][p['id']],c['illustrative_constants_by_q'],spec['training_q']+spec['validation_new_q'],vcs[c['id']]['validation'],counts)
    checks['free_fractional_frontiers_training_constants_and_scope']=True
    checks['fully_charged_conditional_Mellin_observers']=True
    checks['validation_comparisons_and_missing_proof_status']=True
    calcs={o['candidate_id']:o['constants'] for o in cal['illustrative_free_constants']};outcomes={o['candidate_id']:o for o in final['outcomes']}
    for c in arc['archive']:
        assert c==vcs[c['id']];p=ps[c['program_id']];fit_check(c,batch['training_observables'][p['id']],calcs[c['id']],pc['fresh_q'],spec,counts)
        Cs=dict(c['illustrative_constants_by_q'],**calcs[c['id']]);old={str(n):final['program_observables'][p['id']][str(n)] for n in cases['integers']+spec['final_cases']['boundary']}
        comparison_check(c,old,Cs,spec['training_q']+pc['fresh_q'],outcomes[c['id']],counts)
        if c['RH_sufficient_if_uniform']:cost_check(p,c,Cs,pc['fresh_q'],outcomes[c['id']]['fresh_parameter_recovery_cost'],spec,counts)
    checks['fresh_parameters_calibrated_before_fresh_scale_evaluation']=True
    for control in final['negative_controls']:
        c=byc[control['candidate_id']];p=ps[c['program_id']];Cs=dict(c['illustrative_constants_by_q'],**calcs[c['id']]);fake=control['complete_control_observables']
        assert c['RH_sufficient_if_uniform'] and control['analytic_status']=='globally_false_by_uncancelled_pole_at_one' and not control['actual_arithmetic']
        if c['kind']=='density':
            assert control['control_kind']=='wrong_density_center';factor=Q(control['center_factor']);assert factor==Q(spec['wrong_density_center_factor']) and factor!=1
            A=contexts[p['id']][0];assert not A.contains(0)
            for X,row in fake.items():overlap(row['density_correction_ball'],independent_sets['fresh'][p['id']][X]['Z']-a(factor-1)*A*a(X))
        else:
            assert control['diagonal_is_actual_arithmetic_comparator'] and not control['counterfeit_pair_decomposition_claimed']
            H=Q(control['tail_cutoff']);assert H==Q(spec['counterfeit_tail_cutoff']);k,ell,b=map(Q,p['parameters']);aa,h,cc=map(a,p['metric']['entries'])
            for X,row in fake.items():
                fs=[]
                for i,K in enumerate(p['kernels']):
                    err=sum((a(abs(Q(co)))*a(b**(j*m))*powq(a(X),k+ell*m)*powq(a(H),1-k-ell*m)/a(k+ell*m-1) for m,j,co in K['terms']),flint.arb(0))
                    original=independent_sets['fresh'][p['id']][X]['F'][i];v=flint.arb(control['counterfeit_responses'][i][X]);assert v.overlaps(original+flint.arb(0,err));fs.append(v)
                E=aa*fs[0]**2+2*h*fs[0]*fs[1]+cc*fs[1]**2;D=independent_sets['fresh'][p['id']][X]['D']
                overlap(row['energy_ball'],E);overlap(row['diagonal_ball'],D);overlap(row['signed_off_diagonal_ball'],E-D)
            # Parent certificate is checked exactly, so at least one effective
            # numerator is nonzero at the counterfeit pole s=1.
            v=a((k-1)/ell);z=powq(a(b),-(k-1)/ell)
            assert any(not Pvalue(mellin_poly(K),flint.acb(v),flint.acb(z)).contains(0) for K in p['recovery']['effective_kernels'])
        comparison_check(c,fake,Cs,spec['training_q']+pc['fresh_q'],control,counts);counts['analytic_false_controls_checked']+=1
    checks['finite_successful_false_controls_rejected_by_global_arithmetic_gate']=True
    for row in final['all_scale_diagonal_certificate_finite_checks']:
        p=ps[row['program_id']];X=row['scale'];v=independent_sets['fresh'][p['id']][X]['Z'];V=contexts[p['id']][1]
        assert row['passed'] and abs(v)<=V*powq(a(X),Q(1,2));counts['finite_checks_of_true_signed_diagonal_bound']+=1
    for row in final['density_unit_increment_checks']:
        p=ps[row['program_id']];n=row['integer'];offset=Q(spec['final_cases']['real_offset']);zs=independent_sets['fresh'][p['id']];diff=abs(zs[str(Q(n)+offset)]['Z']-zs[str(n)]['Z']);J=density_constants(p)[1]
        assert row['passed'] and diff<=J*a(offset);overlap(row['difference_ball'],diff);overlap(row['bound_ball'],J*a(offset));counts['finite_density_unit_increment_checks']+=1
    for row in final['generic_inputs']:generic_check(row,ps[row['program_id']],counts)
    checks['unrelated_inputs_direct_pair_identity_and_unit_extension']=True
    ac=arc['ablation_comparison'];assert ac['equal_promotion_slot_budgets'] and ac['proposal_slots']==spec['promotion_slots_per_parameter']*len(spec['parameters'])
    assert ac['primary_programs']==len(batch['programs']) and ac['ablation_programs']==len(batch['ablation_programs']) and ac['admitted_promotions']==sum(v['admitted'] for v in batch['promotions'])
    for v in batch['promotions']:
        if v['admitted']:
            parentp=ps[v['parent']];S=list(map(Q,v['matrix']));aa,h,cc=map(Q,parentp['metric']['entries']);u,w,z,t=S
            M=[aa*u*u+2*h*u*z+cc*z*z,aa*u*w+h*(u*t+w*z)+cc*z*t,aa*w*w+2*h*w*t+cc*t*t];scale=max(map(abs,M));M=[x/scale for x in M]
            assert any(p['family']=='promoted_congruence' and p['method']['parent']==v['parent'] and list(map(Q,p['metric']['entries']))==M for p in batch['programs'])
    checks['automatic_congruence_promotion_and_equal_budget_ablation']=True
    assert spec['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[] and not spec['RH_proved'] and not final['RH_proved']
    result={'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_kernel_correlations.py'),'final_sha256':sha(directory/'final_evaluation.json'),
        'checks':checks,'all_passed':all(checks.values()),'counts':dict(counts),'replay_sha256':replay_files,
        'reflection_bridge_audit':reflection,'mathematical_audit_imports_production_code':False,
        'reuses_frozen_independent_math_checker':'check_mellin_kernels.py','machine_formalized':False,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}
    put(directory/'verification.json',result);print('Independent signed correlation checks',sum(checks.values()),'/',len(checks),flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run-dir',type=Path,required=True);args=parser.parse_args();check(args.run_dir)


if __name__=='__main__':main()
