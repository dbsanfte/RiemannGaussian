"""Squarefree density corrections and the ordinary-zero reflection bridge.

No uniform quarter-power estimate is proved by this module. Certificate
search failures remain separate from counterexamples.
"""
from fractions import Fraction as Q
from math import comb,factorial,ceil
import flint
from mellin_kernel_grammar import real,power,serialize,complex_ball,theta,atom_global_bound


def poch(m):
    out=[Q(1)]
    for j in range(m):
        nxt=[Q(0)]*(len(out)+1)
        for i,c in enumerate(out):nxt[i]+=j*c;nxt[i+1]+=c
        out=nxt
    return out


def polynomial(rows):
    out=[Q(0)]*(max(m for m,r,c in rows)+1)
    for m,r,c in rows:
        for j,v in enumerate(poch(m)):out[j]+=Q(c)*v
    while len(out)>1 and out[-1]==0:out.pop()
    return out


def evaluate(c,x):
    value=Q(0)
    for v in reversed(c):value=value*x+v
    return value


def peel(c,j):
    # Exact long division by v+j, with an independently checkable remainder.
    out=[Q(0)]*(len(c)-1);out[-1]=c[-1]
    for i in range(len(out)-2,-1,-1):out[i]=c[i+1]-j*out[i+1]
    if c[0]!=j*out[0]:raise ValueError('Not an exact linear factor')
    return out


def recovery_certificate(rows,k,ell):
    if not rows:return {'kind':'zero_density_observable','all_height_recovery':False,'counterexample_to_bound':False}
    rates={Q(r) for m,r,c in rows}
    if len(rates)!=1:return {'kind':'multiple_rates_missing_recovery_certificate','all_height_recovery':False,
        'counterexample_to_bound':False,'rates':list(map(str,sorted(rates)))}
    P=polynomial(rows)
    if not any(P):return {'kind':'zero_density_observable','all_height_recovery':False,'counterexample_to_bound':False}
    lower=(2*Q(k)-Q(1,2))/Q(ell);rest=P.copy();factors=[]
    for j in range(max(m for m,r,c in rows)+1):
        while len(rest)>1 and evaluate(rest,-Q(j))==0:rest=peel(rest,Q(j));factors.append(j)
    shifted=[sum((c*comb(i,j)*lower**(i-j) for i,c in enumerate(rest) if i>=j),Q(0)) for j in range(len(rest))]
    shifted=[c/rest[-1] for c in shifted]
    good=len(rest)<=3 and all(c>=0 for c in shifted) and shifted[-1]>0
    return {'kind':'common_rate_exact_polynomial_strip_certificate' if good else 'common_rate_missing_polynomial_certificate',
        'all_height_recovery':good,'counterexample_to_bound':False,'common_rate':str(next(iter(rates))),
        'Mellin_polynomial':list(map(str,P)),'peeled_nonpositive_roots':factors,
        'remaining_polynomial':list(map(str,rest)),'shifted_monic_coefficients':list(map(str,shifted)),
        'strict_real_part_lower_bound':str(lower),
        'ordinary_zeta_recovery':'multiplicity plus reflection rho -> 1-conjugate(rho)/2, height halves',
        'sufficient_limiting_density_exponent':'1/4','zero_multiplicities_are_allowed':True}


def reflection_path(beta,height,steps=12):
    beta,height=Q(beta),Q(height)
    if not Q(1,2)<beta<1 or height==0:raise ValueError('Ordinary hypothetical zero right of the critical line required')
    rows=[]
    for _ in range(steps):
        rows.append({'real_part':str(beta),'height':str(height),'distance_from_two_thirds':str(beta-Q(2,3))})
        beta=1-beta/2;height/=2
    return rows


def constants(rows,k,ell,diagonal_certificate,precision=384):
    k,ell=Q(k),Q(ell);flint.ctx.prec=precision;W=flint.arb(0);J=flint.arb(0);local=[]
    for m,r,c in rows:
        r,c=Q(r),Q(c);w=2*k+ell*m
        first=atom_global_bound(2*k,ell,r,m,precision);next_=atom_global_bound(2*k,ell,r,m+1,precision)
        W+=real(abs(c))*first;J+=real(abs(c))*(real(w)*first+real(ell)*next_)
        local.append({'power':str(w),'coefficient_ball':serialize(real(abs(c))*real(r**m)*real(w).zeta()/real(2*w).zeta())})
    A=flint.arb(diagonal_certificate['main_coefficient_ball'])
    return {'absolute_diagonal_bound_constant_ball':serialize(W),'density_unit_increment_constant_ball':serialize(J+abs(A)),
        'local_diagonal_terms':local,'all_real_scale_density_correction_growth_exponent':'1/2',
        'RH_density_growth_exponent_unproved':'1/4'}


def value(data,dc,center_factor=1):
    factor=real(center_factor);A=flint.arb(dc['main_coefficient_ball'])
    return {X:serialize(flint.arb(row['diagonal_ball'])-factor*A*real(X)) for X,row in data.items()}


def frontier(eta,margin,nu,d):
    eta,margin,nu,d=map(Q,(eta,margin,nu,d))
    if eta<Q(1,4) or margin<=0 or nu<=0 or d<0:raise ValueError('Density target requires eta>=1/4, positive approach parameters')
    return {'limit':str(eta),'margin':str(margin),'approach_power':str(nu),'log_power':str(d),
        'constant_quantifiers':'for every q exists finite C_q, for every integer N>=1',
        'constant_growth_in_q_restricted':False,'finite_parameter_grid_suffices':False}


def transfer(program,f,center_factor=1):
    dc=program['diagonal_certificate'];nonzero=not flint.arb(dc['main_coefficient_ball']).contains(0)
    if Q(center_factor)!=1 and nonzero and Q(f['limit'])<1:
        return {'status':'globally_false_uncancelled_density_pole_at_one','RH_sufficient_if_uniform':False,'uniform_premise_proved':False}
    if Q(center_factor)!=1:return {'status':'unresolved_density_normalizer','RH_sufficient_if_uniform':False,'uniform_premise_proved':False}
    rec=program['density_recovery'];eta=Q(f['limit'])
    if eta>=Q(1,2):return {'status':'true_weak_density_frontier','RH_sufficient_if_uniform':False,
        'uniform_premise_proved':True,'same_fitted_constants_proved':False,'constant_witness_ball':dc['signed_remainder_constant_ball']}
    return {'status':'RH_equivalent_density_correction_missing_uniform_signed_proof' if eta==Q(1,4) and rec['all_height_recovery'] else 'density_lead_missing_full_ordinary_zero_bridge',
        'RH_sufficient_if_uniform':eta==Q(1,4) and rec['all_height_recovery'],
        'uniform_premise_proved':False,'finite_parameter_grid_suffices':False}


def charge(program,f,constants_by_q,qs,query,precision=384):
    if not program['density_recovery']['all_height_recovery']:
        return {'status':'missing_all_height_density_recovery','best_log_cost':None,'observers':[]}
    k,ell,b=map(Q,program['parameters']);sigma,t=map(Q,query);flint.ctx.prec=precision
    s=flint.acb(real(sigma),real(t));v=(real(2*k)-s)/real(ell);rec=program['density_recovery']
    P=flint.acb(0)
    for c in reversed(rec['Mellin_polynomial']):P=P*v+real(c)
    factor=v.gamma()*P*(-v*real(rec['common_rate']).log()).exp()/real(ell)
    lower=factor.abs_lower();zeta_lower=s.zeta().abs_lower()
    if not lower>0 or not zeta_lower>0:return {'status':'unresolved_native_density_recovery','best_log_cost':None,'observers':[]}
    gc=program['density_constants'];local=sum((flint.arb(row['coefficient_ball'])/real(Q(row['power'])-sigma) for row in gc['local_diagonal_terms']),flint.arb(0))
    A=abs(flint.arb(program['diagonal_certificate']['main_coefficient_ball']));pole=A/(s-1).abs_lower()
    unit=flint.arb(gc['density_unit_increment_constant_ball'])/real(sigma);d=ceil(Q(f['log_power']));L0=(flint.arb.const_e()+1).log();observers=[]
    for q in qs:
        gap=real(sigma)-theta(f,q)
        if not gap>0:observers.append({'q':q,'status':'outside_density_observer_domain','gap_ball':serialize(gap)});continue
        logarithms=sum((real(Q(factorial(d),factorial(j)*factorial(d-j)))*L0**(d-j)*factorial(j)/gap**(j+1) for j in range(d+1)),flint.arb(0))
        ratio=(local+pole+unit+real(constants_by_q[str(q)])*logarithms)/lower
        cost=ratio/zeta_lower
        observers.append({'q':q,'status':'conditional_signed_density_bound_required','gap_ball':serialize(gap),
            'local_diagonal_cost_ball':serialize(local),'pole_center_cost_ball':serialize(pole),'unit_cost_ball':serialize(unit),
            'native_kernel_transform_ball':complex_ball(factor),'transform_denominator_lower_ball':serialize(lower),
            'native_numerator_zeta_lower_ball':serialize(zeta_lower),
            'conditional_zeta_ratio_bound_ball':serialize(ratio),'conditional_reciprocal_zeta_2s_bound_ball':serialize(cost),
            'log_cost':float(cost.upper().log()),'uniform_signed_premise_proved':False})
    costs=[r['log_cost'] for r in observers if 'log_cost' in r]
    return {'status':'conditional' if costs else 'no_tested_q_inside_density_observer_domain','best_log_cost':min(costs,default=None),
        'observers':observers,'query_for_zeta_ratio':list(map(str,query)),
        'ordinary_zeta_reciprocal_query':list(map(str,(2*sigma,2*t))),
        'reflection_bridge_is_qualitative_all_height':'no sampled zero set is used'}
