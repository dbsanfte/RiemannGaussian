"""Normalized root arithmetic, complete signed moments and exact cancellation.

Arithmetic dilation r can be any positive rational. The actual inverse and
unit reference remain different types. Kernel peaks are normalized to avoid
confounding arithmetic coverage with a change in the displayed scale.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,ceil,log
import flint
from mellin_kernel_grammar import real,power,serialize
from lattice_zero_bridge import root_certificate,exceptional_real_parts

VERSION='normalized-arithmetic-root-moments-signed-profile-collapse-Prony-escaping-zero-chain-v1'
def relative(v):return v.str(85)


def parameters(K,ell,r):
    K,ell,r=map(Q,(K,ell,r))
    if r<=0 or ell<=0 or K<=max(Q(1),1/r):raise ValueError('r>0, ell>0, K>max(1,1/r) required')
    return K,ell,r


def shape(terms):
    out={}
    for m,c in terms:
        if type(m)is not int or m<0:raise ValueError('Nonnegative integer moments required')
        out[m]=out.get(m,Q(0))+Q(c)
    out={m:c for m,c in out.items() if c}
    if not out:raise ValueError('Zero shape excluded')
    scale=max(map(abs,out.values()));orientation=1 if out[max(out)]>0 else -1
    return {'terms':[[m,str(orientation*c/scale)] for m,c in sorted(out.items())],
        'maximum_moment':max(out),'semantics':'g(u)=u^K*sum c_m*u^(ell*m)*exp(R*(1-u^ell)), R=K/ell'}


def rate(params):K,ell,r=parameters(*params);return K/ell
def mellin_shape(c,params):
    R=rate(params)
    return {'terms':[[m,str(Q(a)/R**m)] for m,a in c['terms']],'maximum_moment':c['maximum_moment'],'rate':str(R)}


def polynomial(c,params):
    from lattice_synthesis_grammar import polynomial as frozen_polynomial
    return frozen_polynomial(mellin_shape(c,params))


def profile(model,r):
    r=Q(r)
    if model not in ['inverse','unit']:raise ValueError('Declared arithmetic input required')
    factors=[('1',1),(str(r),-1 if model=='inverse' else 1)];out={}
    for slope,n in factors:out[Q(slope)]=out.get(Q(slope),0)+n
    return {'model':model,'input_factors':[[s,n] for s,n in factors],
        'remaining_factors':[[str(s),n] for s,n in sorted(out.items()) if n],
        'semantics':'product zeta(slope*s)^multiplicity; valid first in the absolute-convergence halfplane'}


@lru_cache(maxsize=None)
def native_zeta(w,precision):
    if flint.ctx.prec!=precision:raise ValueError('Precision-specific moment cache required')
    return real(w).zeta()


def complete_table(params,index_points,maximum_moment=4,min_prec=384,max_terms=2048):
    K,ell,r=parameters(*params);R=K/ell;points=list(map(Q,index_points))
    if not points or min(points)<=0:raise ValueError('Positive arithmetic index scales required')
    flint.ctx.prec=min_prec;Mmax=max(points);zmax=real(R)*power(real(Mmax),r*ell)
    for L in range(16,max_terms+1,8):
        errors=[real(R).exp()*power(real(Mmax),r*(K+ell*m))*zmax**L/factorial(L)
            *real(K+ell*(m+L)).zeta()*real(r*(K+ell*(m+L))).zeta() for m in range(maximum_moment+1)]
        if max(v.upper() for v in errors)<real(Q(1,2**100)):break
    else:raise ArithmeticError('Whole signed-moment Taylor resource exhausted')
    precision=max(min_prec,ceil(float((zmax+real(R)+real(r*(K+ell*maximum_moment))*real(max(Mmax,Q(1))).log()).upper())/log(2))+240)
    flint.ctx.prec=precision;moments={model:[] for model in ['inverse','unit']}
    for h in range(L+maximum_moment):
        w=K+ell*h;zw=native_zeta(str(w),precision);zrw=native_zeta(str(r*w),precision)
        moments['inverse'].append(zw/zrw);moments['unit'].append(zw*zrw)
    values={model:{} for model in moments};errors=[]
    for M in points:
        z=real(R)*power(real(M),r*ell)
        for m in range(maximum_moment+1):
            scale=real(R).exp()*power(real(M),r*(K+ell*m));w=K+ell*(m+L)
            error=scale*z**L/factorial(L)*native_zeta(str(w),precision)*native_zeta(str(r*w),precision)
            for model,rows in moments.items():
                v=flint.arb(0);weight=flint.arb(1)
                for h in range(L):v+=weight*rows[m+h];weight*=(-z)/(h+1)
                values[model][f'{m}:{M}']=serialize(scale*v+flint.arb(0,error))
            errors.append({'moment':m,'index_scale':str(M),'error_ball':relative(error)})
    return {'parameters':list(map(str,(K,ell,r))),'rate':str(R),'index_points':list(map(str,points)),
        'scale_semantics':'X=M^r exactly; the arithmetic-index variable M has the same ordinary-zeta exponent for every r',
        'maximum_moment':maximum_moment,'Taylor_terms':L,'precision':precision,'moments':{m:list(map(relative,v)) for m,v in moments.items()},
        'values':values,'Taylor_error_balls':errors,'all_infinite_arithmetic_positions_included':True,
        'no_finite_lattice_substitution':True,'all_moment_arguments_greater_than_one':True,'RH_input_used':False,'prime_oracle_used':False}


def residues(c,params,precision=512):
    K,ell,r=parameters(*params);R=K/ell;flint.ctx.prec=precision;P=polynomial(c,params);alpha=(K-1)/ell
    val=sum((b*alpha**j for j,b in enumerate(P)),Q(0));I=real(R).exp()*power(real(R),-alpha)*real(alpha).gamma()*real(val)/real(ell)
    A=flint.arb(0) if not profile('inverse',r)['remaining_factors'] else I/real(r).zeta()
    return {'Mellin_polynomial':list(map(str,P)),'continuous_integral_ball':serialize(I),'actual_main_ball':serialize(A),
        'ordinary_main_pole_position':str(r),'main_term_in_index_variable':'A*M^r','r_one_main_residue_is_exact_zero':r==1}


def responses(c,table,points,res=None):
    res=res or residues(c,table['parameters']);K,ell,r=map(Q,table['parameters']);out={}
    for M in map(Q,points):
        raw={model:sum((real(a)*flint.arb(table['values'][model][f'{m}:{M}']) for m,a in c['terms']),flint.arb(0)) for model in ['inverse','unit']}
        out[str(M)]={'actual_raw_ball':serialize(raw['inverse']),'actual_centered_ball':serialize(raw['inverse']-flint.arb(res['actual_main_ball'])*power(real(M),r)),
            'unit_raw_ball':serialize(raw['unit'])}
    return out


def finite_response(c,params,M,precision=512):
    K,ell,r=parameters(*params)
    if profile('inverse',r)['remaining_factors']:raise ValueError('No certified finite support')
    flint.ctx.prec=precision;R=K/ell;y=power(real(M),ell)
    return power(real(M),K)*(real(R)*(1-y)).exp()*sum((real(a)*y**m for m,a in c['terms']),flint.arb(0))


def zero_bridge(c,params,maximum_steps=128):
    K,ell,r=parameters(*params);kernel=root_certificate(mellin_shape(c,params),params)
    base={'kernel_certificate':kernel,'arithmetic_profile':profile('inverse',r),'uniform_critical_estimate_proved':False,'sampled_zeta_zeros_used':False}
    if not base['arithmetic_profile']['remaining_factors']:
        return dict(base,kind='exact_arithmetic_zero_erasure',RH_sufficient_if_uniform=False,ordinary_zeta_information_preserved=False,
            reason='the arithmetic numerator and denominator cancel at every ordinary zero; a kernel-only certificate is insufficient')
    if not kernel['all_right_half_ordinary_zeros_preserved']:return dict(base,kind='missing_kernel_zero_preservation',RH_sufficient_if_uniform=False,ordinary_zeta_information_preserved=False)
    if r<1:
        v=Q(1)
        for j in range(1,maximum_steps+1):
            v*=r
            if v<=Q(1,2):return dict(base,kind='finite_division_escape',RH_sufficient_if_uniform=True,ordinary_zeta_information_preserved=True,
                worst_case_divisions=j,exact_final_r_power=str(v),all_heights_and_multiplicities=True,
                reason='numerator cancellation repeatedly forces beta/r; after finitely many divisions its real part exceeds 1')
        return dict(base,kind='missing_escape_resource',RH_sufficient_if_uniform=False,ordinary_zeta_information_preserved=False,counterexample_to_growth=False)
    exceptions=exceptional_real_parts(r,maximum_steps)
    return dict(base,kind='expanding_reflection_constraints',RH_sufficient_if_uniform=exceptions['complete'] and not exceptions['real_parts'],
        ordinary_zeta_information_preserved=exceptions['complete'],zero_exceptions=exceptions)


def rapid_certificate(c,params,order,model='inverse',precision=512):
    K,ell,r=parameters(*params);order=Q(order);ledger=profile(model,r)
    if order<=0:raise ValueError('Positive rational decay order required')
    if ledger['remaining_factors']:return {'status':'missing_signed_profile_collapse','global_premise_proved':False,'counterexample_to_growth':False,'arithmetic_model':model}
    R=K/ell;flint.ctx.prec=precision;C=flint.arb(0);atoms=[]
    for m,a in c['terms']:
        alpha=(K+order)/ell+m;value=real(R).exp()*real(abs(Q(a)))*power(real(R),-alpha)*power(real(alpha),alpha)*(-real(alpha)).exp()
        C+=value;atoms.append({'moment':m,'peak_parameter':str(alpha),'constant_ball':relative(value)})
    return {'status':'true_signed_actual_all_scale_rapid_decay','arithmetic_model':model,'profile_certificate':ledger,
        'decay_order':str(order),'constant_ball':relative(C),'atom_certificates':atoms,'all_real_positive_scales':True,
        'global_premise_proved':True,'M_observable_equals_single_input_response':True,'M_equals_X_here':r==1,
        'ordinary_zeta_information_preserved':False,'RH_consequence':False,
        'proof_backend':'exact signed arithmetic factor cancellation before estimating the remaining finite kernel'}


def enforce_type(cert,model):
    if cert['arithmetic_model']!=model:raise ValueError('Signed certificate arithmetic input mismatch')
    return True


def global_constants(c,params,res=None,precision=512):
    K,ell,r=parameters(*params);R=K/ell;flint.ctx.prec=precision;res=res or residues(c,params);local=[]
    for m,a in c['terms']:
        w=K+ell*m;local.append({'power':str(r*w),'coefficient_ball':serialize(real(R).exp()*real(abs(Q(a)))*real(w).zeta()*real(r*w).zeta())})
    if r>=1:return {'status':'not_the_small_root_weak_backend','local_terms':local,'global_ordinary_exponent_one_proved':False}
    p=1/r;density=real(p).zeta()
    def atom(m):
        beta=(K-p)/ell+m
        return density*real(R).exp()*power(real(R),-beta)*real(beta).gamma()*(real(K+ell*m)+real(ell*beta))/real(ell)
    B=flint.arb(0);J=flint.arb(0)
    for m,a in c['terms']:
        a=real(abs(Q(a)));B+=a*atom(m);J+=a*(real(K+ell*m)*atom(m)+real(R*ell)*atom(m+1))
    A=abs(flint.arb(res['actual_main_ball']))
    return {'status':'true_small_root_global_weak_and_unit_bounds','ordinary_exponent':'1','constant_ball':serialize(B+A),
        'unit_increment_constant_ball':serialize(real(r)*(J+A)),'local_terms':local,
        'all_M_at_least_one':True,'global_ordinary_exponent_one_proved':True,'RH_strength':False,
        'unsigned_count_bound':'#{(j,d): j*d^r<=t}<=zeta(1/r)*t^(1/r), by summing over j'}


def frontier(eta,margin,nu,d):
    eta,margin,nu,d=map(Q,(eta,margin,nu,d))
    if eta<Q(1,2) or margin<=0 or nu<=0 or d<0:raise ValueError('Cofinal index frontier required')
    return {'limit':str(eta),'margin':str(margin),'approach_power':str(nu),'log_power':str(d),
        'variable':'ordinary arithmetic index M, X=M^r','quantifiers':'for every q exists finite C_q, for every real M>=1',
        'constants_in_q_restricted':False,'finite_q_grid_suffices':False}


@lru_cache(maxsize=None)
def growth(eta,margin,nu,d,q,M):
    theta=real(eta)+real(margin)/power(real(q),Q(nu))
    return (theta*real(M).log()).exp()*power((flint.arb.const_e()+real(M)).log(),Q(d))
def envelope(f,q,M):return growth(f['limit'],f['margin'],f['approach_power'],f['log_power'],q,str(M))


def charge(p,f,Cs,qs,query=('5/8','16'),precision=640):
    bridge=p['zero_bridge']
    if not bridge['RH_sufficient_if_uniform']:return {'status':'missing_ordinary_zeta_recovery','best_log_cost':None,'observers':[]}
    if not p['global_constants'].get('global_ordinary_exponent_one_proved'):
        return {'status':'missing_normalized_unit_increment_backend','best_log_cost':None,'observers':[]}
    K,ell,r=map(Q,p['parameters']);R=K/ell;flint.ctx.prec=precision;sig,t=map(Q,query);z=flint.acb(real(sig),real(t));v,base,num=observer_base(str(K),str(ell),str(r),str(sig),str(t),precision);P=polynomial(p['shape'],p['parameters']);pv=flint.acb(0)
    for a in reversed(P):pv=pv*v+real(a)
    W=base*pv;denom=W.abs_lower()
    if not denom>0 or not num>0:return {'status':'observer_transform_or_numerator_zero','best_log_cost':None,'observers':[]}
    gc=p['global_constants'];local=sum((flint.arb(a['coefficient_ball'])/real(Q(a['power'])-sig) for a in gc['local_terms']),flint.arb(0));pole=abs(flint.arb(p['residues']['actual_main_ball']))/(z-real(r)).abs_lower();unit=flint.arb(gc['unit_increment_constant_ball'])/real(sig);d=ceil(Q(f['log_power']));L0=(flint.arb.const_e()+1).log();out=[]
    for q in qs:
        gap=real(sig)-real(f['limit'])-real(f['margin'])/power(real(q),Q(f['approach_power']))
        if not gap>0:out.append({'q':q,'status':'outside_observer_domain','gap_ball':relative(gap)});continue
        integral=sum((real(Q(factorial(d),factorial(j)*factorial(d-j)))*L0**(d-j)*factorial(j)/gap**(j+1) for j in range(d+1)),flint.arb(0));cost=(local+pole+unit+real(Cs[str(q)])*integral)/denom/num
        out.append({'q':q,'status':'conditional_signed_critical_bound_required','gap_ball':relative(gap),'local_cost_ball':relative(local),'pole_cost_ball':relative(pole),'unit_cost_ball':relative(unit),
            'transform_ball':{'real':relative(W.real),'imag':relative(W.imag)},'transform_denominator_lower_ball':relative(denom),
            'numerator_zeta_lower_ball':relative(num),'conditional_reciprocal_bound_ball':relative(cost),'log_cost':float(cost.upper().log()),'uniform_critical_premise_proved':False})
    return {'status':'conditional','best_log_cost':min((v['log_cost'] for v in out if 'log_cost' in v),default=None),'observers':out,
        'ordinary_zeta_query':list(map(str,query)),'single_query_is_not_all_height_control':True}


@lru_cache(maxsize=None)
def observer_base(K,ell,r,sig,t,precision):
    if flint.ctx.prec!=precision:raise ValueError('Native observer precision mismatch')
    K,ell,r,sig,t=map(Q,(K,ell,r,sig,t));s=flint.acb(real(sig/r),real(t/r));v=(real(K)-s)/real(ell);R=K/ell
    return v,real(R).exp()*v.gamma()*(-v*real(R).log()).exp()/real(ell*r),s.zeta().abs_lower()


def late_tail_bound(c,params,M,cutoff_power=8192,precision=640):
    K,ell,r=parameters(*params);R=K/ell;flint.ctx.prec=precision;out=flint.arb(0)
    for m,a in c['terms']:
        w=K+ell*m
        out+=real(abs(Q(a)))*real(R).exp()*power(real(M),r*w)*real(w).zeta()*(real((1-r*w)*cutoff_power)*real(2).log()).exp()/real(r*w-1)
    return out


def late_tail_pole(c,params,precision=640):
    K,ell,r=parameters(*params);R=K/ell;P=polynomial(c,params);v=(K-1/r)/ell;pv=sum((a*v**j for j,a in enumerate(P)),Q(0));flint.ctx.prec=precision
    if not pv:return {'applies':False,'counterexample_to_actual_growth':False,'reason':'kernel exactly masks the added ordinary pole at 1'}
    W=real(R).exp()*power(real(R),-v)*real(v).gamma()*real(pv)/real(ell*r)
    coefficient=W*real(1/r).zeta() if r!=1 else W
    return {'applies':True,'pole_position':'1','pole_order':2 if r==1 else 1,'leading_coefficient_ball':relative(coefficient),
        'globally_false_at_ordinary_limit_half':True,'actual_arithmetic_changed_only_above_cutoff':True,'counterexample_to_actual_growth':False}
