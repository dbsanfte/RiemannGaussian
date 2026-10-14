"""Typed lattice arithmetic, global estimate synthesis and a sign-loss barrier.

The actual inverse channel and the constant-coefficient reference have different
Dirichlet series. A bound certified for one cannot be transferred to the other.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,ceil,log2
import flint
from estimate_grammar import inverse_one_prefix
from mellin_kernel_grammar import real,power,serialize,atom_global_bound

VERSION='typed-lattice-defects-inferred-annihilators-global-contours-sign-loss-barrier-v1'


def relative(x):return x.str(85)
def complex_relative(z):return {'real':relative(z.real),'imag':relative(z.imag)}


def shape(terms,rate='2'):
    rate=Q(rate);out={}
    if rate<=0:raise ValueError('Positive rational exponential rate required')
    for m,c in terms:
        if type(m)is not int or m<0:raise ValueError('Nonnegative integer moments required')
        out[m]=out.get(m,Q(0))+Q(c)
    out={m:c for m,c in out.items() if c}
    if not out:raise ValueError('Zero shape excluded')
    scale=max(map(abs,out.values()));orientation=1 if out[max(out)]>0 else -1
    return {'terms':[[m,str(orientation*c/scale)] for m,c in sorted(out.items())],
        'rate':str(rate),'maximum_moment':max(out),
        'semantics':'Q(y)=sum c_m*(R*y)^m*exp(-R*y), y>0; signed coefficients allowed'}


def parameters(K,ell,r):
    K,ell,r=map(Q,(K,ell,r))
    if K<=1 or ell<=0 or r<=1:raise ValueError('K>1, ell>0 and rational r>1 required')
    return K,ell,r


def polynomial(c):
    out=[Q(0)]*(c['maximum_moment']+1)
    for m,v in c['terms']:
        term=[Q(1)]
        for j in range(m):
            nxt=[Q(0)]*(len(term)+1)
            for i,a in enumerate(term):nxt[i]+=j*a;nxt[i+1]+=a
            term=nxt
        for i,a in enumerate(term):out[i]+=Q(v)*a
    while len(out)>1 and out[-1]==0:out.pop()
    return out


def peval(P,x):
    out=Q(0)
    for c in reversed(P):out=out*x+c
    return out


def integer_root(value,degree):
    if value<0 or degree<1:raise ValueError('Positive integer root domain required')
    lo,hi=0,1
    while hi**degree<=value:lo,hi=hi,2*hi
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**degree<=value:lo=mid
        else:hi=mid
    return lo


def pair_prefix(N,r):
    """Exact ordering test for j*d^(p/q)<=N, including boundary equality."""
    r=Q(r);p,q=r.numerator,r.denominator;D=integer_root(N**q,p);mu=inverse_one_prefix(D);pairs=[]
    for d in range(1,D+1):
        M=integer_root(N**q//d**p,q)
        for j in range(1,M+1):pairs.append((j,d,mu[d]))
    return pairs,mu


def moment(K,ell,r,j,model):
    w=K+ell*j
    if model=='inverse':return real(w).zeta()/real(r*w).zeta()
    if model=='unit':return real(w).zeta()*real(r*w).zeta()
    raise ValueError('Arithmetic model must be inverse or unit')


def complete_table(K,ell,r,rate,points,N=None,maximum_moment=4,min_prec=384):
    K,ell,r=parameters(K,ell,r);rate=Q(rate);points=list(map(Q,points))
    if rate<=0 or not points or any(X<=0 for X in points):raise ValueError('Positive rate and scales required')
    N=max(256,2*ceil(max(points))) if N is None else N
    if type(N)is not int or N<1 or type(maximum_moment)is not int or maximum_moment<0:raise ValueError('Integer resource labels required')
    flint.ctx.prec=min_prec;Xmax=max(points);density=real(r).zeta()
    for L in range(12,193,4):
        error=max((power(real(Xmax),K)*(real(rate)*power(real(Xmax),ell))**(m+L)*density
            *real(K+ell*(m+L))*power(real(N),1-K-ell*(m+L))/(real(K+ell*(m+L)-1)*factorial(L))).upper()
            for m in range(maximum_moment+1))
        if error<real(Q(1,2**95)):break
    else:raise ArithmeticError('Complete lattice Taylor budget exhausted')
    precision=max(min_prec,ceil(float(K+ell*(maximum_moment+L))*log2(max(N,2)))+220)
    flint.ctx.prec=precision;pairs,mu=pair_prefix(N,r);weights={'inverse':[],'unit':[]};sums={model:[flint.arb(0) for _ in range(L+maximum_moment)] for model in weights}
    for j,d,a in pairs:
        u=real(j)*power(real(d),r);w=power(u,-K);t=power(u,-ell)
        for model,coefficient in [('inverse',a),('unit',1)]:
            if not coefficient:continue
            weights[model].append((real(coefficient)*w,t));v=real(coefficient)*w
            for h in range(len(sums[model])):sums[model][h]+=v;v*=t
    tails={model:[moment(K,ell,r,h,model)-sums[model][h] for h in range(L+maximum_moment)] for model in weights}
    for model,rows in tails.items():
        for h,v in enumerate(rows):
            w=K+ell*h;bound=density*real(w)*power(real(N),1-w)/real(w-1)
            if not abs(v)<=bound:raise ArithmeticError('Complete lattice tail moment unresolved')
    values={model:{} for model in weights};remainders=[]
    for X in points:
        XK=power(real(X),K);z=real(rate)*power(real(X),ell)
        for model,rows in weights.items():
            prefix=[flint.arb(0) for _ in range(maximum_moment+1)]
            for w,t in rows:
                y=z*t;v=w*(-y).exp()
                for m in range(maximum_moment+1):prefix[m]+=v;v*=y
            for m,v in enumerate(prefix):
                tail=flint.arb(0);mult=z**m
                for h in range(L):tail+=mult*tails[model][m+h];mult*=(-z)/(h+1)
                w=K+ell*(m+L);err=z**(m+L)*density*real(w)*power(real(N),1-w)/(factorial(L)*real(w-1))
                values[model][f'{m}:{X}']=serialize(XK*(v+tail+flint.arb(0,err)))
                if model=='unit':remainders.append({'moment':m,'scale':str(X),'error_ball':serialize(XK*err)})
    return {'parameters':list(map(str,(K,ell,r))),'rate':str(rate),'maximum_moment':maximum_moment,'cutoff':N,
        'precision':precision,'Taylor_terms':L,'prefix_pairs':len(pairs),'inverse_prefix':mu,
        'tail_moment_balls':{m:list(map(serialize,v)) for m,v in tails.items()},'values':values,'tail_bounds':remainders,
        'all_infinite_arithmetic_positions_included':True,
        'model_profiles':{'inverse':'zeta(s)/zeta(r*s)','unit':'zeta(s)*zeta(r*s)'},
        'fractional_r_positions_are_generalized_signed_measures':r.denominator!=1,
        'prime_oracle_used_by_producer':False,'no_RH_input':True}


def transform_at(c,K,ell,s):
    v=(real(K)-s)/real(ell);P=flint.acb(0)
    for a in reversed(polynomial(c)):P=P*v+real(a)
    return v.gamma()*P*(-v*real(c['rate']).log()).exp()/real(ell)


def residues(c,params,precision=512):
    K,ell,r=parameters(*params);R=Q(c['rate']);P=polynomial(c);flint.ctx.prec=precision
    alpha=(K-1)/ell;beta=(K-1/r)/ell
    I=power(real(R),-alpha)*real(alpha).gamma()*real(peval(P,alpha))/real(ell)
    W=power(real(R),-beta)*real(beta).gamma()*real(peval(P,beta))/real(ell)
    B=real(1/r).zeta()*W/real(r)
    return {'Mellin_polynomial':list(map(str,P)),'integral_polynomial_value':str(peval(P,alpha)),
        'secondary_polynomial_value':str(peval(P,beta)),'continuous_integral_ball':serialize(I),
        'inverse_main_ball':serialize(I/real(r).zeta()),'unit_main_ball':serialize(I*real(r).zeta()),
        'unit_secondary_ball':serialize(B),'inverse_secondary_term_claimed':False,
        'pole_positions_for_unit':['1',str(1/r)],'both_reference_residues_vanish':peval(P,alpha)==peval(P,beta)==0}


def responses(c,table,points,res=None):
    res=res or residues(c,table['parameters']);K,ell,r=map(Q,table['parameters']);out={}
    for X in map(Q,points):
        raw={model:sum((real(v)*flint.arb(table['values'][model][f'{m}:{X}']) for m,v in c['terms']),flint.arb(0)) for model in ['inverse','unit']}
        actual=raw['inverse']-flint.arb(res['inverse_main_ball'])*real(X)
        reference=raw['unit']-flint.arb(res['unit_main_ball'])*real(X)-flint.arb(res['unit_secondary_ball'])*power(real(X),1/r)
        out[str(X)]={'inverse_raw_ball':serialize(raw['inverse']),'inverse_centered_ball':serialize(actual),
            'unit_raw_ball':serialize(raw['unit']),'unit_two_residue_residual_ball':serialize(reference)}
    return out


def weak_actual(c,params,precision=512):
    K,ell,r=parameters(*params);R=Q(c['rate']);flint.ctx.prec=precision;U=flint.arb(0)
    for m,a in c['terms']:
        beta=(K-1/r)/ell+m
        atom=power(real(R),(1/r-K)/ell)*real(beta).gamma()*(real(K+ell*m)+real(ell*beta))/real(ell)
        U+=real(abs(Q(a)))*atom
    count_constant=real(Q(1,2))+power(real(2),r-1)/real(r-1)
    return {'constant_ball':serialize(count_constant*U),'count_constant_ball':serialize(count_constant),
        'variation_ball':serialize(U),'growth_exponent':str(1/r),'ordinary_zeta_normalized_exponent':'1',
        'all_real_scales':True,'RH_strength':False,
        'count_identity':'Q_r(x)=sum_d mu(d)*floor(x/d^r)',
        'integer_r_free_indicator':r.denominator==1,'imported_prime_distribution_bound':False}


def local_lattice(c,K,ell,Y,terms=112,precision=512):
    """Complete one-dimensional lattice G(Y), useful for barrier calibration."""
    K,ell,Y,R=map(Q,(K,ell,Y,c['rate']));flint.ctx.prec=precision;z=real(R)*power(real(Y),ell);value=flint.arb(0);error=flint.arb(0)
    for m,a in c['terms']:
        total=flint.arb(0);mult=z**m
        for j in range(terms):total+=mult*real(K+ell*(m+j)).zeta();mult*=(-z)/(j+1)
        err=z**(m+terms)*real(K+ell*(m+terms)).zeta()/factorial(terms)
        value+=real(a)*total;error+=real(abs(Q(a)))*err
    return power(real(Y),K)*(value+flint.arb(0,error))


def sign_loss_barrier(c,params,res=None,maximum_halvings=512,precision=512):
    K,ell,r=parameters(*params);R=Q(c['rate']);res=res or residues(c,params);P=polynomial(c);alpha=(K-1)/ell
    flint.ctx.prec=precision;I=flint.arb(res['continuous_integral_ball']);zero=peval(P,alpha)==0
    if not zero:
        lead=abs(I);w=Q(1);mode='nonzero_continuous_mass'
        if not lead>0:return {'status':'missing_native_nonzero_integral_certificate','counterexample_to_actual_bound':False}
    else:
        m0,a0=c['terms'][0];w=K+ell*m0;lead=real(abs(Q(a0))*R**m0)*real(w).zeta();mode='zero_mass_first_nonzero_lattice_coefficient'
    for steps in range(maximum_halvings+1):
        Y0=Q(1,2**steps)
        if not zero:
            remainder=sum((real(abs(Q(a))*R**m)*real(K+ell*m).zeta()*power(real(Y0),K+ell*m-1) for m,a in c['terms']),flint.arb(0))
        else:
            remainder=real(abs(Q(a0))*R**(m0+1))*real(w+ell).zeta()*power(real(Y0),ell)
            remainder+=sum((real(abs(Q(a))*R**m)*real(K+ell*m).zeta()*power(real(Y0),K+ell*m-w) for m,a in c['terms'] if m>m0),flint.arb(0))
        if remainder<=lead/2:break
    else:return {'status':'missing_barrier_halving_resource','counterexample_to_actual_bound':False}
    lower=lead*power(real(Y0),w-1/r)/(power(real(2),r*w)*real(r*w-1))
    if not lower>0:raise ArithmeticError('Positive sign-loss barrier required')
    squarefree_density=1/real(2).zeta();M0=1
    while not squarefree_density*real(M0)/2>=real(Q(5,2))*((2*real(M0)).sqrt()+real(M0).sqrt()):M0*=2
    support_lower=squarefree_density*lead*power(real(Y0),w-1/r)/power(real(2),2*r*w+1)
    return {'status':'certified_absolute_rewrite_barrier','mode':mode,'small_scale_cutoff':str(Y0),
        'local_power':str(w),'leading_coefficient_ball':relative(lead),'remainder_coefficient_ball':relative(remainder),
        'lower_constant_ball':relative(lower),'barrier_growth_exponent':str(1/r),'ordinary_normalized_exponent':'1',
        'theorem':'sum_d |G(X/d^r)-I*X/d^r| >= b*X^(1/r), every X>=Y0',
        'actual_support_lower_constant_ball':relative(support_lower),'squarefree_density_ball':relative(squarefree_density),
        'squarefree_interval_threshold':M0,'actual_support_onset_ball':relative(real(Y0)*power(real(M0),r)),
        'actual_support_theorem':'sum_d |mu(d)|*|G(X/d^r)-I*X/d^r| >= b_support*X^(1/r), X>=Y0*M0^r',
        'retaining_actual_squarefree_support_does_not_remove_the_barrier':True,
        'rules_out_only':'certificates using the post-rewrite absolute norm, including methods that retain the actual squarefree support but discard sign orientation',
        'counterexample_to_actual_bound':False,'actual_signed_cancellation_can_be_stronger':True}


def positive_polynomial_bound(c,alpha,ell):
    out=[Q(0)]*(c['maximum_moment']+1)
    for m,a in c['terms']:
        row=[Q(1)]
        for j in range(m):
            nxt=[Q(0)]*(len(row)+1)
            for i,v in enumerate(row):nxt[i]+=(alpha+j)*v;nxt[i+1]+=v/ell
            row=nxt
        for j,v in enumerate(row):out[j]+=abs(Q(a))*v
    return out


def reference_decay(c,params,a,ray_pairs=None,precision=512):
    """Synthesized true all-scale negative-power bounds for the unit channel."""
    K,ell,r=parameters(*params);a=Q(a);R=Q(c['rate'])
    if a<=0:raise ValueError('Positive rational decay order required')
    ray_pairs=ray_pairs or [(u,v) for u in [Q(1,6),Q(1,4),Q(1,3)] for v in [Q(1,4),Q(1,2),Q(3,4)]]
    flint.ctx.prec=precision;pi=flint.arb.pi();alpha=(K+a)/ell;D=positive_polynomial_bound(c,alpha,ell);rows=[]
    for ray,fraction in ray_pairs:
        ray,fraction=Q(ray),Q(fraction)
        if not 0<ray<Q(1,2) or not 0<fraction<1:raise ValueError('Gamma rotation angles must be internal')
        delta_pi=ray*fraction/((1+r)*max(ell,Q(1)));decay_pi=ray/ell-(1+r)*delta_pi
        if decay_pi<=0:continue
        delta=real(delta_pi)*pi;kappa=real(decay_pi)*pi;cos_kernel=(real(ray)*pi).cos();cos_zeta=delta.sin()
        kernel=real(alpha).gamma()*power(cos_kernel,-alpha)*power(real(R),-alpha)/real(ell)
        zetas=[]
        for slope in [Q(1),r]:
            A=slope*a
            zetas.append(power(real(2),-A)*power(pi,-A-1)*real(1+A).gamma()*power(cos_zeta,-1-A)*real(1+A).zeta())
        integral=sum((real(v)*factorial(j)/kappa**(j+1) for j,v in enumerate(D)),flint.arb(0))
        C=kernel*zetas[0]*zetas[1]*integral/pi
        rows.append({'kernel_ray_pi_fraction':str(ray),'decay_allocation_fraction':str(fraction),
            'zeta_complement_angle_pi_fraction':str(delta_pi),'net_decay_pi_fraction':str(decay_pi),
            'kernel_bound_prefactor_ball':relative(kernel),'zeta_bound_prefactor_balls':list(map(relative,zetas)),
            'height_polynomial_coefficients':list(map(str,D)),'height_integral_bound_ball':relative(integral),
            'global_constant_ball':relative(C),'log_constant':float(C.upper().log())})
    if not rows:raise ArithmeticError('No global Gamma decay certificate')
    best=min(rows,key=lambda row:row['log_constant'])
    return {'status':'true_all_scale_unit_channel_decay','arithmetic_model':'unit','Dirichlet_profile':'zeta(s)*zeta(r*s)',
        'subtract_both_known_residues':True,'decay_order':str(a),'growth_exponent':str(-a),
        'all_real_scales':True,'constant_ball':best['global_constant_ball'],'best_ray':best,'ray_certificates':rows,
        'RH_consequence':False,'actual_inverse_estimate_proved':False,
        'proof_backend':'rotated Euler Gamma integral, zeta functional equation, fully bounded inverse Mellin contour'}


def enforce_certificate_arithmetic(certificate,model):
    if certificate['arithmetic_model']!=model:raise ValueError('Arithmetic input mismatch: a unit-channel proof is not an inverse-channel proof')
    return True


def global_constants(c,params,res=None,precision=512):
    K,ell,r=parameters(*params);R=Q(c['rate']);flint.ctx.prec=precision;J=flint.arb(0);local=[]
    for m,a in c['terms']:
        w=K+ell*m
        # The inherited integral+peak bound applies at Y>=1. Dilation also
        # samples Y=X/d^r<1, so supply a separate local majorant there.
        first=atom_global_bound(K,ell,R,m,precision)+real(R**m)*real(w).zeta()
        next_=atom_global_bound(K,ell,R,m+1,precision)+real(R**(m+1))*real(w+ell).zeta()
        J+=real(abs(Q(a)))*(real(w)*first+real(ell)*next_)
        local.append({'power':str(w),'coefficient_ball':serialize(real(abs(Q(a))*R**m)*real(w).zeta()*real(r*w).zeta())})
    res=res or residues(c,params);A=abs(flint.arb(res['inverse_main_ball']))
    return {'inverse_unit_increment_constant_ball':serialize(real(r).zeta()*J+A),
        'local_absolute_lattice_terms':local,'all_real_scale_derivative_of_raw_lattice_proved':True,
        'small_dilated_scale_majorant_included':True,
        'source_measure_absolute_density_cost_ball':serialize(real(r).zeta())}


def frontier(r,ordinary_eta,margin,nu,d):
    r,eta,margin,nu,d=map(Q,(r,ordinary_eta,margin,nu,d))
    if r<=1 or eta<Q(1,2) or margin<=0 or nu<=0 or d<0:raise ValueError('Admissible normalized cofinal target required')
    return {'ordinary_limit':str(eta),'limit':str(eta/r),'ordinary_margin':str(margin),'margin':str(margin/r),
        'approach_power':str(nu),'log_power':str(d),'constant_growth_in_q_restricted':False,
        'finite_parameter_grid_suffices':False,'constant_quantifiers':'for every q exists finite C_q, for every integer N>=1',
        'ordinary_exponent_equals_r_times_density_exponent':True}


@lru_cache(maxsize=None)
def growth(eta,margin,nu,d,q,X):
    t=real(eta)+real(margin)/power(real(q),Q(nu))
    return (t*real(X).log()).exp()*power((flint.arb.const_e()+real(X)).log(),Q(d))


def env(f,q,X):return growth(f['limit'],f['margin'],f['approach_power'],f['log_power'],q,str(X))


def attempt(p,f):
    if Q(f['ordinary_limit'])>=1:
        return {'status':'true_all_scale_inverse_density_frontier','uniform_premise_proved':True,
            'same_fitted_constants_proved':False,'constant_witness_ball':p['weak_actual']['constant_ball'],'RH_strength':False}
    return {'status':'signed_inverse_dilation_cancellation_required','uniform_premise_proved':False,
        'absolute_rewrite_barrier':p['sign_loss_barrier']['status'],'counterexample_to_actual_bound':False,
        'reference_contour_certificate_cannot_be_reused':True,'unproved_analytic_obligation':'ordinary denominator zeros of zeta(r*s) in the requested strip'}


def charge(p,f,Cs,qs,query=('5/8','16'),precision=512):
    if not p['zero_bridge']['all_right_half_ordinary_zeros_preserved']:
        return {'status':'missing_actual_ordinary_zero_bridge','best_log_cost':None,'observers':[]}
    K,ell,r=map(Q,p['parameters']);sigma,t=map(Q,query);flint.ctx.prec=precision;s=flint.acb(real(sigma/r),real(t/r))
    W=transform_at(p['shape'],K,ell,s);denom=W.abs_lower();zeta=s.zeta().abs_lower()
    if not denom>0 or not zeta>0:return {'status':'query_kernel_or_numerator_zero_not_excluded','best_log_cost':None,'observers':[]}
    gc=p['global_constants'];A=abs(flint.arb(p['residues']['inverse_main_ball']));local=sum((flint.arb(v['coefficient_ball'])/real(Q(v['power'])-sigma/r) for v in gc['local_absolute_lattice_terms']),flint.arb(0))
    pole=A/(s-1).abs_lower();unit=flint.arb(gc['inverse_unit_increment_constant_ball'])/real(sigma/r)
    d=ceil(Q(f['log_power']));L0=(flint.arb.const_e()+1).log();rows=[]
    for q in qs:
        gap=real(sigma/r)-real(f['limit'])-real(f['margin'])/power(real(q),Q(f['approach_power']))
        if not gap>0:rows.append({'q':q,'status':'outside_observer_domain','gap_ball':relative(gap)});continue
        logs=sum((real(Q(factorial(d),factorial(j)*factorial(d-j)))*L0**(d-j)*factorial(j)/gap**(j+1) for j in range(d+1)),flint.arb(0))
        ratio=(local+pole+unit+real(Cs[str(q)])*logs)/denom;cost=ratio/zeta
        rows.append({'q':q,'status':'conditional_signed_actual_density_bound_required','gap_ball':relative(gap),
            'local_cost_ball':relative(local),'pole_cost_ball':relative(pole),'unit_cost_ball':relative(unit),
            'kernel_transform_ball':complex_relative(W),'kernel_denominator_lower_ball':relative(denom),
            'numerator_zeta_lower_ball':relative(zeta),'conditional_reciprocal_bound_ball':relative(cost),
            'log_cost':float(cost.upper().log()),'uniform_signed_premise_proved':False})
    costs=[v['log_cost'] for v in rows if 'log_cost' in v]
    return {'status':'conditional' if costs else 'no_q_inside_observer_domain','best_log_cost':min(costs,default=None),
        'observers':rows,'ordinary_zeta_query':list(map(str,query)),'ratio_query':[str(sigma/r),str(t/r)],
        'single_observer_is_not_all_height_quantitative_control':True}
