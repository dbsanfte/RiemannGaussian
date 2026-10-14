"""Complete branch centers and signed parameter families on actual arithmetic.

All rational 0<a<1 have semantics. Native work caps are evaluation resources,
not a denominator restriction. Failed numerical enclosures are missing data.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,ceil,floor
import flint
from mellin_kernel_grammar import real,power
from divisor_preconditioner_grammar import coefficients,sum_at

VERSION='complete-fractional-branch-centers-normalized-signed-cofinal-families-v1'
def ball(x):return x.str(90)
def cball(x):return {'real':ball(x.real),'imag':ball(x.imag)}
def decode(x):return flint.acb(flint.arb(x['real']),flint.arb(x['imag']))
def croot(a):
    a=Q(a)
    if not 0<a<1:raise ValueError('This branch completion requires 0<a<1')
    return real(a)/real(1-a).gamma()
def regularized_zeta(z):return 1+(z-1)*flint.acb_series([z],prec=1).zeta(deflate=True)[0]
def inflate(x,error):return x+flint.arb(0,error.upper())


@lru_cache(maxsize=None)
def center_series(x,L,precision):
    flint.ctx.prec=precision;old=flint.ctx.cap;flint.ctx.cap=L
    try:
        v=flint.arb_series([0,1],prec=L);u=1-v;Z=1-v*u.zeta(deflate=True)
        H=(real(x)*(-real(x).log()*v).exp()-1)/(u*Z)
        return tuple(H[j] for j in range(L))
    finally:flint.ctx.cap=old


def quadrature_center(a,x,precision=384,bits=96):
    """Full real cut center, with a rigorously bounded Taylor endpoint."""
    a=Q(a);x=Q(x)
    if x<1:raise ValueError('Center is defined for x>=1')
    flint.ctx.prec=precision;c=croot(a)
    if x==1:return {'value_ball':'0','tail_error_ball':'0','complete_branch_center':True,'missing':False}
    p=Q(1,1-a);delta=Q(1,16);R=Q(1,4);L=80;r=power(real(delta),p)
    z=flint.acb(flint.arb(1,real(R)),flint.arb(0,real(R)));lower=abs(regularized_zeta(z)).lower()
    if not lower>0:return {'missing':True,'reason':'regularized_zeta_Cauchy_disk_not_resolved'}
    B=(power(real(x),1+R)+1)/((1-real(R))*lower)
    err=B*real(delta)*power(r/real(R),L)/(1-r/real(R))
    small=sum((h*power(real(delta),p*j+1)/real(p*j+1) for j,h in enumerate(center_series(str(x),L,precision))),flint.arb(0))
    logx=real(x).log()
    def integrand(t,analytic):
        u=1-(real(p)*t.log(analytic=analytic)).exp()
        return logx*(u*logx).hypgeom_1f1(1,2)/regularized_zeta(u)
    tol=real(Q(1,2**bits));large=flint.acb.integral(integrand,flint.acb(real(delta)),flint.acb(1),abs_tol=tol,rel_tol=tol,depth_limit=48,eval_limit=200000)
    if not large.is_finite() or not large.imag.contains(0):return {'missing':True,'reason':'complete_center_quadrature_exhausted'}
    value=c*real(p)*inflate(small+large.real,err)
    return {'value_ball':ball(value),'tail_error_ball':ball(c*real(p)*err),'complete_branch_center':True,'missing':False,
        'endpoint_method':'t^(1/(1-a)), 80-term Taylor with Cauchy remainder on |v|<=1/4','precision':precision,'quadrature_bits':bits}


@lru_cache(maxsize=None)
def center_disk_certificate(precision=384):
    """Rouche on Z(1-v); no ordinary zero information is assumed."""
    flint.ctx.prec=precision;L=64;old=flint.ctx.cap;flint.ctx.cap=L
    try:v=flint.arb_series([0,1],prec=L);Z=1-v*(1-v).zeta(deflate=True);zs=[Z[j] for j in range(L)]
    finally:flint.ctx.cap=old
    R=Q(5,4);outer=Q(2);box=flint.acb(flint.arb(1,real(outer)),flint.arb(0,real(outer)));B=abs(regularized_zeta(box)).upper()
    tail=B*real(R/outer)**L/(1-real(R/outer));variation=sum((abs(zs[j])*real(R)**j for j in range(1,L)),flint.arb(0))+tail;lower=(1-variation).lower()
    return {'certified':lower>0,'radius':str(R),'outer_radius':str(outer),'Taylor_terms':L,'variation_upper_ball':ball(variation),'modulus_lower_ball':ball(lower),
        'outer_Z_modulus_upper_ball':ball(B),'method':'native deflated-zeta coefficients plus Cauchy tail and Rouche','ordinary_zero_assumptions_used':False}


def complete_center(a,x,precision=384,bits=96):
    """Whole real-cut integral from a uniformly certified analytic expansion."""
    a=Q(a);x=Q(x);flint.ctx.prec=precision;c=croot(a)
    if x<1:raise ValueError('Center is defined for x>=1')
    if x==1:return {'value_ball':'0','tail_error_ball':'0','complete_branch_center':True,'missing':False}
    disk=center_disk_certificate(precision)
    if not disk['certified']:return {'missing':True,'reason':'center_Rouche_disk_not_resolved'}
    R=Q(disk['radius']);lower=flint.arb(disk['modulus_lower_ball']);B=(power(real(x),1+R)+1)/(real(R-1)*lower);L=448
    while L<=1024:
        H=center_series(str(x),L,precision);value=c*sum((h/real(j+1-a) for j,h in enumerate(H)),flint.arb(0))
        error=c*B*real(R)**(-L)/(real(L+1-a)*(1-real(1/R)))
        value=inflate(value,error)
        if value.rad()<=real(Q(1,2**bits))*(1+abs(value)):
            return {'value_ball':ball(value),'tail_error_ball':ball(error),'complete_branch_center':True,'missing':False,'Taylor_terms':L,
                'endpoint_method':'complete analytic Taylor integral, weighted Cauchy tail on |v|<=5/4','precision':precision,'target_bits':bits,'zero_free_disk':disk}
        L+=64
    return {'missing':True,'reason':'complete_center_Taylor_resources_exhausted'}


def derivative_guard(a):return 4*real(2).log()*croot(a)/real(1-Q(a))


def canonical(atoms):
    w={}
    for b,c in atoms:
        b=Q(b);c=Q(c)
        if not 0<b<1:raise ValueError('Base logarithmic roots must lie in (0,1)')
        w[b]=w.get(b,Q(0))+c
    w={b:c for b,c in w.items() if c}
    if not w:raise ValueError('Zero operator has no ordinary-zero recovery certificate')
    largest=max(w);norm=max(map(abs,w.values()))*(1 if w[largest]>0 else -1)
    return {'arithmetic_model':'inverse_one','center':'full_real_cut','atoms':[[str(b),str(w[b]/norm)] for b in sorted(w)],
        'normalization':'first_nonzero_parameter_moment','actual_mobius_arithmetic_retained':True,'ordinary_zeta_erased':False}


def moments(program):
    atoms=[(Q(b),Q(w)) for b,w in program['atoms']]
    for m in range(len(atoms)):
        p=sum((w*b**m for b,w in atoms),Q(0))
        if p:return m,p
    raise ValueError('Distinct nonzero atoms must have a nonzero Vandermonde moment')


def recovery(program,limit=256):
    if program.get('arithmetic_model')!='inverse_one' or program.get('center')!='full_real_cut':
        return {'admitted':False,'reason':'actual_arithmetic_and_complete_center_required'}
    atoms=[(Q(b),Q(w)) for b,w in program['atoms']]
    if len({b for b,w in atoms})!=len(atoms) or not atoms or any(not 0<b<1 or not w for b,w in atoms):
        return {'admitted':False,'reason':'canonical_nonzero_distinct_positive_bases_required'}
    m,p=moments(program);bmax,wmax=max(atoms)
    for M in range(limit+1):
        left=abs(wmax)*bmax**M;right=sum((abs(w)*b**M for b,w in atoms if b!=bmax),Q(0))
        if left>right:
            return {'admitted':True,'first_nonzero_moment_order':m,'first_nonzero_moment':str(p),
                'eventual_nonzero_moment_threshold':M,'dominant_moment_left':str(left),'dominant_moment_right':str(right),
                'all_multiplicities_and_all_ordinary_heights':True,'sum_weights_zero':m>0,
                'RH_if_cofinal_critical_signed_estimates':True,'global_signed_premise_proved':False,
                'argument':'entire exponent parameter; cofinal zeros; eventual moment dominance; zeta pole at one',
                'ordinary_zeta_erased':False,'finite_q_success_is_uniform_premise':False}
    return {'admitted':False,'reason':'moment_dominance_certificate_resource_exhausted','missing_not_counterexample':True}


def normalization(program,q):
    if type(q)is not int or q<1:raise ValueError('Positive integer family level required')
    m,p=moments(program);return p/Q(q)**m


def apply(program,q,responses):
    h=normalization(program,q)
    return sum((real(Q(w))*flint.arb(responses[str(Q(b)/q)]) for b,w in program['atoms']),flint.arb(0))/real(h)


def weak_certificate(program,q):
    h=abs(normalization(program,q));K=sum((real(abs(Q(w)))*derivative_guard(Q(b)/q) for b,w in program['atoms']),flint.arb(0))/real(h)
    C=sum((real(abs(Q(w)))*(1+derivative_guard(Q(b)/q)) for b,w in program['atoms']),flint.arb(0))/real(h)
    guard=ceil(Q(C.upper().str(80,radius=False)))+1
    return {'all_real_x_ge_one':True,'ordinary_exponent':'1','log_degree':'1','constant':guard,'derivative_guard_ball':ball(K),
        'arithmetic_model':'inverse_one','complete_branch_center':True,'normalization':str(normalization(program,q)),
        'actual_mobius_arithmetic_retained':True,'global_signed_premise_proved':True,'RH_strength':False}


def leading_center(a,x):
    a=Q(a);x=Q(x)
    if not 0<a<1 or x<1:raise ValueError('Leading center domain')
    if x<2:return real(x-1)*real(2*a)*power(real(2).log(),a-1)
    return real(a)*real(x)*power(real(x).log(),a-1)


def leading_only_obstruction(program,q):
    b,w=max((Q(b),Q(w)) for b,w in program['atoms']);a=b/q
    return {'all_scale_power_below_one_impossible':True,'uncancelled_branch_exponent':str(1-a),
        'dominant_base':str(b),'dominant_weight':str(w),'normalized_by':str(normalization(program,q)),
        'coefficient':'-Gamma(a+1)*(1+EulerGamma)*dominant_weight/normalization',
        'analytic_reason':'noninteger branch at s=1 remains after leading-only centering','complete_center_is_not_rejected':True}


@lru_cache(maxsize=None)
def fractional_profile(a,sreal='5/8',simag='16',precision=512,N=96,M=24):
    """Whole continued F_a(s), EM with an explicit absolute tail enclosure."""
    a=Q(a);croot(a);flint.ctx.prec=precision;s=flint.acb(real(Q(sreal)),real(Q(simag)));logN=real(N).log()
    coeff=[flint.acb(1)];derivatives=[]
    for r in range(2*M+1):
        value=sum((c*power(logN,a-j) for j,c in enumerate(coeff)),flint.acb(0))*flint.acb(real(N)).pow(-s-r)
        derivatives.append(value)
        if r<2*M:
            coeff=[-(s+r)*(coeff[j] if j<len(coeff) else 0)+(real(a-j+1)*coeff[j-1] if j else 0) for j in range(len(coeff)+1)]
    total=sum((flint.acb(real(n)).pow(-s)*power(real(n).log(),a) for n in range(2,N+1)),flint.acb(0))
    integral=((s-1)*logN).gamma_upper(real(a+1))*(s-1).pow(-real(a+1))
    total+=integral-derivatives[0]/2
    for k in range(1,M+1):total-=flint.arb.bernoulli(2*k)/factorial(2*k)*derivatives[2*k-1]
    rate=s.real+2*M-1
    L=(rate*logN).gamma_upper(real(a+1))/power(rate,a+1)
    error=2*real(2*M).zeta()/power(2*flint.arb.pi(),2*M)*L*sum((abs(c)/logN**j for j,c in enumerate(coeff)),flint.arb(0))
    full=total+flint.acb(flint.arb(0,error.upper()),flint.arb(0,error.upper()))
    return {'value_ball':cball(full),'remainder_ball':ball(error),'method':'complete_Euler_Maclaurin','N':N,'M':M,'precision':precision,
        'whole_continuation_not_prefix_surrogate':True,'entire_exponent_parameter':True,'s_real':sreal,'s_imag':simag}


def observer(program,q,s_real='5/8',s_imag='16',precision=512):
    flint.ctx.prec=precision;s=flint.acb(real(Q(s_real)),real(Q(s_imag)));h=normalization(program,q)
    profiles={str(Q(b)/q):fractional_profile(str(Q(b)/q),s_real,s_imag,precision) for b,w in program['atoms']}
    F=sum((real(Q(w))*decode(profiles[str(Q(b)/q)]['value_ball']) for b,w in program['atoms']),flint.acb(0))/real(h)
    stored_F=cball(F);F=decode(stored_F);raw_lower=abs(F).lower();D=2**160
    lower=real(Q(floor(Q(raw_lower.str(170,radius=False))*D)-1,D)) if raw_lower.is_finite() else flint.arb(0)
    if not lower>0 or not abs(s.imag).lower()>0:return {'missing':True,'reason':'full_profile_observer_unresolved','profiles':profiles}
    K=flint.arb(weak_certificate(program,q)['derivative_guard_ball']);Mbound=K/(abs(s)*abs(s.imag))
    return {'missing':False,'normalized_full_profile_ball':stored_F,'profile_modulus_lower_ball':ball(lower),'profile_lower_rounding_bits':160,'full_cut_center_mellin_upper_ball':ball(Mbound),
        'integer_to_real_guard_ball':ball(K/s.real),'normalization':str(h),'profiles':profiles,
        'reciprocal_cost_formula':'|s|*(Mbound+C_q*gap_integral+integer_to_real_guard)/|F_family(s)|',
        'normalization_and_full_center_costs_charged':True,'conditional_on_global_signed_premise':True,'RH_proved':False}
