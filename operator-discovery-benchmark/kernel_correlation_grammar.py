"""Complete signed Gram observables and certified squarefree diagonals.

The observable and proof templates are supplied. Its unresolved obligation is
signed off-diagonal arithmetic control, not a finite numerical fit.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,ceil,log2
import flint
from mellin_kernel_grammar import (real,power,serialize,encode,poly,bank_certificate,
    global_certificate,theta,native_observer,evaluate_poly,mellin_polynomial,complex_ball)

VERSION='complete-Gram-correlations-squarefree-density-singular-metrics-cofinal-growth-v1'


def rate_terms(rows):
    out={}
    for m,r,c in rows:
        if type(m) is not int:raise ValueError('Integer moment label required')
        r,c=Q(r),Q(c)
        if m<0 or r<=0:raise ValueError('Nonnegative moment, positive rational rate required')
        out[m,r]=out.get((m,r),Q(0))+c
    return [[m,str(r),str(c)] for (m,r),c in sorted(out.items()) if c]


def kernel_product(K,L,b):
    """Pointwise multiplication creates general rational exponential rates."""
    b=Q(b);rows=[]
    for m,j,c in K['terms']:
        for h,t,d in L['terms']:
            r,s=b**j,b**t;R=r+s
            rows.append([m+h,str(R),str(Q(c)*Q(d)*r**m*s**h/R**(m+h))])
    return rate_terms(rows)


def metric(a,b,c):
    a,b,c=map(Q,(a,b,c));scale=max(abs(a),abs(b),abs(c))
    if not scale:raise ValueError('Zero observable excluded')
    a,b,c=a/scale,b/scale,c/scale;det=a*c-b*b;positive=a>=0 and c>=0 and det>=0
    rows=[];pivots=[]
    if positive:
        if a>0:
            rows.append(['1',str(b/a)]);pivots.append(str(a))
            if det>0:rows.append(['0','1']);pivots.append(str(det/a))
        elif c>0:rows.append(['0','1']);pivots.append(str(c))
    return {'entries':list(map(str,(a,b,c))),'positive_semidefinite':positive,
        'positive_definite':bool(positive and det>0),'determinant':str(det),
        'active_covectors':rows,'positive_pivots':pivots,'rank':len(rows) if positive else None,
        'identity':'F^T H F=sum d_i*(r_i dot F)^2 for positive semidefinite H',
        'indefinite_is_not_a_counterexample_to_any_growth_bound':True}


def effective_kernels(Ks,H):
    out=[];pivots=[];vectors=[]
    for row,pivot in zip(H['active_covectors'],H['positive_pivots']):
        terms={}
        for weight,K in zip(map(Q,row),Ks):
            for m,j,c in K['terms']:terms[m,j]=terms.get((m,j),Q(0))+weight*Q(c)
        terms={ij:c for ij,c in terms.items() if c}
        if not terms:continue
        out.append({'terms':encode(terms),'maximum_moment':max(m for m,j in terms),
            'maximum_dilation':max(j for m,j in terms),'semantics':Ks[0]['semantics']})
        pivots.append(pivot);vectors.append(row)
    return out,pivots,vectors


def diagonal_terms(Ks,H,b):
    a,h,c=map(Q,H['entries']);rows=[]
    for weight,K,L in [(a,Ks[0],Ks[0]),(2*h,Ks[0],Ks[1]),(c,Ks[1],Ks[1])]:
        for m,r,v in kernel_product(K,L,b):rows.append([m,r,str(weight*Q(v))])
    return rate_terms(rows)


@lru_cache(maxsize=None)
def _diagonal_atom(k,ell,m,r,precision):
    flint.ctx.prec=precision
    A=(2*k-1)/ell+m;B=(2*k-Q(1,2))/ell+m
    integral=power(real(r),Q(1-2*k)/ell)*real(A).gamma()/real(ell)
    derivative=power(real(r),(Q(1,2)-2*k)/ell)*(real(2*k+ell*m)*real(B).gamma()+real(ell)*real(B+1).gamma())/real(ell)
    return integral,derivative


def diagonal_certificate(rows,k,ell,precision=512):
    """True signed squarefree density remainder at every real scale."""
    k,ell=Q(k),Q(ell);flint.ctx.prec=precision
    if k<=1 or ell<=0:raise ValueError('Original inverse kernel requires k>1, ell>0')
    I=flint.arb(0);U=flint.arb(0);components=[]
    for m,r,c in rows:
        r,c=Q(r),Q(c)
        integral,derivative=_diagonal_atom(k,ell,m,r,precision)
        I+=real(c)*integral;U+=real(abs(c))*derivative
        components.append({'moment':m,'rate':str(r),'coefficient':str(c),
            'signed_integral_ball':serialize(real(c)*integral),
            'absolute_weighted_variation_ball':serialize(real(abs(c))*derivative)})
    density=1/flint.arb(2).zeta()
    return {'components':components,'continuous_integral_ball':serialize(I),
        'weighted_variation_ball':serialize(U),'squarefree_density_ball':serialize(density),
        'main_coefficient_ball':serialize(density*I),'signed_remainder_constant_ball':serialize(real(Q(5,2))*U),
        'theorem':'|D_H(X)-X*I_H/zeta(2)|<=(5/2)*U_H*sqrt(X), every real X>0',
        'squarefree_count_theorem':'|sum_(n<=x)mu(n)^2-x/zeta(2)|<=(5/2)*sqrt(x), every real x>0',
        'imported_prime_distribution_estimate':False,'RH_strength_for_full_response':False,
        'proof_backend':'square-divisor inversion, exact positive-real Euler series, partial summation'}


def squarefree_table(mu,k,ell,b,points,maximum_moment=4,maximum_dilation=2,min_prec=384):
    """Complete nonlinear diagonal atoms, with the infinite squarefree tail."""
    k,ell,b=map(Q,(k,ell,b));points=list(map(Q,points));N=len(mu)-1;exponent=2*k
    if k<=1 or ell<=0 or b<=1 or not points:raise ValueError('Complete positive inverse-kernel domain required')
    if mu[0]!=0 or mu[1]!=1:raise ValueError('Complete inverse prefix required')
    convol=[0]*(N+1)
    for d in range(1,N+1):
        if mu[d]:
            for n in range(d,N+1,d):convol[n]+=mu[d]
    if convol[1:]!=[1]+[0]*(N-1):raise ValueError('Invalid inverse coefficient prefix')
    rates=sorted({b**i+b**j for i in range(maximum_dilation+1) for j in range(maximum_dilation+1)})
    flint.ctx.prec=min_prec;Xmax=max(points);Rmax=max(rates)
    for L in range(12,193,4):
        error=max((power(real(Xmax),exponent)*(real(Rmax)*power(real(Xmax),ell))**(m+L)
            *power(real(N),1-exponent-ell*(m+L))/(real(exponent+ell*(m+L)-1)*factorial(L))).upper()
            for m in range(maximum_moment+1))
        if error<real(Q(1,2**90)):break
    else:raise ArithmeticError('Squarefree Taylor resource budget exhausted')
    precision=max(min_prec,ceil(float(exponent+ell*(maximum_moment+L))*log2(max(N,2)))+186)
    flint.ctx.prec=precision;sums=[flint.arb(0) for _ in range(L+maximum_moment)];weights=[]
    for n in range(1,N+1):
        if not mu[n]:continue
        w=power(real(n),-exponent);t=power(real(n),-ell);weights.append((w,t));v=w
        for j in range(len(sums)):sums[j]+=v;v*=t
    moments=[]
    for j in range(len(sums)):
        w=exponent+ell*j;value=real(w).zeta()/real(2*w).zeta()-sums[j]
        if not abs(value)<=power(real(N),1-w)/real(w-1):raise ArithmeticError('Squarefree tail moment unresolved')
        moments.append(value)
    rows={};tails=[]
    for X in points:
        Xk=power(real(X),exponent);Xe=power(real(X),ell)
        for r in rates:
            c=real(r)*Xe;values=[flint.arb(0) for _ in range(maximum_moment+1)]
            for w,t in weights:
                z=c*t;v=w*(-z).exp()
                for m in range(maximum_moment+1):values[m]+=v;v*=z
            for m,value in enumerate(values):
                tail=flint.arb(0);v=c**m
                for j in range(L):tail+=v*moments[m+j];v*=(-c)/(j+1)
                w=exponent+ell*(m+L);error=c**(m+L)*power(real(N),1-w)/(factorial(L)*real(w-1))
                rows[f'{m}:{r}:{X}']=serialize(Xk*(value+tail+flint.arb(0,error)))
                tails.append({'moment':m,'rate':str(r),'scale':str(X),'error_ball':serialize(Xk*error)})
    return {'k':str(k),'ell':str(ell),'base':str(b),'maximum_moment':maximum_moment,'rates':list(map(str,rates)),
        'cutoff':N,'precision':precision,'Taylor_terms':L,'tail_moment_balls':list(map(serialize,moments)),
        'values':rows,'tail_bounds':tails,'all_infinite_squarefree_terms_included':True,
        'arithmetic_source':'square of the actual constant-one inverse, not independent random signs',
        'all_moment_exponents_greater_than_one':True}


def observable(Ks,H,values,diagonal,rows,points):
    a,b,c=map(real,H['entries']);out={};pivots=list(map(real,H['positive_pivots']))
    for X in map(Q,points):
        f,g=(flint.arb(v[str(X)]) for v in values)
        if H['positive_semidefinite']:
            E=sum((d*(real(v[0])*f+real(v[1])*g)**2 for d,v in zip(pivots,H['active_covectors'])),flint.arb(0))
        else:E=a*f*f+2*b*f*g+c*g*g
        D=sum((real(v)*flint.arb(diagonal['values'][f'{m}:{r}:{X}']) for m,r,v in rows),flint.arb(0))
        out[str(X)]={'energy_ball':serialize(E),'diagonal_ball':serialize(D),'signed_off_diagonal_ball':serialize(E-D)}
    return out


@lru_cache(maxsize=None)
def growth(eta,margin,nu,d,q,X):
    th=real(eta)+real(margin)/power(real(q),Q(nu))
    return (2*th*real(X).log()).exp()*power((flint.arb.const_e()+real(X)).log(),Q(d))


def energy_frontier(eta,margin,nu,d):
    eta,margin,nu,d=map(Q,(eta,margin,nu,d))
    if eta<Q(1,2) or margin<=0 or nu<=0 or d<0:raise ValueError('Cofinal energy target requires eta>=1/2, positive approach parameters')
    return {'limit':str(eta),'margin':str(margin),'approach_power':str(nu),'log_power':str(d),
        'exponent':'2*(eta+margin/q^nu)','constant_quantifiers':'for every q exists finite B_q, for every integer N>=1',
        'constant_growth_in_q_restricted':False,'finite_parameter_grid_suffices':False}


def recovery(Ks,H):
    if not H['positive_semidefinite']:
        return {'kind':'indefinite_signed_observable_missing_coercive_recovery','all_height_no_common_zero':False,
            'counterexample_to_signed_bound':False}
    effective,pivots,vectors=effective_kernels(Ks,H)
    cert=bank_certificate(effective) if effective else {'kind':'zero_effective_observable','all_height_no_common_zero':False}
    return {'kind':'positive_semidefinite_effective_kernel_recovery','effective_kernels':effective,
        'positive_pivots':pivots,'active_covectors':vectors,'certificate':cert,
        'all_height_no_common_zero':cert['all_height_no_common_zero'],
        'singular_metrics_allowed':True,'counterexample_to_signed_bound':False}


def charge(program,f,rho,constants,qs,query,precision=384):
    rec=program['recovery'];sigma,t=map(Q,query);rho=Q(rho)
    if not rec['all_height_no_common_zero']:
        return {'status':'missing_coercive_all_height_recovery','best_log_cost':None,'observers':[]}
    k,ell,b=map(Q,program['parameters']);flint.ctx.prec=precision
    if not Q(1,2)<sigma<k:raise ValueError('Correlation observer requires 1/2<sigma<k')
    cert=rec['certificate'];v,z,G=native_observer(k,ell,b,sigma,t,precision)
    if cert['kind']=='exact_bivariate_Bezout':
        denominator=(G*evaluate_poly(poly(cert['target_polynomial']),v,z)).abs_lower()
        factors=[evaluate_poly(poly(A),v,z).abs_upper() for A in cert['multipliers']]
    else:
        denominator=(G*evaluate_poly(mellin_polynomial(rec['effective_kernels'][0]),v,z)).abs_lower();factors=[flint.arb(1)]
    if not denominator>0:return {'status':'unresolved_native_recovery','best_log_cost':None,'observers':[]}
    gcs=[global_certificate(K,k,ell,b,precision) for K in rec['effective_kernels']]
    dc=program['diagonal_certificate'];A=flint.arb(dc['main_coefficient_ball']);U=flint.arb(dc['signed_remainder_constant_ball'])
    if not A>0 or not U>=0:raise ArithmeticError('A nonzero positive Gram observable requires positive diagonal integral')
    positive=real(max(1+rho,Q(0)));observations=[];d=ceil(Q(f['log_power'])/2);L0=(flint.arb.const_e()+1).log()
    for q in qs:
        gap=real(sigma)-theta(f,q)
        if not gap>0:observations.append({'q':q,'status':'outside_observer_domain','gap_ball':serialize(gap)});continue
        logarithms=sum((real(Q(factorial(d),factorial(j)*factorial(d-j)))*L0**(d-j)*factorial(j)/gap**(j+1)
            for j in range(d+1)),flint.arb(0))
        diagonal=positive.sqrt()*(A.sqrt()/real(sigma-Q(1,2))+U.sqrt()/real(sigma-Q(1,4)))
        signed=real(constants[str(q)]).sqrt()*logarithms;norms=[]
        for pivot,gc in zip(rec['positive_pivots'],gcs):
            local=sum((flint.arb(term['constant_ball'])/real(Q(term['power'])-sigma) for term in gc['local_terms']),flint.arb(0))
            unit=flint.arb(gc['unit_increment_constant_ball'])/real(sigma)
            norms.append(local+unit+(diagonal+signed)/real(pivot).sqrt())
        cost=real(ell)*sum((factor*norm for factor,norm in zip(factors,norms)),flint.arb(0))/denominator
        observations.append({'q':q,'status':'conditional_signed_off_diagonal_bound_required','gap_ball':serialize(gap),
            'diagonal_density_cost_ball':serialize(diagonal),'signed_cost_ball':serialize(signed),
            'full_effective_transform_norm_balls':list(map(serialize,norms)),
            'native_gamma_ball':complex_ball(G),'denominator_lower_ball':serialize(denominator),
            'conditional_reciprocal_bound_ball':serialize(cost),'log_cost':float(cost.upper().log()),
            'uniform_signed_premise_proved':False})
    costs=[r['log_cost'] for r in observations if 'log_cost' in r]
    return {'status':'conditional' if costs else 'no_tested_q_inside_observer_domain',
        'best_log_cost':min(costs,default=None),'observers':observations,
        'metric_rank':program['metric']['rank'],'all_height_qualitative_recovery':True,
        'single_native_observer_is_not_all_height_quantitative_control':True}


def weak_attempt(program,f,rho):
    if Q(f['limit'])<1:return {'status':'signed_correlation_certificate_missing','available_point_growth_exponent':'1',
        'diagonal_signed_density_theorem_proved':True,'off_diagonal_uniform_premise_proved':False,
        'counterexample_to_candidate':False}
    k,ell,b=map(Q,program['parameters']);H=list(map(Q,program['metric']['entries']))
    bounds=[flint.arb(global_certificate(K,k,ell,b,384)['constant_ball']) for K in program['kernels']]
    W=real(abs(H[0]))*bounds[0]**2+2*real(abs(H[1]))*bounds[0]*bounds[1]+real(abs(H[2]))*bounds[1]**2
    dc=program['diagonal_certificate'];D=abs(flint.arb(dc['main_coefficient_ball']))+flint.arb(dc['signed_remainder_constant_ball'])
    B=W+real(abs(1+Q(rho)))*D
    return {'status':'unconditional_energy_exponent_two_witness','constant_ball':serialize(B),
        'diagonal_signed_density_theorem_proved':True,'RH_strength':False,
        'same_fitted_constants_proved':False,'point_growth_exponent':'1'}
