"""Signed exponential/dilation kernels, complete arithmetic tails and zero recovery.

The grammar and certificate methods are supplied. Search never proves a growth
estimate merely by fitting it. Rational powers have no denominator ceiling.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, ceil, log2
import flint

VERSION = 'complete-inverse-tails-bivariate-Mellin-kernels-free-cofinal-constants-v1'


def real(x):
    x=Q(x); return flint.arb(x.numerator)/x.denominator


def power(x,a):
    a=Q(a)
    if not a:return flint.arb(1)
    if x==0 and a>0:return flint.arb(0)
    if not x>0:raise ValueError('Positive base required for this rational power')
    return x.root(a.denominator)**a.numerator


def serialize(x):
    if not x.is_finite():raise ArithmeticError('Unresolved native enclosure')
    return str((x+flint.arb(0,real(Q(1,2**180))*(1+abs(x)))).str(55))


def complex_ball(z):return {'real':serialize(z.real),'imag':serialize(z.imag)}
def decode(z):return flint.acb(flint.arb(z['real']),flint.arb(z['imag']))


def encode(p):return [[i,j,str(c)] for (i,j),c in sorted(p.items()) if c]
def poly(rows):return {(int(i),int(j)):Q(c) for i,j,c in rows if Q(c)}


def plus(a,b):
    out=a.copy()
    for ij,c in b.items():out[ij]=out.get(ij,Q(0))+c
    return {ij:c for ij,c in out.items() if c}


def product(a,b):
    out={}
    for (i,j),c in a.items():
        for (r,h),d in b.items():out[(i+r,j+h)]=out.get((i+r,j+h),Q(0))+c*d
    return {ij:c for ij,c in out.items() if c}


def rising(m):
    out={(0,0):Q(1)}
    for j in range(m):out=product(out,{(1,0):Q(1),(0,0):Q(j)})
    return out


def canonical(terms):
    out={}
    for m,j,c in terms:
        if type(m) is not int or type(j) is not int or m<0 or j<0:
            raise ValueError('Nonnegative integer moment and dilation labels required')
        out[(m,j)]=out.get((m,j),Q(0))+Q(c)
    out={ij:c for ij,c in out.items() if c}
    if not out:raise ValueError('Zero kernel is excluded')
    # Overall scalar and common dilation are representation redundancies.
    h=min(j for m,j in out); out={(m,j-h):c for (m,j),c in out.items()}
    divisor=out[min(out)];out={ij:c/divisor for ij,c in out.items()}
    return {'terms':encode(out),'maximum_moment':max(m for m,j in out),
            'maximum_dilation':max(j for m,j in out),
            'semantics':'K(y)=sum c[m,j]*(b^j*y)^m*exp(-b^j*y), y>0'}


def mellin_polynomial(kernel):
    out={}
    for m,j,c in kernel['terms']:
        out=plus(out,{(i,h+j):Q(c)*v for (i,h),v in rising(m).items()})
    return out


def linear_solve(columns,target):
    """Exact rectangular elimination; free variables are fixed to zero."""
    keys=sorted(set(target).union(*(set(c) for c in columns)))
    rows=[[c.get(ij,Q(0)) for c in columns]+[target.get(ij,Q(0))] for ij in keys]
    pivots=[];row=0
    for k in range(len(columns)):
        pivot=next((r for r in range(row,len(rows)) if rows[r][k]),None)
        if pivot is None:continue
        rows[row],rows[pivot]=rows[pivot],rows[row];v=rows[row][k]
        rows[row]=[x/v for x in rows[row]]
        for r in range(len(rows)):
            if r!=row and rows[r][k]:
                v=rows[r][k];rows[r]=[x-v*y for x,y in zip(rows[r],rows[row])]
        pivots.append(k);row+=1
        if row==len(rows):break
    if any(not any(r[:-1]) and r[-1] for r in rows):return None
    out=[Q(0)]*len(columns)
    for r,k in enumerate(pivots):out[k]=rows[r][-1]
    return out


def bank_certificate(kernels,multiplier_degree=1,target_order=2):
    """Search rational identities sum A_i(v,z) P_i(v,z)=(v)_r z^h.

    The right side has no zero when Re(v)>0 and z!=0. An unsuccessful
    bounded certificate search says nothing about the truth of a bound.
    """
    Ps=[mellin_polynomial(k) for k in kernels]
    monomials=[(i,j) for i in range(multiplier_degree+1) for j in range(multiplier_degree+1)]
    columns=[product(P,{ij:Q(1)}) for P in Ps for ij in monomials]
    for r in range(target_order+1):
        for h in range(multiplier_degree+max(k['maximum_dilation'] for k in kernels)+1):
            target=product(rising(r),{(0,h):Q(1)})
            solution=linear_solve(columns,target)
            if solution is None:continue
            As=[{ij:solution[n*len(monomials)+j] for j,ij in enumerate(monomials)
                 if solution[n*len(monomials)+j]} for n in range(len(Ps))]
            assert sum_identity(As,Ps)==target
            return {'kind':'exact_bivariate_Bezout','multipliers':list(map(encode,As)),
                    'target_rising_order':r,'target_dilation_power':h,
                    'target_polynomial':encode(target),'numerator_polynomials':list(map(encode,Ps)),
                    'all_height_no_common_zero':True,'domain':'Re(v)>0; z!=0',
                    'infinite_height_sampling_used':False}
    if len(kernels)==1:
        # This exact dominance argument also permits equality: |z|<1.
        terms=poly(kernels[0]['terms']);ms={m for m,j in terms}
        if len(ms)==1:
            m=next(iter(ms));h=min(j for _,j in terms);c0=terms[m,h]
            if abs(c0)>=sum(abs(c) for (i,j),c in terms.items() if j!=h):
                return {'kind':'strict_unit_disk_dominance','moment':m,'dilation_power':h,
                    'constant':str(c0),'tail_absolute_sum':str(sum(abs(c) for (i,j),c in terms.items() if j!=h)),
                    'numerator_polynomials':list(map(encode,Ps)),'all_height_no_common_zero':True,
                    'domain':'Re(v)>0; z=b^(-v); b>1','infinite_height_sampling_used':False}
    return {'kind':'missing_bounded_certificate','all_height_no_common_zero':False,
            'numerator_polynomials':list(map(encode,Ps)),'counterexample_to_growth_bound':False}


def sum_identity(As,Ps):
    out={}
    for A,P in zip(As,Ps):out=plus(out,product(A,P))
    return out


def evaluate_poly(p,v,z):
    return sum((real(c)*v**i*z**j for (i,j),c in p.items()),flint.acb(0))


def frontier(eta,epsilon,nu,log_power=0):
    eta,epsilon,nu,log_power=map(Q,(eta,epsilon,nu,log_power))
    if epsilon<=0 or nu<=0 or log_power<0 or eta<0:
        raise ValueError('Nonnegative limit/log power, positive margin and approach power required')
    return {'limit':str(eta),'margin':str(epsilon),'approach_power':str(nu),'log_power':str(log_power),
            'theta_expression':'eta+epsilon/q^nu','parameter_domain':'every integer q>=2',
            'constant_quantifiers':'for every q there exists finite C_q, for every integer N>=1',
            'constant_growth_in_q_restricted':False,'finite_parameter_grid_suffices':False,
            'RH_sufficient_if_uniform_and_bank_recovers':bool(eta<=Q(1,2)),
            'uniform_signed_premise_proved':False}


def theta(f,q):
    if type(q) is not int or q<2:raise ValueError('Integer q>=2 required')
    return real(f['limit'])+real(f['margin'])/power(real(q),Q(f['approach_power']))


def envelope(f,q,X):
    X=real(X)
    return (theta(f,q)*X.log()).exp()*power((flint.arb.const_e()+X).log(),Q(f['log_power']))


def choose_resources(k,ell,b,maximum_moment,maximum_dilation,N,Xmax,min_prec=384,target_bits=90):
    k,ell,b,Xmax=map(Q,(k,ell,b,Xmax))
    if k<=1 or ell<=0 or b<=1 or type(N) is not int or N<1 or Xmax<=0:
        raise ValueError('k>1, ell>0, b>1, complete positive cutoff/scale required')
    flint.ctx.prec=min_prec;r=b**maximum_dilation
    for L in range(12,193,4):
        w=k+ell*(maximum_moment+L)
        R=max((power(real(Xmax),k)*(real(r)*power(real(Xmax),ell))**(m+L)
               *power(real(N),1-k-ell*(m+L))/(real(k+ell*(m+L)-1)*factorial(L))).upper()
              for m in range(maximum_moment+1))
        if R<real(Q(1,2**target_bits)):break
    else:raise ArithmeticError('Tail Taylor resource budget exhausted')
    precision=max(min_prec,ceil(float(w)*log2(max(N,2)))+target_bits+96)
    return {'cutoff':N,'tail_Taylor_terms':L,'precision':precision,'target_absolute_bits':target_bits,
            'largest_tail_error_bound_ball':serialize(R),'maximum_scale':str(Xmax)}


def primitive_table(mu,k,ell,b,points,maximum_moment=2,maximum_dilation=2,min_prec=384):
    """Prefix plus exact real reciprocal-zeta moments plus rigorous Taylor tail."""
    k,ell,b=map(Q,(k,ell,b));points=list(map(Q,points));N=len(mu)-1
    if mu[0]!=0 or mu[1]!=1:raise ValueError('Constant-one inverse required')
    check=[0]*(N+1)
    for d in range(1,N+1):
        if mu[d]:
            for n in range(d,N+1,d):check[n]+=mu[d]
    if check[1:]!=[1]+[0]*(N-1):raise ValueError('The prefix is not the complete Dirichlet inverse')
    resource=choose_resources(k,ell,b,maximum_moment,maximum_dilation,N,max(points),min_prec)
    flint.ctx.prec=resource['precision'];L=resource['tail_Taylor_terms']
    weights=[];prefix=[flint.arb(0) for _ in range(L+maximum_moment)]
    for n in range(1,N+1):
        if not mu[n]:continue
        w=real(mu[n])*power(real(n),-k);t=power(real(n),-ell);weights.append((w,t))
        z=w
        for j in range(len(prefix)):prefix[j]+=z;z*=t
    moments=[]
    for j in range(len(prefix)):
        value=1/real(k+ell*j).zeta()-prefix[j]
        # A simple independently meaningful bound on each arithmetic tail.
        upper=power(real(N),1-k-ell*j)/real(k+ell*j-1)
        if not abs(value)<=upper:raise ArithmeticError('Real reciprocal-zeta tail unresolved')
        moments.append(value)
    rows={};tail_rows=[]
    for X in points:
        Xe=power(real(X),ell);Xk=power(real(X),k)
        values={(m,j):flint.arb(0) for m in range(maximum_moment+1) for j in range(maximum_dilation+1)}
        for w,t in weights:
            for j in range(maximum_dilation+1):
                y=real(b**j)*Xe*t;v=w*(-y).exp()
                for m in range(maximum_moment+1):values[m,j]+=v;v*=y
        for (m,j),value in values.items():
            c=real(b**j)*Xe;tail=flint.arb(0);v=c**m
            for t in range(L):tail+=v*moments[m+t];v*=(-c)/(t+1)
            w=k+ell*(m+L)
            error=c**(m+L)*power(real(N),1-w)/(factorial(L)*real(w-1))
            total=Xk*(value+tail+flint.arb(0,error))
            rows[f'{m}:{j}:{X}']=serialize(total)
            tail_rows.append({'moment':m,'dilation':j,'scale':str(X),'error_bound_ball':serialize(Xk*error)})
    return {'k':str(k),'ell':str(ell),'base':str(b),'resources':resource,'values':rows,
            'reciprocal_zeta_tail_moments':list(map(serialize,moments)),
            'tail_certificates':tail_rows,'coefficient_prefix_complete':True,
            'infinite_tail_included':True,'tail_identity_domain':'all moment exponents >1',
            'new_prime_distribution_bound_imported':False}


def response(kernel,table,points):
    out={}
    for X in map(Q,points):
        value=sum((real(c)*flint.arb(table['values'][f'{m}:{j}:{X}']) for m,j,c in kernel['terms']),flint.arb(0))
        out[str(X)]=serialize(value)
    return out


@lru_cache(maxsize=None)
def atom_global_bound(k,ell,r,m,precision):
    """Unimodal integral+2*peak bound, valid at every real X>=1."""
    if flint.ctx.prec!=precision:raise ValueError('Precision must match cache key')
    k,ell,r=map(Q,(k,ell,r));a=k+ell*m
    # Integral over t>0 and at most twice the peak control the discrete sum.
    I=power(real(r),Q(1-k)/ell)*real(Q(k-1,ell)+m).gamma()/real(ell)
    peak=power(real(r),-k/ell)*power(real(a/ell),a/ell)*(-real(a/ell)).exp()
    return I+2*peak


def global_certificate(kernel,k,ell,b,precision):
    k,ell,b=map(Q,(k,ell,b));flint.ctx.prec=precision
    W=flint.arb(0);J=flint.arb(0);local=[]
    for m,j,c in kernel['terms']:
        r=b**j;v=atom_global_bound(k,ell,r,m,precision);u=atom_global_bound(k,ell,r,m+1,precision)
        W+=real(abs(Q(c)))*v;J+=real(abs(Q(c)))*(real(k+ell*m)*v+real(ell)*u)
        local.append({'power':str(k+ell*m),'constant_ball':serialize(real(abs(Q(c)))*real(r**m)*real(k+ell*m).zeta())})
    return {'all_real_scale_bound':'|F_K(X)|<=W*X for every real X>=1',
            'constant_ball':serialize(W),'unit_increment_bound':'|F_K(N+t)-F_K(N)|<=J*t, 0<=t<=1',
            'unit_increment_constant_ball':serialize(J),'local_terms':local,
            'RH_strength':False,'signed_arithmetic_control_used':False,
            'proof_backend':'unimodal positive envelope and its full integral; no prime distribution premise'}


@lru_cache(maxsize=None)
def native_observer(k,ell,b,sigma,t,precision):
    if flint.ctx.prec!=precision:raise ValueError('Native observer precision mismatch')
    v=(real(k)-flint.acb(real(sigma),real(t)))/real(ell)
    return v,(-v*real(b).log()).exp(),v.gamma()


def charged_cost(kernels,cert,k,ell,b,f,constants,qs,global_certs,query):
    sigma,t=map(Q,query);k,ell,b=map(Q,(k,ell,b))
    if not 0<sigma<k:raise ValueError('This observer requires 0<sigma<k')
    if not cert['all_height_no_common_zero']:
        return {'status':'missing_all_height_recovery_certificate','best_log_cost':None,'observers':[]}
    v,z,Gamma=native_observer(k,ell,b,sigma,t,flint.ctx.prec);Ps=[mellin_polynomial(K) for K in kernels]
    norms=[]
    for K,gc in zip(kernels,global_certs):
        local=sum((flint.arb(a['constant_ball'])/real(Q(a['power'])-sigma) for a in gc['local_terms']),flint.arb(0))
        norms.append((local,flint.arb(gc['unit_increment_constant_ball'])/real(sigma)))
    factors=[]
    if cert['kind']=='exact_bivariate_Bezout':
        R=evaluate_poly(poly(cert['target_polynomial']),v,z)
        denominator=(Gamma*R).abs_lower()
        factors=[evaluate_poly(poly(A),v,z).abs_upper() for A in cert['multipliers']]
    else:
        denominator=(Gamma*evaluate_poly(Ps[0],v,z)).abs_lower();factors=[flint.arb(1)]
    if not denominator>0:return {'status':'unresolved_native_denominator','best_log_cost':None,'observers':[]}
    observers=[]
    for q in qs:
        gap=real(sigma)-theta(f,q)
        if not gap>0:
            observers.append({'q':q,'status':'outside_this_observers_convergence_domain','gap_ball':serialize(gap)});continue
        d=ceil(Q(f['log_power']));L0=(flint.arb.const_e()+1).log()
        # log(e+X)<=log(e+1)+log(X); integer moment majorant.
        logmoment=sum((real(factorial(d)//(factorial(j)*factorial(d-j)))*L0**(d-j)*factorial(j)/gap**(j+1)
                       for j in range(d+1)),flint.arb(0))
        Bs=[local+unit+real(constants[i][str(q)])*logmoment for i,(local,unit) in enumerate(norms)]
        cost=real(ell)*sum((factor*B for factor,B in zip(factors,Bs)),flint.arb(0))/denominator
        observers.append({'q':q,'status':'conditional_global_signed_bound_required',
                          'gap_ball':serialize(gap),'Mellin_log_moment_ball':serialize(logmoment),
                          'complete_transform_norm_balls':list(map(serialize,Bs)),
                          'native_gamma_ball':complex_ball(Gamma),'native_denominator_lower_ball':serialize(denominator),
                          'conditional_reciprocal_zeta_bound_ball':serialize(cost),
                          'log_cost':float(cost.upper().log()),'uniform_premise_verified':False})
    valid=[o for o in observers if o.get('log_cost') is not None]
    return {'status':'conditional' if valid else 'no_tested_q_inside_this_observers_domain',
            'best_log_cost':min((o['log_cost'] for o in valid),default=None),'observers':observers,
            'all_height_qualitative_recovery':True,'native_query':list(map(str,query)),
            'finite_query_is_not_an_all_height_quantitative_bound':True}


def certificate_attempt(f,kernels,gcs):
    eta=Q(f['limit'])
    if eta>=1:
        return {'status':'unconditional_weak_frontier_proved','limiting_exponent':str(eta),
                'constant_witnesses':[g['constant_ball'] for g in gcs],
                'RH_strength':False,'same_numerical_fitted_constants_proved':False}
    return {'status':'missing_uniform_signed_cancellation_certificate','limiting_exponent':str(eta),
            'available_proved_growth_exponent':'1','remaining_gap':str(1-eta),
            'obstruction_to_this_backend':'the absolute envelope divided by X^theta_q diverges whenever theta_q<1',
            'counterexample_to_candidate':False,'RH_strength_uniform_estimate_proved':False}
