"""Generated signed prime/composite transports with paid whole-window error.

Each failed window is kept unchanged. The transformed full core remains an
open RH-strength target; the proved correction is not its missing bound.
"""
from collections import Counter
from fractions import Fraction as Q
import math
import numpy as np
from flint import arb
from scipy.special import exp1

THETAS=('1/2','7/12','2/3','3/4','5/6','1')


def validate(program):
    if set(program)!={'cofactor','theta','capacity_fraction','load_multiple','keep_failed_windows'}:
        raise ValueError('complete transport AST')
    if type(program['cofactor']) is not int or not 2<=program['cofactor']<=16:raise ValueError('cofactor2..16')
    if type(program['theta']) is not str or str(Q(program['theta']))!=program['theta'] or not 0<Q(program['theta'])<=1:
        raise ValueError('canonical rational window exponent')
    if program['capacity_fraction']!='1/2' or type(program['load_multiple']) is not int or program['load_multiple']!=4 or program['keep_failed_windows'] is not True:
        raise ValueError('complete window fallback and fixed capacity budget')


def factors(n):
    out=[];p=2
    while p*p<=n:
        e=0
        while n%p==0:n//=p;e+=1
        if e:out.append((p,e))
        p+=1
    if n>1:out.append((n,1))
    return out


def theory(program):
    validate(program);theta=Q(program['theta']);m=program['cofactor'];f=factors(m)
    omega_one=sum(e==1 for p,e in f);positive=bool(omega_one%2)
    exponent=2*theta-Q(5,3)
    return dict(rule='exact_capacity_checked_whole_window_transport',program=program,
        source_prime_identity='f(p)=-R_u*p^(-1/3)+(beta+R_u)*p^(-2/3)',
        source_premise='complete original source AST; beta9/2 and0<R_u<5',
        window='A=2^k,L=2^floor(theta*k); all integer windows[A+jL,A+(j+1)L) inside[A,2A)',
        fallback='if ANY source sign, destination sign, capacity or count test fails, retain the ENTIRE original window',
        correction='D(x)=F(x)-G(x); completed windows have exactly zero ordinary mass',
        prefix_error_bound='|D(n)|<=5*L*A^(-1/3) for every integer n in the annulus[A,2A)',
        energy_error_constant='25',energy_error_power=str(exponent),
        energy_error_bound='E_D(X)<=25*X^energy_error_power at EVERY dyadic X>=1',
        full_energy_recovery=['E_F(X)<=2E_G(X)+50X^energy_error_power','E_G(X)<=2E_F(X)+50X^energy_error_power'],
        cofinal_recovery=exponent<=0,coefficient_absolute_domination='|g(n)|<=|f(n)|, with the full unit and all failed windows retained',
        bank_error_identity='B_D(x)=log(x)*D(x)-integral_1^x D(t)/t dt',
        bank_error_bound='|B_D(x)|<=5*x^alpha*(log x+1/alpha), alpha=theta-1/3>0' if theta>Q(1,3) else None,
        completed_window_log_moments_retained=True,new_log_bank='direct sum g(n)*log n; original Euler log generator does NOT apply',
        cofactor_factorization=f,number_of_valuation_one_primes=omega_one,cofactor_leading_capacity_positive=positive,
        cofactor_sign_rule='A0(m)=beta*nu0(m)*[-2+nu1(m)/nu0(m)+mu(m)/nu0(m)]; bracket strictlynegative andsign(nu0)=(-1)^omega_one',
        eventual_prime_removal_proved=positive and Q(17,30)<theta<Q(99,100),
        prime_count_import=dict(title='Guth and Maynard, New large value estimates for Dirichlet polynomials',
            url='https://arxiv.org/pdf/2405.20552',theorem='Corollary1.3',threshold='17/30',strict_threshold=True,
            role='eventual nonempty windows, bounded reuse and positive capacity; NOT needed for the unconditional error bound'),
        unchanged_fresh_semiprimes='both prime factors>16 imply g(pq)=f(pq); their prior positive-sector obstruction persists',
        critical_pole_preservation=theta<Q(5,6),
        whole_transformed_core_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False)


def catalogue(meter):
    rows=[]
    for m in range(2,17):
        for theta in THETAS:
            p=dict(cofactor=m,theta=theta,capacity_fraction='1/2',load_multiple=4,keep_failed_windows=True)
            cert=theory(p)
            rows.append(dict(id=len(rows),program=p,certificate=cert,
                admitted=cert['cofinal_recovery'] and cert['eventual_prime_removal_proved'],
                status='unpaid_recovery_power' if not cert['cofinal_recovery'] else
                    'eventual_capacity_sign_fails' if not cert['cofactor_leading_capacity_positive'] else
                    'prime_count_import_does_not_cover_exponent' if not cert['eventual_prime_removal_proved'] else 'recoverable_new_core_open'))
            meter.charge(200)
    return rows


def sieve(H,meter):
    flags=bytearray(b'\1')*(H+1);flags[0:2]=b'\0\0'
    for p in range(2,math.isqrt(H)+1):
        if flags[p]:
            count=(H-p*p)//p+1;flags[p*p:H+1:p]=b'\0'*count;meter.charge(count)
    meter.charge(H)
    return [n for n in range(2,H+1) if flags[n]]


def transform(coefficients,program,meter):
    validate(program);H=len(coefficients)-1
    if H<1 or (H+1)&H or not coefficients[0].is_zero():raise ValueError('complete2^J coefficient array with zero dummy')
    if any(not isinstance(v,arb) or not v.is_finite() for v in coefficients):raise ValueError('finite Arb source')
    theta=Q(program['theta']);m=program['cofactor'];primes=sieve(H,meter)
    prime_windows={};dest_windows={};spec=[]
    for k in range((H+1).bit_length()-1):
        A=1<<k;L=1<<(theta.numerator*k//theta.denominator)
        for lo in range(A,2*A,L):spec.append((A,L,lo,lo+L));prime_windows[lo]=[];dest_windows[lo]=[]
    def window(n):
        k=n.bit_length()-1;A=1<<k;L=1<<(theta.numerator*k//theta.denominator)
        return A+(n-A)//L*L
    for p in primes:
        prime_windows[window(p)].append(p)
        if p>m and m*p<=H:dest_windows[window(m*p)].append(m*p)
        meter.charge(30)
    g=list(coefficients);windows=[];assignments=[]
    for A,L,lo,stop in spec:
        src=prime_windows[lo];dest=dest_windows[lo];reason=None;load=0;local=[]
        if not src:reason='empty'
        elif any(not coefficients[p]<0 for p in src):reason='source_sign'
        elif not dest:reason='no_destinations'
        elif any(not coefficients[t]>0 for t in dest):reason='destination_sign'
        else:
            load=(len(src)+len(dest)-1)//len(dest)
            if load>4*m:reason='congestion'
            else:
                demands={t:arb(0) for t in dest}
                for i,p in enumerate(src):
                    t=dest[i%len(dest)];a=-coefficients[p];demands[t]+=a;local.append([p,t,a]);meter.charge(10)
                if any(not demands[t]<=coefficients[t]/2 for t in dest):reason='capacity'
                else:
                    for p,t,a in local:g[p]=arb(0)
                    for t,a in demands.items():g[t]=coefficients[t]-a
                    assignments.extend(local)
        accepted=reason is None
        windows.append(dict(annulus=A,start=lo,stop=stop,length=L,sources=src,destinations=dest,max_load=load,
            status='accepted' if accepted else 'empty' if reason=='empty' else 'kept',reason=reason,
            assignments=local if accepted else []))
        meter.charge(40+8*(len(src)+len(dest)))
    meter.live(8*(H+1)+8*len(assignments)+10*len(windows))
    return dict(H=H,program=program,g=g,windows=windows,assignments=assignments,
                status_counts=dict(Counter(w['reason'] or 'accepted' for w in windows)),whole_signed_bound_proved=False,RH_proved=False)


def float_scores(state,source,scales,meter):
    H=state['H'];f=np.asarray([float(v) for v in source]);g=np.asarray([float(v) for v in state['g']])
    F=f.cumsum();G=g.cumsum();logs=np.zeros(H+1);logs[1:]=np.log(np.arange(1,H+1))
    Bg=(g*logs).cumsum();D=F-G
    result=[]
    for X in scales:
        if type(X) is not int or X<1 or X&(X-1) or 2*X-1>H:raise ValueError('complete dyadic block')
        if 2*X-1>H:raise ValueError('complete block')
        n=np.arange(X,2*X);ell=np.zeros(len(n));nonunit=n>1
        ell[nonunit]=exp1(np.log(n[nonunit]))-exp1(np.log(n[nonunit]+1))
        primes=[p for w in state['windows'] if w['annulus']==X for p in w['sources']]
        moved=[p for w in state['windows'] if w['annulus']==X and w['status']=='accepted' for p in w['sources']]
        result.append(dict(X=X,energy_transformed=float(np.sum(G[n]**2)/X**2),energy_original=float(np.sum(F[n]**2)/X**2),
            energy_error=float(np.sum(D[n]**2)/X**2),prime_log_work=float(np.sum(G[n]*Bg[n]*ell)),
            prime_count=len(primes),transported_primes=len(moved),coverage=len(moved)/len(primes) if primes else 1.))
    meter.charge(40*H)
    return result


def exact_scores(state,source,scales,meter):
    H=state['H'];F=[arb(0)]*(H+1);G=[arb(0)]*(H+1);Bg=[arb(0)]*(H+1);D=[arb(0)]*(H+1);B=[arb(0)]*(H+1)
    for n in range(1,H+1):
        logn=arb(n).log();F[n]=F[n-1]+source[n];G[n]=G[n-1]+state['g'][n]
        B[n]=B[n-1]+source[n]*logn;Bg[n]=Bg[n-1]+state['g'][n]*logn;D[n]=F[n]-G[n];meter.charge(100)
    blocks=[]
    for X in scales:
        if type(X) is not int or X<1 or X&(X-1) or 2*X-1>H:raise ValueError('complete dyadic block')
        energy=sum((v*v for v in G[X:2*X]),arb(0))/X**2
        error=sum((v*v for v in D[X:2*X]),arb(0))/X**2
        original=sum((v*v for v in F[X:2*X]),arb(0))/X**2
        work=arb(0)
        for n in range(max(2,X),2*X):
            ell=arb(n).log().expint(1)-arb(n+1).log().expint(1)
            work+=G[n]*Bg[n]*ell;meter.charge(600)
        blocks.append(dict(X=X,energy_transformed=energy,energy_error=error,energy_original=original,prime_log_work=work))
    state.update(F=F,G=G,B=B,Bg=Bg,D=D,B_D=[b-c for b,c in zip(B,Bg)],blocks=blocks)
    meter.live(12*(H+1)+8*len(state['assignments'])+10*len(state['windows']))
    return state


def obligation(row):
    return dict(schema='recoverable-transported-core-bound-v1',program_id=row['id'],program=row['program'],
        global_source='g=T_program(f), defined on complete dyadic windows with exact capacity and whole-window fallback',
        required='E_G(X)<=C_epsilon X^epsilon for everyepsilon>0 and EVERYdyadicX>=1; a fixed-polylog bound is a stronger sufficient target',
        signed_work_route='W_g(2X)<=rho W_g(X)+C(1+log2X)^k uniformly, followed by generic signed-work/Volterra recovery',
        direct_log_bank='B_g(x)=sum_(n<=x)g(n)logn; completed-window log mismatch is retained',
        paid_recovery=row['certificate'],original_target_preserved=True,
        inherited_square_lift_head='all coefficient-majorant-only head certificates transfer because|g|<=|f|; their full signed remainders remain open',
        inherited_euler_log_identity=False,full_transformed_core_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False)
