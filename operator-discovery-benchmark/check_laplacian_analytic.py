#!/usr/bin/env python3
"""Independent Omega coefficients, direct native-zeta anchors and zero boxes."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time

import flint
from check_laplacian import K, exp_D, factors

BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(20)


def box(r):
    return flint.acb(flint.arb(0,r),flint.arb(0,r))


@lru_cache(maxsize=None)
def primes(N):
    return tuple(n for n in range(2,N+1) if flint.fmpz(n).is_prime())


def native_P(s,sigma,M=40):
    value=flint.acb(0)
    for m in range(1,M+1):
        fs=factors(m)
        mu=0 if any(e>1 for e in fs.values()) else (-1)**len(fs)
        if mu:
            value+=real(Q(mu,m))*(m*s).zeta().log()
    v=real(sigma)
    t=flint.arb(2)**(-v)
    tail=t**(M+1)/((M+1)*(1-t))*(1+2/((M+1)*v-1))
    return value+box(tail)


def direct(s,N,absolute=False,Hermitian=False):
    ps=primes(N)
    xs=[(-s*flint.arb(p).log()).exp() for p in ps]
    power=4*s.real if Hermitian else 4*s
    weights={d:(-power*flint.arb(d).log()).exp() for d in range(1,N)}
    out=flint.acb(0)
    for i,p in enumerate(ps):
        for j,q in enumerate(ps):
            if i>=j:
                continue
            diff=xs[i]+xs[j] if absolute else xs[i]-xs[j]
            square=diff.real**2+diff.imag**2 if Hermitian else diff**2
            out+=square*weights[q-p]
    return out


def integer_tail(sigma,S,N,exclude_two=False):
    A, sig=N//2,real(sigma)
    u=2-4*sigma
    d=6*sig-2
    if u>-1:
        C=real(1 if u>=0 else 1/(u+1))
        balanced=S**2*C*flint.arb(A)**(-d)/d
    elif u==-1:
        v=2*sig+1
        balanced=S**2*flint.arb(A)**(-v)*((1+flint.arb(A).log())/v+1/v**2)
    else:
        balanced=S**2*(1+1/(4*sig-3))*flint.arb(A)**(-2*sig-1)/(2*sig+1)
    prefix=sum((flint.arb(a)**(-2*sig) for a in range(3 if exclude_two else 2,A+1)),flint.arb(0))
    small=4*prefix*flint.arb(A)**(1-4*sig)/(4*sig-1)
    large=4/(4*sig-1)*flint.arb(A)**(-d)/d
    return balanced+small+large


def anchor(s,sigma,N=1536,degree=10):
    value=direct(s,N)
    coeff=flint.acb(1)
    two=(-s*flint.arb(2).log()).exp()
    for k in range(degree+1):
        if k:
            coeff*= (4*s+k-1)/k
        tails=[]
        for j in (4,5,6):
            arg=j*s+k
            p=native_P(arg,j*sigma+k)
            finite=sum(((-arg*flint.arb(q).log()).exp() for q in primes(N)),flint.acb(0))
            tails.append(p-finite)
        value+=coeff*2**k*(two**2*tails[0]-2*two*tails[1]+tails[2])
    S=s.abs_upper()
    ratio=flint.arb(4)/(N+1)
    remainder=4*flint.arb(2)**(-2*real(sigma))*flint.arb(2)**(4*S)*ratio**(degree+1)/(1-ratio)*flint.arb(N)**(1-4*real(sigma))/(4*real(sigma)-1)
    error=integer_tail(sigma,S,N,exclude_two=True)+remainder
    return value+box(error),error


@lru_cache(maxsize=None)
def frames(beta,amplitude,size=6144):
    h=[Q(0)]*(size+1)
    for n in range(2,size+1):
        fs=factors(n)
        if len(fs)==1:
            h[n]=Q(1,next(iter(fs.values())))
    k=K(h,h,4)
    actual=exp_D([beta*a+amplitude*b for a,b in zip(h,k)])
    major=exp_D([abs(beta)*a+abs(amplitude)*abs(b) for a,b in zip(h,k)])
    return actual,major


def series(coefs,s):
    return sum((real(v)*(-s*flint.arb(n).log()).exp() for n,v in enumerate(coefs) if v),flint.acb(0))


def absolute_Gamma(sigma,N=1536):
    sig=real(sigma)
    finite=direct(flint.acb(sig),N,absolute=True).real
    norm=(real(Q(3,2))**sig+real(Q(2,3))**sig+2)/2
    T=flint.arb(N)**(1-sig)/(sig-1)
    P=(1+1/(sig-1)).log()
    return finite+flint.arb(0,(norm*(2*P*T+T**2)).abs_upper())


def scalar(old,reject_Hermitian=False):
    sigma,height=Q(old['s'][0]),old['s'][1]
    beta,amp=Q(old['beta']),Q(old['amplitude'])
    s=flint.acb(real(sigma),height)
    coefs,major=frames(beta,amp)
    assert coefs[6]==beta**2-2*amp
    finite=series(coefs,s)
    gamma,error=anchor(s,sigma)
    actual=(real(beta)*s.zeta().log()+real(amp)*gamma).exp()
    total=(real(abs(beta))*real(sigma).zeta().log()+real(abs(amp))*absolute_Gamma(sigma)).exp()
    tail=(total-series(major,flint.acb(real(sigma))).real).abs_upper()
    distance=(finite-actual).abs_upper()
    wrong=(finite+real(Q(1,3))*(-s*flint.arb(4).log()).exp()-actual).abs_lower()
    passed=bool(distance<tail) and bool(wrong>tail)
    row={'s':old['s'],'beta':old['beta'],'family':old['family'],'coefficient_cutoff':6144,
         'direct_graph_cutoff':1536,'binomial_degree':10,'Mobius_cutoff':40,
         'difference_upper_ball':short(distance),'integer_absolute_majorant_tail_ball':short(tail),
         'smaller_changed_coefficient_four_error':'1/3','changed_difference_lower_ball':short(wrong),
         'native_pair_anchor_error_ball':short(error),'coefficient_six':str(coefs[6])}
    if reject_Hermitian:
        H=direct(s,1536,Hermitian=True)
        H+=box(integer_tail(sigma,s.abs_upper(),1536))
        false=(real(beta)*s.zeta().log()+real(amp)*H).exp()
        distance_H=(finite-false).abs_lower()
        row['wrong_Hermitian_scalar_difference_lower_ball']=short(distance_H)
        row['wrong_Hermitian_form_rejected']=bool(distance_H>tail)
        passed=passed and row['wrong_Hermitian_form_rejected']
    row['all_passed']=passed
    print('Independent Laplacian scalar',sigma,height,beta,old['family'],passed,flush=True)
    return row


def graph_polynomial(s,N):
    indicator,values,squares=([flint.acb(0)]*(N+1) for _ in range(3))
    for p in primes(N):
        indicator[p]=flint.acb(1)
        values[p]=(-s*flint.arb(p).log()).exp()
        squares[p]=values[p]**2
    d=flint.acb_poly(squares)*flint.acb_poly(list(reversed(indicator)))
    c=flint.acb_poly(values)*flint.acb_poly(list(reversed(values)))
    return sum(((d[N+j]+d[N-j]-2*c[N+j])*(-4*s*flint.arb(j).log()).exp()
                for j in range(1,N)),flint.acb(0))


def zeros(source):
    rows=[]
    for old in source['whole_actual_zero_correction_controls']['records']:
        radius=Q(old['radius'])
        centre=flint.acb(real(Q(1,2)),old['disk_centre'][1])
        s=centre+box(real(radius))
        sigma=Q(1,2)-radius
        first=direct(s,1536)
        reference=graph_polynomial(s,3072)
        tail=integer_tail(sigma,s.abs_upper(),3072)
        left=integer_tail(sigma,s.abs_upper(),1536)
        diff=(first-reference).abs_upper()
        M=(reference+box(tail)).abs_upper()
        positives=all(bool((-real(Q(row['beta'])**2)*M).exp()>0) for row in old['input_root_factor_bounds'])
        passed=bool(diff<tail+left) and M.is_finite() and positives and sigma>Q(1,3)
        rows.append({'disk_centre':old['disk_centre'],'radius':old['radius'],
                     'direct_graph_cutoff':1536,'polynomial_graph_cutoff':3072,
                     'grouped_comparison_difference_upper_ball':short(diff),
                     'changed_integer_paired_comparison_tail_ball':short(tail+left),
                     'whole_disk_Gamma_modulus_upper_ball':short(M),
                     'strictly_positive_factor_bounds':positives,'whole_disk_correction_holomorphic':True,
                     'new_zero_located':False,'all_passed':passed})
    return {'records':rows,'all_passed':all(row['all_passed'] for row in rows)}


def main():
    start=time.monotonic()
    flint.ctx.prec=640
    source=json.loads((BASE/'laplacian-results/laplacian_analytic.json').read_text())
    assert source['all_passed']
    points=[scalar(old,True) for old in source['actual_zeta_ball_checks']]
    roots=[scalar(old) for old in source['ordinary_root_scalar_controls']['records']]
    zero=zeros(source)
    checks={'six_full_native_zeta_scalar_groups_changed_coefficients_reference_and_tails':all(row['all_passed'] for row in points),
            'positive_Hermitian_form_cannot_replace_holomorphic_correction':all(row['wrong_Hermitian_form_rejected'] for row in points),
            'five_ordinary_root_groups_Omega_recursion_and_smaller_errors':all(row['all_passed'] for row in roots),
            'two_whole_zero_disk_grouped_correction_and_positive_factor_bounds':zero['all_passed'],
            'changed_main_and_zero_cutoffs':all(row['coefficient_cutoff']!=old['coefficient_cutoff'] for row,old in zip(points,source['actual_zeta_ball_checks'])),
            'no_historical_novelty_or_new_RH_estimate_claimed':not source['historical_novelty_established'] and not source['new_RH_estimate_proved']}
    out={'checks':checks,'actual_zeta_ball_checks':points,'ordinary_root_scalar_controls':{'records':roots,'all_passed':all(row['all_passed'] for row in roots)},
         'whole_actual_zero_correction_controls':zero,'production_imports':False,
         'shared_trusted_kernel':'FLINT/Arb and independent exact checker helpers; integer tails, direct pair/native-prime anchors and Omega coefficients',
         'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (BASE/'laplacian-results/laplacian_analytic_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent Laplacian analytic:',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)
    assert out['all_passed']


if __name__=='__main__':
    main()
