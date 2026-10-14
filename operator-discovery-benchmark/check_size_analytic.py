#!/usr/bin/env python3
"""Independent size-product analytic audit with ordinary Fourier tails.

No production helper is imported. A Dirichlet/Abel remainder replaces
the Fejer bound, a fresh coefficient cutoff is used, and the resonance
factor is evaluated by exact rising factorials plus a geometric tail
instead of a native hypergeometric function. The actual zero is counted
with a Cauchy remainder. FLINT/Arb is the shared trusted kernel.
"""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json

import flint


BASE=Path(__file__).resolve().parent


def real(q):
    q=Q(q)
    return flint.arb(q.numerator)/q.denominator


def error_box(r):return flint.acb(flint.arb(0,r),flint.arb(0,r))


@lru_cache(maxsize=None)
def factor(n):
    p,exponents=2,{}
    while p*p<=n:
        while n%p==0:
            n//=p
            exponents[p]=exponents.get(p,0)+1
        p+=1
    if n>1:exponents[n]=1
    return exponents


def h(n,b):
    value=0
    while n>=b:n//=b;value+=1
    return value


def d_beta(n,beta):
    value=Q(1)
    for exponent in factor(n).values():
        for j in range(exponent):value*=beta+j;value/=j+1
    return value


def resonance_coefficients(beta,b,degree):
    # Produce the whole coefficient list using its independent rational
    # ratio, avoiding factorization of b^k and native hypergeometric calls.
    values=[Q(1)]
    for k in range(degree):
        ratio=Q(1)
        for exponent in factor(b).values():
            for j in range(exponent):ratio*=Q(beta+exponent*k+j,exponent*k+j+1)
        values.append(values[-1]*ratio)
    return values


def resonance(s,beta,b,degree=48):
    x=(-s*flint.arb(b).log()).exp()
    coefficients=resonance_coefficients(beta,b,degree)
    value=flint.acb(0)
    for coefficient in reversed(coefficients):value=value*x+real(coefficient)
    tail=x.abs_upper()**(degree+1)/(1-x.abs_upper())
    return value+error_box(tail)


def power(z,beta,sigma):
    assert bool(real(sigma).zeta().log()<flint.arb.pi())
    return (real(beta)*z.zeta().log()).exp()


def ordinary_fourier_reference(s,sigma,beta,b,degree=384):
    f=power(s,beta,sigma)
    r,r2=resonance(s,beta,b),resonance(s,2*beta,b)
    tau=2*flint.arb.pi()/flint.arb(b).log()
    one,two=flint.acb(0),flint.acb(0)
    for m in range(1,degree+1):
        plus=power(s-flint.acb(0,m*tau),beta,sigma)
        minus=power(s+flint.acb(0,m*tau),beta,sigma)
        one+=(plus-minus)/m
        two+=(plus**2-minus**2)/m
    scale=flint.acb(0,2*flint.arb.pi())
    j=(f-r)/2-one/scale
    j2=(f**2-r2)/2-two/scale
    result=f**2-2*f*j+j2
    # Abel summation gives a sawtooth tail <=1/(pi*N*|sin(pi*x)|).
    # On integer indices x=log_b n, use sin(pi*distance)>=2*distance
    # and distance>=1/(sqrt(b)*n*log(b)); exact resonances have no error.
    error=flint.arb(b).sqrt()*flint.arb(b).log()*(real(sigma-1).zeta()-1/(1-flint.arb(b)**(-real(sigma-1))))
    error/=2*flint.arb.pi()*(degree+1)
    return f,r,result,error*(2*f.abs_upper()+1)


def coefficient_series(values,s):
    return sum((real(v)*(-s*flint.arb(n).log()).exp() for n,v in enumerate(values[1:],1)),flint.acb(0))


def fresh_arithmetic_coefficients(beta,b,cutoff=768):
    g=[Q(0)]+[d_beta(n,beta) for n in range(1,cutoff+1)]
    lower=[Q(0)]*(cutoff+1)
    paired=[Q(0)]*(cutoff+1)
    for a in range(1,cutoff+1):
        for c in range(1,cutoff//a+1):
            if h(a*c,b)==h(a,b)+h(c,b):lower[a*c]+=g[a]*g[c]
    k=1
    while k<=cutoff:
        for m in range(1,cutoff//k+1):paired[k*m]+=g[k]*g[m]
        k*=b
    return lower,paired


def point_checks(source):
    records=[]
    for item in source['actual_zeta_ball_checks']:
        b,beta,sigma,height=item['base'],Q(item['beta']),Q(item['s'][0]),item['s'][1]
        lower,paired=fresh_arithmetic_coefficients(beta,b)
        s=flint.acb(real(sigma),height)
        finite_lower,finite_pair=coefficient_series(lower,s),coefficient_series(paired,s)
        f,r,reference,spectral_error=ordinary_fourier_reference(s,sigma,beta,b)
        tail=flint.arb(768)**(1-real(sigma))/(real(sigma)-1)
        tests=[]
        perturbation=real(Q(1,11))*(-s*flint.arb(2).log()).exp()
        for name,finite,value,allowed in (('pair_coefficient_product',finite_pair,f*r,tail),
                                         ('ordinary_partial_Fourier_sum',finite_lower,reference,tail+spectral_error)):
            good=(finite-value).abs_upper()
            bad=(finite+perturbation-value).abs_lower()
            tests.append({'representation':name,'difference_upper_ball':str(good),'proved_bound_ball':str(allowed),
                          'within_bound':bool(good<allowed),'independent_coefficient_error_rejected':bool(bad>allowed)})
        records.append({'s':item['s'],'base':b,'beta':str(beta),'arithmetic_cutoff':768,'ordinary_Fourier_degree':384,
                        'comparisons':tests,'all_passed':all(x['within_bound'] and x['independent_coefficient_error_rejected'] for x in tests)})
    return records


def actual_zero_control(source):
    item=source['actual_critical_line_zero_control']
    height=Q(item['disk_centre'][1]);small=Q(item['radius']);large=Q(1,100)
    c=flint.acb(real(Q(1,2)),real(height))
    region=flint.acb(real(Q(1,2))+flint.arb(0,real(small)),real(height)+flint.arb(0,real(small)))
    wider=flint.acb(real(Q(1,2))+flint.arb(0,real(large)),real(height)+flint.arb(0,real(large)))
    jet=flint.acb_series([c,1],2).zeta()
    ratio=real(small/large)
    error=jet[0].abs_upper()+wider.zeta().abs_upper()*ratio**2/(1-ratio)
    linear=jet[1].abs_lower()*real(small)
    records=[]
    for stored in item['records']:
        b,beta=stored['base'],Q(stored['beta'])
        correction=resonance(region,beta,b,degree=64)
        lower=correction.real.lower()
        records.append({'base':b,'beta':str(beta),'independent_resonance_degree':64,
                        'real_part_lower_after_infinite_tail_ball':str(lower),'correction_nonzero_certified':bool(lower>0)})
    return {'independent_Cauchy_larger_radius':str(large),'Cauchy_Rouche_error_upper_ball':str(error),
            'linear_comparison_lower_ball':str(linear),'one_simple_actual_zeta_zero_independently_certified':bool(error<linear),
            'resonance_records':records,'all_passed':bool(error<linear) and all(x['correction_nonzero_certified'] for x in records)}


def main():
    flint.ctx.prec=192
    source=json.loads((BASE/'size-results/size_analytic_probe.json').read_text())
    exact=json.loads((BASE/'size-results/size_carry_verification.json').read_text())
    assert exact['all_passed']
    points=point_checks(source)
    zero=actual_zero_control(source)
    moment_tests=[]
    for b in (2,6,12):
        for beta in (Q(1,2),Q(1,4),Q(1,8),Q(1)):
            values=resonance_coefficients(beta,b,32)
            passed=True
            while values:
                passed &= all(v>=0 for v in values)
                values=[a-b for a,b in zip(values,values[1:])]
            moment_tests.append(passed)
    result={'actual_zeta_ball_checks':points,'actual_zero_control':zero,
            'exact_resonance_moment_difference_checks_passed':all(moment_tests),
            'continuous_parameter_theorem_source':'Written beta integral proof in size_carry_proof.txt; finite differences are supporting checks only',
            'all_passed':all(x['all_passed'] for x in points) and zero['all_passed'] and all(moment_tests),
            'shared_trusted_kernel':'FLINT/Arb','proof':'size_carry_proof.txt'}
    (BASE/'size-results/size_analytic_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f"Independent size analytic audit: points={sum(x['all_passed'] for x in points)}/{len(points)}, "
          f"Cauchy actual-zero and resonance checks={zero['all_passed']}, all={result['all_passed']}")
    assert result['all_passed']


if __name__=='__main__':main()
