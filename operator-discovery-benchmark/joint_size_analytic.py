#!/usr/bin/env python3
"""Actual-zeta comparisons for two-size root lifts and torus controls."""

from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import time

import flint

from joint_size_search import height


BASE=Path(__file__).resolve().parent


def rb(value):
    value=Q(value)
    return flint.arb(value.numerator)/value.denominator


def prime_power(base):
    for p in range(2,base+1):
        if base%p==0:
            n,e=base,0
            while n%p==0:n//=p;e+=1
            if n!=1:raise ValueError('This analytic evaluator is restricted to prime-power bases')
            return p,e


def resonance(s,base,beta):
    p,e=prime_power(base)
    x=(-s*flint.arb(base).log()).exp()
    if beta==1:return 1/(1-x)
    numerator=[flint.acb(rb(Q(beta+j,e))) for j in range(e)]
    denominator=[flint.acb(rb(Q(j+1,e))) for j in range(e-1)]
    return x.hypgeom(numerator,denominator)


def common_power_base(b,c):
    p,e=prime_power(b);r,f=prime_power(c)
    if p!=r:return None
    from math import gcd
    return p**(e*f//gcd(e,f))


def weights(degree):
    result={0:flint.acb(rb(Q(1,2)))}
    for m in range(1,degree+1):
        value=rb(Q(degree+1-m,(degree+1)*m))/(2*flint.arb.pi())
        result[m]=flint.acb(0,value)
        result[-m]=flint.acb(0,-value)
    return result


def theta_approx(n,base,degree):
    if n==base**height(n,base):return flint.arb(0)
    angle=2*flint.arb.pi()*flint.arb(n).log()/flint.arb(base).log()
    return rb(Q(1,2))-sum((rb(Q(degree+1-m,(degree+1)*m))*(m*angle).sin()/flint.arb.pi()
                          for m in range(1,degree+1)),flint.arb(0))


def filtered_resonance(s,base,other,beta,degree,cutoff=48):
    p,e=prime_power(base)
    root=[Q(1)]
    for j in range(1,e*cutoff+1):root.append(root[-1]*(beta+j-1)/j)
    theta=[theta_approx(p**j,other,degree) for j in range(e*cutoff+1)]
    coeffs=[sum((rb(root[j]*root[e*k-j])*theta[e*k-j] for j in range(e*k+1)),flint.arb(0)) for k in range(cutoff+1)]
    x=(-s*flint.arb(base).log()).exp()
    value=sum((v*x**k for k,v in enumerate(coeffs)),flint.acb(0))
    # Fejer-corrected theta is in [0,1] and d_(2beta)<=1 here.
    tail=x.abs_upper()**(cutoff+1)/(1-x.abs_upper())
    return value,tail


def fejer_error(sigma,base,degree):
    n=flint.arb(degree+1)
    first=(1+2*n.log())/(4*n)
    v=flint.arb(base)
    return first*(rb(sigma).zeta()-1/(1-v**(-rb(sigma))))+v.sqrt()*v.log()/(2*n)*(rb(sigma-1).zeta()-1/(1-v**(1-rb(sigma))))


def spectral_lift(s,sigma,b,c,beta=Q(1,2),degree=48):
    assert beta==Q(1,2) and sigma>2
    assert bool(rb(sigma).zeta().log()<flint.arb.pi())
    wb,wc=weights(degree),weights(degree)
    tb=2*flint.arb.pi()/flint.arb(b).log();tc=2*flint.arb.pi()/flint.arb(c).log()
    grid={}
    for m,n in product(wb,wc):
        point=s-flint.acb(0,m*tb+n*tc)
        grid[m,n]=(rb(beta)*point.zeta().log()).exp()
    f=grid[0,0]
    sb=sum((v*grid[m,0] for m,v in wb.items()),flint.acb(0))
    sc=sum((v*grid[0,n] for n,v in wc.items()),flint.acb(0))
    sb2=sum((v*grid[m,0]**2 for m,v in wb.items()),flint.acb(0))
    sc2=sum((v*grid[0,n]**2 for n,v in wc.items()),flint.acb(0))
    r_c={m:resonance(s-flint.acb(0,m*tb),c,beta) for m in wb}
    r_b={n:resonance(s-flint.acb(0,n*tc),b,beta) for n in wc}
    r_c2={m:resonance(s-flint.acb(0,m*tb),c,2*beta) for m in wb}
    r_b2={n:resonance(s-flint.acb(0,n*tc),b,2*beta) for n in wc}
    jb=sb-r_b[0]/2;jc=sc-r_c[0]/2
    pb=sb2-r_b2[0]/2;pc=sc2-r_c2[0]/2
    common=common_power_base(b,c)
    rbc=resonance(s,common,beta) if common else flint.acb(1)
    rbc2=resonance(s,common,2*beta) if common else flint.acb(1)
    double=sum((vb*vc*grid[m,n] for m,vb in wb.items() for n,vc in wc.items()),flint.acb(0))
    double2=sum((vb*vc*grid[m,n]**2 for m,vb in wb.items() for n,vc in wc.items()),flint.acb(0))
    jb_c=double-sum((v*r_c[m] for m,v in wb.items()),flint.acb(0))/2-sum((v*r_b[n] for n,v in wc.items()),flint.acb(0))/2+rbc/4
    pb_c=double2-sum((v*r_c2[m] for m,v in wb.items()),flint.acb(0))/2-sum((v*r_b2[n] for n,v in wc.items()),flint.acb(0))/2+rbc2/4
    rb_h,tail_b=filtered_resonance(s,b,c,beta,degree)
    rc_h,tail_c=filtered_resonance(s,c,b,beta,degree)
    output_b=sum((v*grid[m,0]*(sum((z*grid[m,n] for n,z in wc.items()),flint.acb(0))-r_c[m]/2) for m,v in wb.items()),flint.acb(0))-rb_h/2
    output_c=sum((v*grid[0,n]*(sum((z*grid[m,n] for m,z in wb.items()),flint.acb(0))-r_b[n]/2) for n,v in wc.items()),flint.acb(0))-rc_h/2
    value=f*f-2*f*(jb+jc)+pb+pc+2*f*jb_c+2*jb*jc-2*output_b-2*output_c+pb_c
    eb,ec=fejer_error(sigma,b,degree),fejer_error(sigma,c,degree)
    kernel_error=(2*rb(sigma).zeta()**rb(beta)+1)*min(eb+2*ec,ec+2*eb)
    return value,kernel_error+tail_b+tail_c


def actual_zeta_checks(source):
    lookup={tuple(x['bases']):x for x in source['zeta_profiles']}
    cases=((2,3,3,'89.23'),(2,3,3,'-97.37'),(2,5,4,'197.11'),(2,5,4,'-211.53'),(2,4,6,'331.79'),(2,4,6,'-347.17'))
    records=[]
    for b,c,sigma,t in cases:
        s=flint.acb(sigma,t);item=lookup[b,c]
        coefficients=next(x['coefficients'] for x in item['root_lifts'] if x['q']==2)
        arithmetic=sum((rb(Q(coefficients[n]))*(-s*flint.arb(n).log()).exp() for n in range(1,item['cutoff']+1)),flint.acb(0))
        spectral,error=spectral_lift(s,sigma,b,c)
        tail=flint.arb(item['cutoff'])**(1-sigma)/(sigma-1)
        error+=tail
        delta=2*(-s*flint.arb(2).log()).exp()
        difference=(arithmetic-spectral).abs_upper();corrupt=(arithmetic+delta-spectral).abs_lower()
        passed=bool(difference<error) and bool(corrupt>error)
        records.append({'bases':[b,c],'s':[str(sigma),t],'root_order':2,'arithmetic_cutoff':item['cutoff'],
                        'Fejer_degree':48,'resonance_cutoff':48,'difference_upper_ball':str(difference),'proved_infinite_error_ball':str(error),
                        'coefficient_2_perturbation':2,'perturbed_difference_lower_ball':str(corrupt),'all_passed':passed})
        print(f'Joint actual-zeta b,c={b},{c}, s={sigma}+{t}i: {passed}',flush=True)
    return records


def torus_moment_controls():
    records=[]
    for (b,c),k,q in product(((2,3),(2,5),(2,6)),(32,64,128),(2,4)):
        eps=flint.arb(2)**(-k);sigma=1+eps;a=rb(Q(1,q))
        tb=2*flint.arb.pi()/flint.arb(b).log();tc=2*flint.arb.pi()/flint.arb(c).log()
        mass=eps**a*sigma.zeta()**a
        moments=[]
        for m,n in product(range(-2,3),repeat=2):
            if not (m or n):continue
            frequency=m*tb+n*tc
            nonzero=bool(frequency.abs_lower()>0)
            upper=eps**a*flint.acb(sigma,frequency).zeta().abs_upper()**a
            moments.append({'mode':[m,n],'frequency_ball':str(frequency),'frequency_certified_nonzero':nonzero,
                            'angular_Fourier_modulus_upper_ball':str(upper)})
        records.append({'bases':[b,c],'epsilon_power_of_two':-k,'root_order':q,'total_mass_ball':str(mass),
                        'moments':moments,'all_frequencies_certified_nonzero':all(x['frequency_certified_nonzero'] for x in moments),
                        'scope':'Finite actual-root Fourier-modulus controls; the natural-boundary theorem is universal and not inferred from these samples'})
    dependent=[]
    for b,c,k in product((2,3),(2,),(32,64,128)):
        c=b**c
        eps=flint.arb(2)**(-k);a=rb(Q(1,2))
        magnitude=eps**a*(1+eps).zeta()**a
        dependent.append({'bases':[b,c],'nonconstant_mode_with_identically_zero_frequency':[1,-2],
                          'epsilon_power_of_two':-k,'moment_modulus_lower_ball':str(magnitude),
                          'independence_shortcut_rejected':bool(magnitude>rb(Q(9,10)))})
    return {'independent_records':records,'dependent_records':dependent,
            'all_passed':all(x['all_frequencies_certified_nonzero'] for x in records) and all(x['independence_shortcut_rejected'] for x in dependent)}


def main():
    started=time.monotonic();flint.ctx.prec=192
    source=json.loads((BASE/'joint-results/joint_size_search.json').read_text())
    points=actual_zeta_checks(source);moments=torus_moment_controls()
    result={'actual_zeta_ball_checks':points,'actual_root_torus_moment_controls':moments,
            'dependent_intersection_resonance_counterexample':{'bases':[2,4],'index':4,'correct_coefficient':'3/4','wrong_coefficient_if_common_power_projection_is_unit_only':'5/16'},
            'natural_boundary_proof_scope':'Every multiplicatively independent pair b,c; every finite q>=2 and alpha>0; Re(s)=1 is a natural boundary',
            'quantitative_spectral_domain':'Re(s)>2 for the explicit Fejer error; exact arithmetic identity on Re(s)>1',
            'new_RH_estimate_proved':False,'all_passed':all(x['all_passed'] for x in points) and moments['all_passed'],
            'proof':'joint_size_proof.txt','elapsed_seconds':time.monotonic()-started}
    (BASE/'joint-results/joint_size_analytic.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'Joint actual-zeta audit: all={result["all_passed"]}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__=='__main__':main()
