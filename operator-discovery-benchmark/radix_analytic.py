#!/usr/bin/env python3
"""Native radix-three bridge, spurious zero, and complete branch-ladder tests."""

from fractions import Fraction as Q
from functools import lru_cache
from math import factorial
from pathlib import Path
import json
import time
import flint

from radix_search import allowed
from prime_pair_analytic import mobius, mobius_tail

BASE=Path(__file__).resolve().parent
DEST=BASE/'radix-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def short(x):return x.str(25)


def box(r):return flint.acb(flint.arb(0,r),flint.arb(0,r))


@lru_cache(maxsize=None)
def splits(n,b):return tuple(k for k in range(1,n+1) if allowed(k,n-k,b))


def graded_exp(h,b=3):
    zero=h[0]*0;one=zero+1;out=[one]+[zero]*(len(h)-1)
    for n in range(1,len(h)):
        out[n]=sum((k*h[k]*out[n-k] for k in splits(n,b)),zero)/n
    return out


def native_P(s,M=32):
    return sum((real(Q(mobius(k),k))*(k*s).zeta().log() for k in range(1,M+1) if mobius(k)),s*0)


def local_cutoff(k,M):
    # Fixed per grade, hence a single analytic finite approximant on the
    # entire certification disk. All newly omitted terms are bounded below.
    return min(M,max(1,96//k))


def enclose_finite_P(s,k,M,sigma):
    value=flint.acb(0)
    for m in range(1,M+1):
        mu=mobius(m)
        if not mu:continue
        if m*k>=8:
            x=real(m*k*sigma)
            term=box(flint.arb(2)**(-x)*(1+2/(x-1)))
        else:term=(m*k*s).zeta().log()
        value+=real(Q(mu,m))*term
    return value


def finite(s,b=3,beta=Q(1),D=192,M=32,components=False,enclose_sigma=None):
    zero=s*0;h=[zero,zero]
    for k in range(2,D+1):
        Mk=local_cutoff(k,M)
        if enclose_sigma is not None and k>=8:
            x=real(k*enclose_sigma)
            bound=flint.arb(2)**(-x)*(1+2/(x-1))+mobius_tail(k*enclose_sigma,Mk)
            value=box(bound)
        elif enclose_sigma is not None:value=enclose_finite_P(s,k,Mk,enclose_sigma)
        else:value=native_P(k*s,Mk)
        h.append(real(beta)*value/k)
    q=sum(h[2:],zero)
    h[1]=real(beta)*s.zeta().log()-q
    if not components:return sum(graded_exp(h,b),zero),h
    first=h[1];h[1]=zero
    e=graded_exp(h,b)
    A=[sum((v for n,v in enumerate(e) if n+j<=D and n%b<=b-1-j),zero)/factorial(j) for j in range(b)]
    F=sum((v*first**j for j,v in enumerate(A)),zero)
    h[1]=first
    return F,h,A


def error_bound(sigma,h,beta=Q(1),D=192,M=32):
    assert sigma>Q(1,2)
    t=real(sigma);a=D+1;r=flint.arb(2)**(t/2)
    Qtail=(1+2/(a*t-1))*flint.arb(2)**(-a*t)/(a*(1-flint.arb(2)**(-t)))
    delta=sum((mobius_tail(k*sigma,local_cutoff(k,M))/k for k in range(2,D+1)),flint.arb(0))
    E1=real(abs(beta))*(delta+Qtail)
    E=real(abs(beta))*(2*delta+Qtail)
    C0=sum((v.abs_upper() for v in h[1:]),flint.arb(0))
    C=(r*(h[1].abs_upper()+E1)+real(abs(beta))*r*r/(2*(1-r*flint.arb(2)**(-t)))
       *(flint.arb(2)**(-2*t)+flint.arb(2)**(1-2*t)/(2*t-1)))
    return E*(C0+E).exp()+C.exp()*r**(-D-1)


def full_groups():
    exact=json.loads((DEST/'radix_search.json').read_text())
    coefs=list(map(Q,next(row for row in exact['zeta_profiles']['records'] if row['radix']==3 and row['beta']=='1')['coefficients']))
    rows=[]
    for sigma,height in ((Q(4),'3.19'),(Q(5),'-6.43'),(Q(6),'9.71'),(Q(4),'-13.03'),(Q(5),'16.37'),(Q(6),'-19.73')):
        s=flint.acb(real(sigma),height);F,h=finite(s,D=64)
        E=error_bound(sigma,h,D=64)
        prefix=sum((real(v)*(-s*flint.arb(n).log()).exp() for n,v in enumerate(coefs) if v),flint.acb(0))
        tail=real(4096)**(1-real(sigma))/(real(sigma)-1)+E
        diff=(prefix-F).abs_upper()
        wrong=(prefix+real(Q(1,11))*(-s*flint.arb(8).log()).exp()-F).abs_lower()
        passed=bool(diff<tail) and bool(wrong>tail)
        rows.append({'s':[str(sigma),height],'radix':3,'beta':'1','ordinary_coefficient_cutoff':4096,
                     'grade_cutoff':64,'Mobius_cutoff':32,'difference_upper_ball':short(diff),
                     'combined_infinite_error_ball':short(tail),'changed_coefficient_eight_error':'1/11',
                     'changed_difference_lower_ball':short(wrong),'all_passed':passed})
        print('Radix-three full coefficient-origin/native-zeta',sigma,height,passed,flush=True)
    return rows


def leading_controls():
    rows=[]
    for b in (3,4,5,7):
        sigma=Q(3,4);s=flint.acb(real(sigma),'4.29');beta=Q(1)
        F,h,A=finite(s,b,beta,D=96,components=True)
        # The leading coefficient is supported on grades divisible by b.
        # Independently evaluate the scaled transfer at b*s, beta/b.
        scaled,hs=finite(b*s,b,Q(1,b),D=64)
        E=error_bound(sigma,h,D=96)
        Es=error_bound(b*sigma,hs,Q(1,b),D=64)
        diff=(A[-1]-real(beta**(b-1))*scaled/factorial(b-1)).abs_upper()
        lower=2-(real(b*Q(1,2)).zeta()**real(Q(1,b)))
        passed=bool(diff<E+Es) and bool(lower>0)
        rows.append({'radix':b,'s':['3/4','4.29'],'beta':'1','difference_upper_ball':short(diff),
                     'combined_error_ball':short(E+Es),'uniform_critical_half_plane_H_modulus_lower_ball':short(lower),
                     'self_similarity':'leading = beta**(b-1)/(b-1)! * F_(b,beta/b)(b*s)', 'all_passed':passed})
        print('Radix leading self-similarity',b,passed,flush=True)
    return {'records':rows,'all_passed':all(row['all_passed'] for row in rows)}


def corridor(centre,sigma_low,height_radius,multiple=1,segments=128):
    end=Q(3);rows=[]
    for j in range(segments):
        lo=sigma_low+(end-sigma_low)*Q(j,segments);hi=sigma_low+(end-sigma_low)*Q(j+1,segments)
        z=flint.acb(real((lo+hi)/2)+flint.arb(0,real((hi-lo)/2)),centre.imag+flint.arb(0,real(height_radius)))
        value=(multiple*z).zeta()
        clear=bool(value.real>0 or value.imag>0 or value.imag<0)
        rows.append({'real_interval':[str(lo),str(hi)],'native_zeta_ball':short(value),'avoids_principal_LOG_cut':clear})
    return {'multiple':multiple,'segments':segments,'records':rows,'all_passed':all(row['avoids_principal_LOG_cut'] for row in rows)}


def created_zero():
    seed=['0.8726906273277811','14.720036235948083'];c=flint.acb(*seed)
    for _ in range(2):
        v,_=finite(c);u=real(Q(1,100000))
        a,_=finite(c+u);b,_=finite(c-u);d=(a-b)/(2*u)
        next_c=c-v/d
        coords=[format(float(next_c.real.mid()),'.17g'),format(float(next_c.imag.mid()),'.17g')]
        c=flint.acb(*coords)
    # Refinement only locates a candidate. The disk proof below certifies it.
    radius=Q(1,100000);outer=Q(1,100)
    sigma=Q(coords[0])-outer;region=c+box(real(outer))
    anchor=corridor(c,sigma,outer)
    print('Radix artifact branch corridor',anchor['all_passed'],flush=True)
    F,h=finite(region,D=192,M=32,enclose_sigma=sigma);U=error_bound(sigma,h,D=192,M=32)
    M=F.abs_upper();u=outer/1000
    centre_value,_=finite(c,D=192,M=32)
    plus,_=finite(c+real(u),D=192,M=32);minus,_=finite(c-real(u),D=192,M=32)
    derivative=(plus-minus)/(2*real(u))
    derivative_error=M*real(u)**2/real(outer)**3/(1-real(u/outer)**2)
    ratio=real(radius/outer)
    remainder=M*ratio**2/(1-ratio)
    margin=(derivative.abs_lower()-derivative_error)*real(radius)-centre_value.abs_upper()-remainder-U
    rectangle=c+box(real(radius));zeta_lower=rectangle.zeta().abs_lower()
    half_sigma=Q(coords[0])-radius
    half,hh=finite(rectangle,beta=Q(1,2),enclose_sigma=half_sigma);half_error=error_bound(half_sigma,hh,Q(1,2))
    half_lower=half.abs_lower()-half_error
    passed=bool(margin>0) and bool(zeta_lower>0) and bool(half_lower>0) and anchor['all_passed']
    out={'disk_centre':coords,'exploratory_seed':seed,'radius':str(radius),'outer_radius':str(outer),
         'grade_cutoff':192,'Mobius_cutoff':32,'finite_value_ball':short(centre_value),'finite_derivative_ball':short(derivative),
         'derivative_method':'symmetric finite quotient with a proved Cauchy derivative error',
         'derivative_error_ball':short(derivative_error),'derivative_quotient_step':str(u),
         'Mobius_per_grade_rule':'min(32,max(1,96//k))','high_grades_on_rectangles':'proved prime-series and Mobius-tail enclosures for k>=8',
         'outer_finite_modulus_bound_ball':short(M),'Cauchy_higher_order_remainder_ball':short(remainder),
         'infinite_operator_approximation_error_ball':short(U),'Rouche_margin_ball':short(margin),
         'ordinary_zeta_modulus_lower_on_disk_rectangle_ball':short(zeta_lower),
         'transferred_ordinary_input_half_root_modulus_lower_on_disk_rectangle_ball':short(half_lower),
         'exactly_one_simple_transformed_zero_certified':bool(margin>0),
         'ordinary_zeta_zero_in_this_disk':False,'ordinary_output_half_root_has_spurious_monodromy':True,
         'Euler_to_local_LOG_corridor':anchor,'new_ordinary_zeta_zero_located':False,'all_passed':passed}
    print('Radix-three created operator zero certificate',passed,'margin',short(margin),flush=True)
    return out


def blind_spot():
    centre=flint.acb(real(Q(3,4)),'1.37');radius=Q(1,200);base=centre+real(radius)
    region=centre+box(real(radius));z=region.zeta();F,h,A=finite(base,components=True)
    U=error_bound(Q(151,200),h);hop=flint.acb(0,2*flint.arb.pi())
    # Components A[2] already include 1/2. The target is defined using the
    # exact infinite coefficients in the proof. This ball calculation is
    # only a numerical illustration of that exact algebraic construction.
    astar=-A[1]/(2*A[2])-hop/2
    def polynomial(x):return A[0]+A[1]*x+A[2]*x*x
    p=[polynomial(astar+k*hop) for k in range(3)]
    first=p[1]-p[0];second=p[2]-2*p[1]+p[0]
    Hlower=2-real(3*Q(151,200)).zeta()**real(Q(1,3))
    theoretical=hop**2*(2*A[2])
    passed=bool(z.abs_lower()>0) and bool(first.abs_upper()<flint.arb('1e-12')) and bool(second.abs_lower()>0) and second.overlaps(theoretical)
    return {'controlled_extra_zero_location':['3/4','1.37'],'radius':str(radius),
            'actual_zeta_nonzero_on_whole_rectangle':bool(z.abs_lower()>0),
            'basepoint':['151/200','1.37'],'chosen_primitive_log_value_ball':short(astar),
            'single_loop_pointwise_change_ball':short(first),'two_loop_second_difference_ball':short(second),
            'leading_H_lower_ball':short(Hlower),'infinite_coefficient_error_bound_ball':short(U),
            'first_jump_is_exactly_zero_by_constructed_model':True,'second_difference_is_nonzero_by_universal_H_bound':True,
            'scope':'Control for the derived polynomial-log criterion with coefficients fixed from zeta; not the operator on a substituted arithmetic input',
            'all_passed':passed}


def ordinary_root_controls():
    s=flint.acb(2,'8.31');rows=[];base,hbase=finite(s,beta=Q(1));Ebase=error_bound(Q(2),hbase)
    assert real(Q(2)).zeta()-1<1
    for beta,family in ((Q(1),'input'),(Q(1,2),'input'),(Q(1,2),'output'),(Q(1,4),'input'),(Q(1,4),'output')):
        if family=='input':value,h=finite(s,beta=beta);E=error_bound(Q(2),h,beta)
        else:value=(real(beta)*base.log()).exp();E=Ebase*real(beta)/(2-real(Q(2)).zeta())**(1-real(beta))
        rows.append({'beta':str(beta),'family':family,'value_ball':short(value),'approximation_error_ball':short(E),
                     'full_ordinary_EXP_coefficient_prefix_used':False,'all_passed':value.is_finite() and bool(E>0)})
    half,hhalf=finite(s,beta=Q(1,2));Ehalf=error_bound(Q(2),hhalf,Q(1,2))
    diff=(half-base.sqrt()).abs_lower()-Ehalf-Ebase
    return {'s':['2','8.31'],'records':rows,'input_and_ordinary_output_half_roots_distinct':bool(diff>0),
            'distinctness_margin_ball':short(diff),'all_passed':all(row['all_passed'] for row in rows) and bool(diff>0)}


def zero_ladders():
    rows=[]
    for filename,key in (('size-results/size_analytic_probe.json','actual_critical_line_zero_control'),('cancellation-results/cancellation_analytic.json','fresh_actual_critical_line_zero_control')):
        old=json.loads((BASE/filename).read_text())[key];assert old['all_passed']
        c=flint.acb(real(Q(1,2)),old['disk_centre'][1]);rad=Q(old['radius']);sigma=Q(1,2)-rad
        region=c+box(real(rad));z2=(2*region).zeta();path=corridor(c,sigma,rad,multiple=2)
        bounds=[]
        for beta in (Q(1),Q(1,2),Q(1,4)):
            Hlower=2-real(3*sigma).zeta()**real(beta/3)
            difference=4*flint.arb.pi()**2*real(beta**2)*Hlower
            bounds.append({'beta':str(beta),'whole_disk_H_modulus_lower_ball':short(Hlower),
                           'second_log_monodromy_difference_modulus_lower_ball':short(difference),'positive':bool(difference>0)})
        passed=bool(z2.abs_lower()>0) and path['all_passed'] and all(row['positive'] for row in bounds)
        rows.append({'disk_centre':old['disk_centre'],'radius':str(rad),'reused_simple_zero':True,
                     'native_zeta_two_s_modulus_lower_ball':short(z2.abs_lower()),'LOG_zeta_two_s_Euler_corridor':path,
                     'root_parameters_and_second_monodromy_bounds':bounds,'single_loop_sampling_is_not_complete_detector':True,
                     'new_ordinary_zeta_zero_located':False,'all_passed':passed})
    return {'records':rows,'all_passed':all(row['all_passed'] for row in rows)}


def main():
    start=time.monotonic();flint.ctx.prec=512
    assert json.loads((DEST/'radix_search.json').read_text())['all_passed']
    points=full_groups();leading=leading_controls();artifact=created_zero();blind=blind_spot();roots=ordinary_root_controls();zeros=zero_ladders()
    out={'actual_zeta_ball_checks':points,'leading_self_similarity_controls':leading,'created_operator_zero':artifact,
         'single_loop_blind_spot_control':blind,'ordinary_root_auxiliary_controls':roots,'actual_zeta_zero_branch_ladder_controls':zeros,
         'ordinary_root_location_fidelity':'rejected','counts_as_new_primitive':False,'historical_novelty_established':False,
         'new_RH_estimate_proved':False,'all_passed':all(row['all_passed'] for row in points) and all(obj['all_passed'] for obj in (leading,artifact,blind,roots,zeros)),
         'seconds':time.monotonic()-start}
    (DEST/'radix_analytic.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Global radix native analytic source:',out['all_passed'],'seconds',out['seconds'],flush=True)
    assert out['all_passed']


if __name__=='__main__':main()
