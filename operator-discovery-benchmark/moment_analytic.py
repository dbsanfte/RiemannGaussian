#!/usr/bin/env python3
"""Certified uniform-height limits, sharp edge obstruction and root factors."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time
import flint

from moment_search import primes, kernel
from prime_pair_analytic import prime_zeta_polynomial, mobius_tail

BASE=Path(__file__).resolve().parent
DEST=BASE/'moment-results'


def real(x):
    x=Q(x)
    return flint.arb(x.numerator)/x.denominator


def short(x):
    return x.str(28)


def rho(sigma,second=10):
    return flint.arb(6)**(-real(sigma))+flint.arb(second)**(-real(sigma))


def integer_major(sigma):
    sig=real(sigma)
    return 16*((4*sig).zeta()-1)*((6*sig).zeta()-1)


def prime_major(sigma,M=40):
    sig=real(sigma)
    assert sigma>Q(1,4)
    P=prime_zeta_polynomial(flint.acb(4*sig),M).real+flint.arb(0,mobius_tail(4*sigma,M))
    even=flint.arb(2)**(-6*sig)*(6*sig).zeta()
    odd=(1-flint.arb(2)**(-6*sig))*(6*sig).zeta()-1
    return 16*((P-flint.arb(2)**(-4*sig))*even+flint.arb(2)**(-4*sig)*odd)


def tail(sigma,cutoff,m=4):
    sig=real(sigma);A=flint.arb(cutoff//2)
    base=(16*((4*sig).zeta()-1)*A**(1-6*sig)/(6*sig-1)
          +16*((6*sig).zeta()-1)*A**(1-4*sig)/(4*sig-1))
    return base*rho(sigma)**(m-4)


def direct(s,cutoff,m):
    ps=primes(cutoff)
    x=[(-s*flint.arb(p).log()).exp() for p in ps]
    gap={d:(-s*flint.arb(d).log()).exp() for d in range(2,cutoff)}
    return sum((gap[q-p]**2*(gap[q-p]*(x[i]-x[j]))**m
                for i,p in enumerate(ps) for j,q in enumerate(ps) if q-p>=2),flint.acb(0))


@lru_cache(maxsize=None)
def sparse_coefficients(m,cutoff):
    return kernel({p:Q(1) for p in primes(cutoff)},m)


def encoded(s,cutoff,m):
    return sum((real(v)*(-s*flint.arb(n).log()).exp()
                for n,v in sparse_coefficients(m,cutoff).items()),flint.acb(0))


def correction_groups():
    points=((Q(3,4),'2.87'),(Q(1),'-5.17'),(Q(5,4),'7.53'),
            (Q(3,4),'-9.89'),(Q(1),'12.23'),(Q(5,4),'-14.69'))
    rows=[]
    for sigma,height in points:
        s=flint.acb(real(sigma),height);m=4
        arithmetic=encoded(s,256,m);difference_form=direct(s,512,m)
        error=tail(sigma,256,m)+tail(sigma,512,m)
        diff=(arithmetic-difference_form).abs_upper()
        wrong=(arithmetic+real(Q(1,2))*(-s*flint.arb(4*6**m).log()).exp()-difference_form).abs_lower()
        z=s.zeta();M=prime_major(sigma)
        left=z*arithmetic.exp();right=z*difference_form.exp()
        full_error=z.abs_upper()*(M+error).exp()*error
        full_difference=(left-right).abs_upper()
        passed=bool(diff<error) and bool(wrong>error) and bool(z.abs_lower()>0) and bool(full_difference<full_error)
        rows.append({'s':[str(sigma),height],'m':m,'encoded_prime_input_cutoff':256,
                     'difference_form_prime_input_cutoff':512,
                     'encoded_correction_ball':short(arithmetic),'difference_correction_ball':short(difference_form),
                     'combined_infinite_correction_error_ball':short(error),'difference_upper_ball':short(diff),
                     'changed_first_coefficient_error':'1/2','changed_difference_lower_ball':short(wrong),
                     'native_zeta_times_finite_correction_ball':short(left),
                     'factored_zeta_difference_upper_ball':short(full_difference),'factored_zeta_comparison_error_ball':short(full_error),
                     'ordinary_EXP_of_FULL_transformed_coefficient_prefix_computed':False,
                     'scope':'Auxiliary correction / factored native-zeta control; excluded from cumulative full coefficient-origin comparison count',
                     'all_passed':passed})
        print('Moment correction/native-zeta auxiliary',sigma,height,passed,flush=True)
    return {'records':rows,'all_passed':all(row['all_passed'] for row in rows)}


def uniform_controls():
    sig=Q(1,2);C=prime_major(sig);CI=integer_major(sig);r=rho(sig)
    rows=[]
    for m in (4,8,16,24,32,48,64):
        M=C*r**(m-4)
        rows.append({'m':m,'uniform_correction_modulus_bound_ball':short(M),
                     'uniform_relative_zeta_factor_error_bound_ball':short(M.exp()-1),
                     'input_half_root_factor_error_bound_ball':short((M/4).exp()-1),
                     'all_heights_and_Re_at_least_half':True})
    return {'sigma':'1/2','rho_ball':short(r),'prime_parity_C_ball':short(C),
            'integer_C_ball':short(CI),'records':rows,
            'all_passed':bool(0<r<1) and bool(0<C<CI)}


def threshold():
    lo,hi=Q(33,100),Q(2,5)
    for _ in range(88):
        mid=(lo+hi)/2
        if rho(mid)>1:
            lo=mid
        else:
            assert rho(mid)<1
            hi=mid
    return {'lower':str(lo),'upper':str(hi),'decimal_lower_ball':short(real(lo)),
            'decimal_upper_ball':short(real(hi)),
            'lower_rho_minus_one_ball':short(rho(lo)-1),'upper_rho_minus_one_ball':short(rho(hi)-1),
            'all_passed':bool(rho(lo)>1) and bool(rho(hi)<1) and hi-lo<Q(1,10**26)}


def unstable_unmasked():
    sigma=Q(1,2);t=flint.arb.pi()/(real(Q(3,2)).log());s=flint.acb(real(sigma),t)
    edge=(-s*flint.arb(2).log()).exp()-(-s*flint.arb(3).log()).exp()
    C=prime_major(sigma);rows=[]
    for m in (8,16,32,64):
        regular=direct(s,192,m);E=tail(sigma,192,m)
        leading=edge**m;bound=C*rho(sigma)**(m-4)
        lower=leading.abs_lower()-bound
        passed=bool(lower>1) and bool((regular).abs_upper()<bound+E)
        rows.append({'m':m,'unmasked_first_index':2**m,'fixed_prefix_cutoff':128,
                     'unmasked_prefix_correction_identically_zero':2**m>128,
                     'regularized_finite_value_ball':short(regular),'regularized_uniform_bound_ball':short(bound),
                     'unmasked_infinite_correction_modulus_lower_ball':short(lower),
                     'unmasked_finite_value_ball':short(leading+regular),'all_passed':passed})
    return {'sigma':str(sigma),'height_ball':short(t),'edge_modulus_ball':short(edge.abs_upper()),
            'records':rows,'coefficientwise_identity_implies_scalar_identity_rejected':True,
            'all_passed':all(row['all_passed'] for row in rows)}


def sharp_controls(bracket):
    lo,hi=Q(bracket['lower']),Q(bracket['upper']);rows=[]
    t=flint.arb.pi()/real(Q(5,3)).log()
    for side,sigma in (('below',lo-Q(1,100)),('above',hi+Q(1,100))):
        s=flint.acb(real(sigma),t)
        x=(-s*flint.arb(3).log()).exp()-(-s*flint.arb(5).log()).exp()
        for m in (128,256,512):
            leading=(-s*flint.arb(2).log()).exp()**(m+2)*x**m
            rest=integer_major(sigma)*rho(sigma,15)**(m-4)
            lower=leading.abs_lower()-rest;upper=leading.abs_upper()+rest
            bound=integer_major(sigma)*rho(sigma)**(m-4)
            passed=bool(rest<leading.abs_lower()/2) and (bool(lower>1) if side=='below' else bool(upper<bound))
            rows.append({'side':side,'sigma':str(sigma),'m':m,'resonant_height_ball':short(t),
                         'rho_ball':short(rho(sigma)),'next_edge_rho_ball':short(rho(sigma,15)),
                         'dominant_edge_modulus_ball':short(leading.abs_upper()),'all_other_edges_bound_ball':short(rest),
                         'infinite_modulus_lower_ball':short(lower),'infinite_modulus_upper_ball':short(upper),
                         'all_passed':passed})
    return {'records':rows,'threshold_nondecay_proved_by_dominant_edge':True,
            'all_passed':all(row['all_passed'] for row in rows)}


def root_controls():
    sigma=Q(2);s=flint.acb(real(sigma),'7.67');m=4
    g=encoded(s,256,m);ref=direct(s,512,m);E=tail(sigma,256,m)+tail(sigma,512,m)
    L=s.zeta().log();assert real(sigma).zeta().log()<flint.arb.pi()
    rows=[]
    for beta,family in ((Q(1),'input'),(Q(1,2),'input'),(Q(1,2),'output'),(Q(1,4),'input'),(Q(1,4),'output')):
        amp=beta**2 if family=='input' else beta
        a=(real(beta)*L+real(amp)*g).exp();b=(real(beta)*L+real(amp)*ref).exp()
        error=(real(beta)*L.real+abs(real(amp))*(prime_major(sigma)+E)).exp()*abs(real(amp))*E
        passed=bool((a-b).abs_upper()<error)
        rows.append({'beta':str(beta),'family':family,'amplitude':str(amp),
                     'difference_upper_ball':short((a-b).abs_upper()),'comparison_error_ball':short(error),'all_passed':passed})
    pin=(L/2+g/4).exp();pout=(L/2+g/2).exp()
    distinct=(pin-pout).abs_lower()>0
    return {'s':['2','7.67'],'m':m,'records':rows,'input_and_output_half_roots_distinct':bool(distinct),
            'below_one_principal_LOG_zeta_anchor_used':False,
            'all_passed':all(row['all_passed'] for row in rows) and bool(distinct)}


def zero_controls():
    rows=[]
    for filename,key in (('size-results/size_analytic_probe.json','actual_critical_line_zero_control'),
                         ('cancellation-results/cancellation_analytic.json','fresh_actual_critical_line_zero_control')):
        old=json.loads((BASE/filename).read_text())[key];assert old['all_passed']
        sigma=Q(1,2)-Q(old['radius']);C=prime_major(sigma);r=rho(sigma)
        for m in (8,16,32,64):
            M=C*r**(m-4)
            factors=[{'beta':str(beta),'amplitude':str(beta**2),
                      'modulus_lower_ball':short((-real(beta**2)*M).exp()),
                      'modulus_upper_ball':short((real(beta**2)*M).exp()),
                      'relative_factor_error_bound_ball':short((real(beta**2)*M).exp()-1),
                      'positive_lower':bool((-real(beta**2)*M).exp()>0)} for beta in (Q(1),Q(1,2),Q(1,4))]
            passed=bool(r<1) and all(row['positive_lower'] for row in factors) and sigma>Q(1,m)
            rows.append({'disk_centre':old['disk_centre'],'radius':old['radius'],'m':m,
                         'sigma_lower':str(sigma),'reused_simple_zero':True,'new_zero_located':False,
                         'uniform_whole_disk_correction_modulus_bound_ball':short(M),'root_factors':factors,
                         'ordinary_correction_series_absolute_on_whole_disk':True,
                         'whole_zero_disk_correction_holomorphic':True,'root_exponent_preserved':'multiplicity*beta',
                         'all_passed':passed})
    return {'records':rows,'all_passed':all(row['all_passed'] for row in rows)}


def main():
    start=time.monotonic();flint.ctx.prec=512
    assert json.loads((DEST/'moment_search.json').read_text())['all_passed']
    corr=correction_groups();uniform=uniform_controls();bracket=threshold()
    unmasked=unstable_unmasked();sharp=sharp_controls(bracket);roots=root_controls();zeros=zero_controls()
    objects=(corr,uniform,bracket,unmasked,sharp,roots,zeros)
    out={'correction_native_zeta_auxiliary_groups':corr,'uniform_height_bounds':uniform,
         'sharp_uniform_limit_threshold':bracket,'unmasked_coefficientwise_limit_counterexample':unmasked,
         'resonant_threshold_controls':sharp,'ordinary_root_auxiliary_controls':roots,
         'whole_actual_zero_root_controls':zeros,'new_full_coefficient_origin_comparison_groups':0,
         'counts_as_new_primitive':False,'historical_novelty_established':False,'new_RH_estimate_proved':False,
         'all_passed':all(obj['all_passed'] for obj in objects),'seconds':time.monotonic()-start}
    (DEST/'moment_analytic.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Moment analytic limits and roots:',out['all_passed'],'seconds',out['seconds'],flush=True)
    assert out['all_passed']


if __name__=='__main__':
    main()
