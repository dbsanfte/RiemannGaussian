#!/usr/bin/env python3
"""Independent polynomial correlations, integer tails and critical-root audit."""

from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json
import time
import flint

from check_gap import factors
from check_moment import fibres, weights

BASE=Path(__file__).resolve().parent
DEST=BASE/'moment-results'


def real(x):
    x=Q(x)
    return flint.arb(x.numerator)/x.denominator


def short(x):
    return x.str(28)


def primes(N):
    return tuple(n for n in range(2,N+1) if flint.fmpz(n).is_prime())


def envelope(sigma,second=10):
    return (-real(sigma)*flint.arb(6).log()).exp()+(-real(sigma)*flint.arb(second).log()).exp()


def C_integer(sigma):
    return 16*((4*real(sigma)).zeta()-1)*((6*real(sigma)).zeta()-1)


def P_native(t,M=48):
    value=flint.arb(0)
    for k in range(1,M+1):
        fs=factors(k)
        mu=0 if any(e>1 for e in fs.values()) else (-1)**len(fs)
        if mu:
            value+=Q(mu,k).numerator* (k*t).zeta().log()/Q(mu,k).denominator
    ratio=(-t*flint.arb(2).log()).exp()
    remainder=ratio**(M+1)/(M+1)/(1-ratio)*(1+2/((M+1)*t-1))
    return value+flint.arb(0,remainder)


def C_prime(sigma):
    t=real(sigma);z=(6*t).zeta();a=(-4*t*flint.arb(2).log()).exp();b=(-6*t*flint.arb(2).log()).exp()
    return 16*((P_native(4*t)-a)*b*z+a*((1-b)*z-1))


def omitted(sigma,N,m=4):
    # Slightly looser lower split, different from production's N//2.
    A=flint.arb((N-2)//2);t=real(sigma)
    return 16*envelope(sigma)**(m-4)*(
        ((4*t).zeta()-1)*A**(1-6*t)/(6*t-1)
        +((6*t).zeta()-1)*A**(1-4*t)/(4*t-1))


def poly(s,N,m=4):
    powers=[];ps=primes(N)
    for j in range(m+1):
        a=[flint.acb(0)]*(N+1)
        for p in ps:
            a[p]=(-j*s*flint.arb(p).log()).exp()
        powers.append(a)
    value=flint.acb(0)
    gap={d:(-(m+2)*s*flint.arb(d).log()).exp() for d in range(2,N)}
    for j,w in enumerate(weights(m)):
        corr=flint.acb_poly(powers[m-j])*flint.acb_poly(list(reversed(powers[j])))
        value+=w*sum((corr[N-d]*gap[d] for d in range(2,N)),flint.acb(0))
    return value


def encoded(s,N,m):
    ps=primes(N)
    possible={p**(m-j)*q**j*(q-p)**(m+2) for p in ps for q in ps if q-p>=2 for j in range(m+1)}
    out=flint.acb(0)
    for n in possible:
        c=sum(w for p,q,j,w in fibres(n,m) if q<=N)
        out+=c*(-s*flint.arb(n).log()).exp()
    return out


def audit_correction(data):
    rows=[]
    for source in data['correction_native_zeta_auxiliary_groups']['records']:
        sigma,height=Q(source['s'][0]),source['s'][1];s=flint.acb(real(sigma),height)
        a=encoded(s,192,4);b=poly(s,384,4);E=omitted(sigma,192)+omitted(sigma,384)
        wrong=(a+real(Q(1,3))*(-s*flint.arb(5184).log()).exp()-b).abs_lower()
        passed=bool((a-b).abs_upper()<E) and bool(wrong>E)
        z=s.zeta();factor_error=z.abs_upper()*(C_integer(sigma)+E).exp()*E
        passed=passed and bool((z*a.exp()-z*b.exp()).abs_upper()<factor_error)
        assert source['ordinary_EXP_of_FULL_transformed_coefficient_prefix_computed'] is False
        rows.append({'s':source['s'],'encoded_prime_input_cutoff':192,'polynomial_prime_input_cutoff':384,
                     'difference_upper_ball':short((a-b).abs_upper()),'combined_integer_tail_ball':short(E),
                     'changed_first_coefficient_error':'1/3','changed_difference_lower_ball':short(wrong),
                     'all_passed':passed})
    assert all(row['all_passed'] for row in rows)
    return {'records':rows,'all_passed':True}


def audit_uniform(data):
    C=C_prime(Q(1,2));CI=C_integer(Q(1,2));r=envelope(Q(1,2))
    source=data['uniform_height_bounds'];assert C.overlaps(flint.arb(source['prime_parity_C_ball']))
    assert r.overlaps(flint.arb(source['rho_ball'])) and 0<C<CI and r<1
    rows=[]
    for row in source['records']:
        m=row['m'];bound=C*r**(m-4);generic=CI*r**(m-4)
        assert bound.overlaps(flint.arb(row['uniform_correction_modulus_bound_ball']))
        assert (bound.exp()-1).overlaps(flint.arb(row['uniform_relative_zeta_factor_error_bound_ball']))
        assert ((bound/4).exp()-1).overlaps(flint.arb(row['input_half_root_factor_error_bound_ball']))
        rows.append({'m':m,'independent_prime_bound_ball':short(bound),'independent_integer_bound_ball':short(generic)})
    # Finite independent graph edge maxima are supplementary to the proof.
    for p in primes(127):
        for q in primes(127):
            if q-p>=2:
                v=real(Q(1,p*(q-p))).sqrt()+real(Q(1,q*(q-p))).sqrt()
                assert v<=r or (p,q)==(3,5)
    return {'records':rows,'prime_C_ball':short(C),'integer_C_ball':short(CI),'all_passed':True}


def audit_threshold(data):
    source=data['sharp_uniform_limit_threshold'];lo,hi=Q(source['lower']),Q(source['upper'])
    assert envelope(lo)>1 and envelope(hi)<1 and hi-lo<Q(1,10**26)
    a,b=Q(1,3),Q(1,2)
    for _ in range(100):
        mid=(a+b)/2
        if envelope(mid)>1:a=mid
        else:
            assert envelope(mid)<1
            b=mid
    assert max(a,lo)<min(b,hi)
    t=flint.arb.pi()/real(Q(5,3)).log()
    rows=[]
    for row in data['resonant_threshold_controls']['records']:
        sigma,m=Q(row['sigma']),row['m'];s=flint.acb(real(sigma),t)
        # Independently expand the dominant edge into encoded Dirichlet faces.
        edge=sum((w*(-s*flint.arb(3**(m-j)*5**j*2**(m+2)).log()).exp()
                  for j,w in enumerate(weights(m))),flint.acb(0))
        mod=flint.arb(2)**(-2*real(sigma))*envelope(sigma)**m
        assert edge.abs_lower()<=mod and edge.abs_upper()>=mod
        rest=C_integer(sigma)*envelope(sigma,15)**(m-4)
        assert rest<edge.abs_lower()/2
        if row['side']=='below':
            assert edge.abs_lower()-rest>1
        else:
            assert edge.abs_upper()+rest<C_integer(sigma)*envelope(sigma)**(m-4)
        assert (edge.abs_lower()-rest).overlaps(flint.arb(row['infinite_modulus_lower_ball']))
        rows.append({'side':row['side'],'m':m,'encoded_dominant_edge_ball':short(edge),'all_passed':True})
    return {'independent_threshold_lower':str(a),'independent_threshold_upper':str(b),
            'records':rows,'all_passed':True}


def audit_trap(data):
    source=data['unmasked_coefficientwise_limit_counterexample'];sigma=Q(1,2)
    t=flint.arb.pi()/real(Q(3,2)).log();s=flint.acb(real(sigma),t)
    # Antiphase gives an exact positive envelope, independently of complex
    # exponentiation of the production edge.
    a=flint.arb(2)**(-real(sigma))+flint.arb(3)**(-real(sigma))
    rows=[]
    for row in source['records']:
        m=row['m'];bound=C_integer(sigma)*envelope(sigma)**(m-4)
        lower=a**m-bound
        value=poly(s,256,m) if m in (8,16) else None
        assert lower>1 and 2**m>128
        if value is not None:
            assert value.abs_upper()<bound+omitted(sigma,256,m)
        rows.append({'m':m,'independent_unmasked_modulus_lower_ball':short(lower),'all_passed':True})
    return {'records':rows,'all_passed':True}


def audit_roots_and_zeros(data):
    roots=data['ordinary_root_auxiliary_controls'];s=flint.acb(2,'7.67')
    gamma=poly(s,384);L=s.zeta().log();assert flint.arb(2).zeta().log()<flint.arb.pi()
    for row in roots['records']:
        beta=Q(row['beta']);amp=beta**2 if row['family']=='input' else beta
        assert amp==Q(row['amplitude'])
        own=(real(beta)*L+real(amp)*gamma).exp()
        other=(real(beta)*L+real(amp)*encoded(s,192,4)).exp()
        err=(real(beta)*L.real+abs(real(amp))*(C_integer(Q(2))+omitted(Q(2),192)+omitted(Q(2),384))).exp()*abs(real(amp))*(omitted(Q(2),192)+omitted(Q(2),384))
        assert (own-other).abs_upper()<err
    assert ((L/2+gamma/4).exp()-(L/2+gamma/2).exp()).abs_lower()>0
    zero_rows=[]
    for row in data['whole_actual_zero_root_controls']['records']:
        sigma,m=Q(row['sigma_lower']),row['m'];assert sigma>Q(1,m)
        C=C_prime(sigma);bound=C*envelope(sigma)**(m-4)
        assert bound.overlaps(flint.arb(row['uniform_whole_disk_correction_modulus_bound_ball']))
        for f in row['root_factors']:
            beta=Q(f['beta']);amp=beta**2
            assert amp==Q(f['amplitude'])
            lower=(-real(amp)*bound).exp()
            assert lower>0 and lower.overlaps(flint.arb(f['modulus_lower_ball']))
            assert ((real(amp)*bound).exp()-1).overlaps(flint.arb(f['relative_factor_error_bound_ball']))
        assert row['reused_simple_zero'] and not row['new_zero_located']
        zero_rows.append({'disk_centre':row['disk_centre'],'m':m,
                          'independent_integer_disk_bound_ball':short(C_integer(sigma)*envelope(sigma)**(m-4)),
                          'all_passed':True})
    return {'ordinary_root_scalar_controls':5,'whole_zero_disk_order_groups':len(zero_rows),
            'whole_zero_disk_records':zero_rows,'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=768
    data=json.loads((DEST/'moment_analytic.json').read_text());assert data['all_passed']
    corr=audit_correction(data);uniform=audit_uniform(data);threshold=audit_threshold(data)
    trap=audit_trap(data);roots=audit_roots_and_zeros(data)
    checks={'independent_polynomial_correlations_and_changed_coefficient_rejection':corr['all_passed'],
            'native_prime_and_integer_uniform_height_majorants':uniform['all_passed'],
            'independent_threshold_bracket_and_encoded_resonant_edges':threshold['all_passed'],
            'coefficientwise_identity_limit_counterexample':trap['all_passed'],
            'ordinary_roots_and_whole_zero_disk_factors':roots['all_passed'],
            'counts_and_novelty_scope_honest':data['new_full_coefficient_origin_comparison_groups']==0 and not data['new_RH_estimate_proved'] and not data['historical_novelty_established']}
    out={'checks':checks,'correction_audit':corr,'uniform_audit':uniform,'threshold_audit':threshold,
         'coefficientwise_limit_audit':trap,'root_audit':roots,'production_imports':False,
         'shared_trusted_kernel':'FLINT/Arb and previously independent integer factor helpers',
         'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'moment_analytic_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent moment analytic audit:',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)
    assert out['all_passed']


if __name__=='__main__':
    main()
