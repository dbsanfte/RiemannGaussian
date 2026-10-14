#!/usr/bin/env python3
"""Infinite native fractional bridges and whole-disk zero visibility."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import argparse
import json
import time
import flint

from fractional_prime_probe import numerator, box, real

BASE=Path(__file__).resolve().parent
DEST=BASE/'fractional-prime-results'


@lru_cache(maxsize=None)
def log(n):return flint.arb(n).log()


def short(x):return x.str(28)


def derivative(s,k=1):return flint.acb_series([s,1],prec=k+1).zeta()[k]*(2 if k==2 else 1)


def log_tail(N,sigma):
    a=real(sigma)-1;return real(N)**(-a)*(log(N)/a+1/a**2)


def euler_derivative_bound(x):
    return flint.arb(2)**(-x)*(log(2)+2*log(2)/(x-1)+2/(x-1)**2)


def native_groups(source):
    coefficients=[flint.arb(x) for x in next(r for r in source['profiles'] if r['alpha']=='1/2')['L_coefficients']]
    rows=[]
    for sigma,t in ((4,'3.83'),(5,'-7.29'),(6,'10.73'),(4,'-14.17'),(5,'17.59'),(6,'-21.01')):
        s=flint.acb(sigma,t);N,certificate=numerator(s,Q(sigma));whole=N/s.zeta()
        partial=sum((c*(-s*log(n)).exp() for n,c in enumerate(coefficients) if n>=2),flint.acb(0))
        tail=log_tail(4096,Q(sigma));difference=(partial-whole).abs_upper()
        wrong=(partial+real(Q(1,11))*(-s*log(13)).exp()-whole).abs_lower()
        passed=bool(difference<tail) and bool(wrong>tail)
        rows.append({'s':[str(sigma),t],'coefficient_cutoff':4096,
                     'native_identity':'sum Lambda_(1/2)(n)n^-s=N_(1/2)(s)/zeta(s)',
                     'coefficient_origin':'complete divisor-recursion inversion of (log n)^(1/2), with no prime-indicator input',
                     'operator_component':'full unnormalized fractional arithmetic logarithm L_(1/2); not the whole normalized decoder B_(1/2)',
                     'native_value_real_ball':short(whole.real),'native_value_imag_ball':short(whole.imag),
                     'numerator_certificate':certificate,'difference_upper_ball':short(difference),
                     'integer_log_tail_ball':short(tail),'changed_coefficient_index':13,'coefficient_error':'1/11',
                     'wrong_difference_lower_ball':short(wrong),'all_passed':passed})
        print('Native fractional-log group',sigma,t,passed,flush=True)
    return rows


def derivative_bound(c,r):
    """Bound N' on the whole old zero disk via a real-u partition."""
    region=c+box(real(r));delta=Q(1,32);U=Q(8)
    low_region=region+flint.acb(flint.arb(real(delta*delta/2),real(delta*delta/2)))
    low=real(delta)*derivative(low_region,2).abs_upper()
    d0=derivative(region).abs_upper();mid=flint.arb(0);a=delta;cells=0
    while a<U:
        b=min(U,a*Q(9,8))
        x=Q(1,2)-r+a*a
        # Absolute Euler-series derivative bound is valid here for x>=2.
        # It avoids a wide native derivative box becoming nonfinite farther
        # right, without repeating already verified quadrature/corridors.
        if x>=2:other=euler_derivative_bound(real(x))
        else:
            shifted=region+flint.acb(flint.arb(real((a*a+b*b)/2),real((b*b-a*a)/2)))
            other=derivative(shifted).abs_upper()
        mid+=(d0+other)*real(1/a-1/b);a=b;cells+=1
    high=(d0+euler_derivative_bound(real(Q(1,2)-r+U*U)))/real(U)
    bound=(low+mid+high)/flint.arb.pi().sqrt()
    return bound,{'small_u_zeta_second_derivative_term_ball':short(low),
                  'middle_derivative_bound_ball':short(mid),'large_u_derivative_bound_ball':short(high),
                  'partition_cells':cells,'delta':str(delta),'U':str(U)}


def corridor(c,r,scale):
    """Cover a horizontal strip by adaptively refined native zero-free boxes."""
    start=Q(1,2)+2*r if scale==1 else Q(1)-2*r
    end=Q(3);height=c.imag*scale
    todo=[(start,end,-scale*r,scale*r)];accepted=[]
    while todo:
        a,b,y,z=todo.pop();rect=flint.acb(flint.arb(real((a+b)/2),real((b-a)/2)),height+flint.arb(real((y+z)/2),real((z-y)/2)))
        lower=rect.zeta().abs_lower()
        if lower>0:accepted.append((a,b,y,z,lower));continue
        assert max(b-a,z-y)>Q(1,2**28), (a,b,y,z,'corridor failed')
        if b-a>=z-y:
            m=(a+b)/2;todo.extend(((a,m,y,z),(m,b,y,z)))
        else:
            m=(y+z)/2;todo.extend(((a,b,y,m),(a,b,m,z)))
    assert sum((b-a)*(z-y) for a,b,y,z,_ in accepted)==(end-start)*2*scale*r
    return {'scale':scale,'start_real':str(start),'end_real':str(end),'imag_radius':str(scale*r),
            'boxes':[{'left':str(a),'right':str(b),'imag_offset_lower':str(y),'imag_offset_upper':str(z),'zeta_modulus_lower_ball':short(v)} for a,b,y,z,v in accepted],
            'minimum_zeta_modulus_lower_ball':short(min(v for *_,v in accepted)),
            'continuation_to_right_of_three_by_Euler_product':True,'all_passed':True}


def connection_disk(c,r):
    """A count-one outer disk fills the gap before the corridor begins."""
    radius=4*r;region=c+box(real(radius));second=derivative(region,2).abs_upper()
    linear=real(radius)*derivative(c).abs_lower()
    remainder=c.zeta().abs_upper()+real(radius*radius/2)*second
    margin=linear-remainder
    assert margin>0 and derivative(region).abs_lower()>0
    assert radius*radius>5*r*r
    return {'radius':str(radius),'radius_multiple_of_input_disk':4,
            'linear_boundary_modulus_lower_ball':short(linear),
            'constant_and_second_derivative_remainder_upper_ball':short(remainder),
            'Rouche_margin_lower_ball':short(margin),
            'whole_outer_disk_zeta_derivative_modulus_lower_ball':short(derivative(region).abs_lower()),
            'exactly_one_simple_zero_in_connection_disk':True,
            'connector_real_offsets':[-1,2],'connector_imag_offsets':[-1,1],
            'connector_rectangle_inside_outer_disk':True,
            'no_uncovered_gap_between_zero_disk_and_corridor':True,'all_passed':True}


def zeros(cached=None):
    rows=[]
    for path,key in (('size-results/size_analytic_probe.json','actual_critical_line_zero_control'),
                     ('cancellation-results/cancellation_analytic.json','fresh_actual_critical_line_zero_control')):
        old=json.loads((BASE/path).read_text())[key];assert old['all_passed']
        c=flint.acb(real(Q(1,2)),old['disk_centre'][1]);r=Q(old['radius'])
        previous=next((v for v in cached['records'] if v['disk_centre']==old['disk_centre'] and v['radius']==str(r)),None) if cached else None
        if previous:
            point=flint.acb(flint.arb(previous['native_numerator_real_ball']),flint.arb(previous['native_numerator_imag_ball']))
            assert point.is_finite()
            cert=previous['numerator_certificate']
        else:point,cert=numerator(c,Q(1,2))
        M,dc=derivative_bound(c,r)
        lower=point.abs_lower()-real(r)*M
        region=c+box(real(r));d=derivative(region)
        C=lower/d.abs_upper();branch=flint.arb.pi().sqrt()*C
        paths=previous['horizontal_zero_free_corridors'] if previous else [corridor(c,r,scale) for scale in (1,2)]
        assert all(v['all_passed'] for v in paths)
        connector=connection_disk(c,r)
        passed=bool(lower>0) and bool(d.abs_lower()>0) and bool(branch>0)
        rows.append({'disk_centre':old['disk_centre'],'radius':str(r),'reused_simple_zeta_zero':True,
                     'native_numerator_real_ball':short(point.real),'native_numerator_imag_ball':short(point.imag),
                     'numerator_certificate':cert,'whole_disk_numerator_derivative_upper_ball':short(M),
                     'derivative_certificate':dc,'whole_disk_numerator_modulus_lower_ball':short(lower),
                     'whole_disk_zeta_derivative_modulus_lower_ball':short(d.abs_lower()),
                     'fractional_log_simple_pole_residue_modulus_lower_ball':short(C),
                     'decoder_inverse_sqrt_branch_coefficient_modulus_lower_ball':short(branch),
                     'horizontal_zero_free_corridors':paths,
                     'local_connection_disk':connector,
                     'previous_point_quadrature_and_corridors_reused':bool(previous),
                     'decoder_B_half_has_nonzero_inverse_sqrt_branch':True,
                     'ordinary_normalized_unit_root_lift_preserves_zeta_zero_set':False,
                     'new_zeta_zero_located':False,'all_passed':passed})
        print('Whole-disk fractional numerator at old zero',old['disk_centre'][1],short(lower),passed,flush=True)
    return {'records':rows,'global_nonvanishing_of_fractional_numerator_at_every_zeta_zero_proved':False,
            'generic_zero_retention_is_conditional_on_nonzero_numerator':True,
            'all_passed':all(r['all_passed'] for r in rows)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-verified-components',action='store_true',help='Refine derivative bounds while retaining passed point and corridor components')
    args=parser.parse_args()
    start=time.monotonic();flint.ctx.prec=384;flint.ctx.cap=20
    source=json.loads((DEST/'fractional_prime_search.json').read_text())
    cached=json.loads((DEST/'fractional_prime_analytic.json').read_text()) if args.reuse_verified_components else None
    groups=cached['actual_zeta_ball_checks'] if cached else native_groups(source)
    assert all(v['all_passed'] for v in groups)
    control=zeros(cached['fractional_numerator_and_decoder_actual_zero_controls'] if cached else None)
    out={'actual_zeta_ball_checks':groups,'fractional_numerator_and_decoder_actual_zero_controls':control,
         'new_full_coefficient_origin_comparison_groups':6,
         'full_normalized_B_decoder_native_value_compared':False,
         'analytic_normalized_decoder_definition':'B_(1/2)(s)=sum mu(k)/k * R_(1/2)(k*s), R_(1/2)(s)=1/sqrt(pi) integral_0^infty t^-1/2 N_(1/2)(s+t)/zeta(s+t) dt',
         'new_uniform_prime_distribution_estimate_proved':False,'new_RH_estimate_proved':False,
         'historical_novelty_established':False,
         'all_passed':all(r['all_passed'] for r in groups) and control['all_passed'],'seconds':time.monotonic()-start}
    (DEST/'fractional_prime_analytic.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Fractional analytic controls',out['all_passed'],'seconds',out['seconds'],flush=True)
    assert out['all_passed']


if __name__=='__main__':main()
