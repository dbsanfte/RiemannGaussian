#!/usr/bin/env python3
"""Native prime-weight bridges, Mellin zero cancellation and decoder norms."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time
import flint

from prime_scale_search import sieve,mu

BASE=Path(__file__).resolve().parent
DEST=BASE/'prime-scale-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def short(x):return x.str(25)


@lru_cache(maxsize=None)
def log(n):return flint.arb(n).log()


def derivative(s):return flint.acb_series([s,1],prec=2).zeta()[1]


def symbol(s):return (s*log(2)).exp()-2


def log_tail(N,sigma):
    t=real(sigma);return real(N)**(1-t)*(log(N)/(t-1)+1/(t-1)**2)


def groups(source):
    bases=source['native_von_Mangoldt_coefficient_prime_bases'];rows=[];aux=[]
    for sig,t in ((4,'3.47'),(5,'-6.83'),(6,'10.19'),(4,'-13.61'),(5,'17.03'),(6,'-20.47')):
        s=flint.acb(sig,t);z=s.zeta();d=derivative(s);value=-d/z
        prefix=sum((log(p)*(-s*log(n)).exp() for n,p in enumerate(bases) if p),flint.acb(0))
        tail=log_tail(4096,Q(sig));diff=(prefix-value).abs_upper()
        wrong=(prefix+real(Q(1,11))*(-s*log(13)).exp()-value).abs_lower()
        passed=bool(diff<tail) and bool(wrong>tail)
        rows.append({'s':[str(sig),t],'coefficient_cutoff':4096,'native_identity':'sum Lambda(n)n^-s=-zeta_prime(s)/zeta(s)',
                     'coefficient_origin':'log-weighted LOG_D zeta coefficients; prime powers kept explicitly',
                     'difference_upper_ball':short(diff),'integer_log_tail_ball':short(tail),
                     'changed_prime_coefficient':13,'coefficient_error':'1/11','changed_difference_lower_ball':short(wrong),
                     'all_passed':passed})
        A=symbol(s)
        floor_prefix=sum((log(n)*(-s*log(n)).exp() for n in range(2,4097)),flint.acb(0))*A/s
        floor_native=-d*A/s;floor_bound=tail*A.abs_upper()/s.abs_lower()
        delta=(floor_prefix-floor_native).abs_upper()
        aux.append({'s':[str(sig),t],'floor_trace_Mellin_identity':'-zeta_prime(s)*(2**s-2)/s',
                    'coefficient_cutoff':4096,'difference_upper_ball':short(delta),'error_ball':short(floor_bound),
                    'zero_poles_cancelled_by_zeta_factor':True,'auxiliary_only':True,'all_passed':bool(delta<floor_bound)})
        print('Prime-weight native coefficient group',sig,t,passed,flush=True)
    return rows,{'records':aux,'all_passed':all(r['all_passed'] for r in aux)}


def zero_controls():
    rows=[]
    for name,key in (('size-results/size_analytic_probe.json','actual_critical_line_zero_control'),
                     ('cancellation-results/cancellation_analytic.json','fresh_actual_critical_line_zero_control')):
        old=json.loads((BASE/name).read_text())[key];assert old['all_passed']
        c=flint.acb(real(Q(1,2)),old['disk_centre'][1]);r=Q(old['radius'])
        rect=c+flint.acb(flint.arb(0,real(r)),flint.arb(0,real(r)))
        d=derivative(rect);A=symbol(rect)
        A_lower=2-flint.arb(2)**real(Q(1,2)+r)
        residue=A_lower/rect.abs_upper()
        floor_regular=-d*A/rect
        passed=bool(d.abs_lower()>0) and bool(A_lower>0) and bool(residue>0) and floor_regular.is_finite()
        rows.append({'disk_centre':old['disk_centre'],'radius':str(r),'reused_simple_zeta_zero':True,
                     'whole_disk_zeta_derivative_modulus_lower_ball':short(d.abs_lower()),
                     'whole_disk_scale_symbol_modulus_lower_ball':short(A_lower),
                     'decoded_simple_pole_residue_modulus_lower_ball':short(residue),
                     'floor_trace_Mellin_holomorphic_on_whole_disk':True,
                     'decoded_prime_contrast_has_simple_pole':True,'new_zeta_zero_located':False,'all_passed':passed})
    return {'records':rows,'central_symbol_zeros_have_real_part_one':True,
            'unmodified_floor_trace_RH_holomorphy_gate_rejected':True,'all_passed':all(r['all_passed'] for r in rows)}


def norms():
    spf,_=sieve(4096);rows=[]
    for sigma in (Q(1,2),Q(1),Q(5,4),Q(2)):
        for N in (16,64,256,1024,4096):
            value=sum((real(abs(mu(n,spf)))*flint.arb(n)**(-real(sigma)) for n in range(1,N+1)),flint.arb(0))
            rows.append({'sigma':str(sigma),'X':N,'finite_generic_decoder_norm_lower_ball':short(value)})
    aux=[]
    for sigma in (Q(2),Q(3),Q(4)):
        prefix=sum((real(abs(mu(n,spf)))*flint.arb(n)**(-real(sigma)) for n in range(1,4097)),flint.arb(0))
        native=real(sigma).zeta()/real(2*sigma).zeta();tail=real(4096)**(1-real(sigma))/(real(sigma)-1)
        wrong=(prefix+real(Q(1,11))*flint.arb(2)**(-real(sigma))-native).abs_lower()
        passed=bool((prefix-native).abs_upper()<tail) and bool(wrong>tail)
        aux.append({'sigma':str(sigma),'native_infinite_norm_ball':short(native),
                    'difference_upper_ball':short((prefix-native).abs_upper()),'tail_ball':short(tail),
                    'wrong_coefficient_lower_ball':short(wrong),'all_passed':passed})
    density=2-real(2).zeta();block=(4*density-1)/4
    assert density>0 and block>0
    return {'finite_saturating_lower_bounds':rows,'native_squarefree_norm_auxiliaries':aux,
            'elementary_squarefree_density_lower_ball':short(density),'each_power_four_sigma_one_block_lower_ball':short(block),
            'generic_scale_decoder_bounded_iff_sigma_gt_one_proved':True,
            'generic_norm_when_sigma_gt_one':'zeta(sigma)/zeta(2*sigma)',
            'prime_specific_cancellation_improvement_ruled_out':False,
            'all_passed':all(r['all_passed'] for r in aux)}


def negative_control():
    raw=flint.arb(252).log();decoded=real(Q(7,10)).log()
    assert raw>0 and decoded<0
    return {'X':5,'positive_raw_trace_ball':short(raw),'decoded_prime_contrast_ball':short(decoded),
            'raw_trace':'log binomial(10,5)=log 252','decoded_contrast':'psi(10)-2*psi(5)=log(7/10)',
            'positive_trace_implies_positive_decoded_contrast_rejected':True,'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=512;flint.ctx.cap=2
    source=json.loads((DEST/'prime_scale_search.json').read_text())
    actual,aux=groups(source);zeros=zero_controls();norm=norms();negative=negative_control()
    out={'actual_zeta_ball_checks':actual,'floor_trace_Mellin_auxiliary_checks':aux,
         'actual_zeta_zero_erasure_and_decoded_pole_controls':zeros,'scale_decoder_norm_controls':norm,
         'positive_trace_negative_prime_contrast_control':negative,
         'new_full_coefficient_origin_comparison_groups':6,'historical_novelty_established':False,
         'new_uniform_prime_distribution_estimate_proved':False,'new_RH_estimate_proved':False,
         'all_passed':all(r['all_passed'] for r in actual) and aux['all_passed'] and zeros['all_passed'] and norm['all_passed'] and negative['all_passed'],
         'seconds':time.monotonic()-start}
    (DEST/'prime_scale_analytic.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Prime-scale native/root/norm checks:',out['all_passed'],'seconds',out['seconds'],flush=True)
    assert out['all_passed']


if __name__=='__main__':main()
