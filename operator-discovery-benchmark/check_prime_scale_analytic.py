#!/usr/bin/env python3
"""Changed prime coefficients/cutoffs, zero residues and exact norm controls."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time
import flint

from check_gap import factors

BASE=Path(__file__).resolve().parent
DEST=BASE/'prime-scale-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def short(x):return x.str(25)


@lru_cache(maxsize=None)
def log(n):return flint.arb(n).log()


def mu(n):
    fs=factors(n);return 0 if any(v>1 for v in fs.values()) else (-1)**len(fs)


def derivative(s):return flint.acb_series([s,1],prec=2).zeta()[1]


def prefix(s,limit):
    out=flint.acb(0)
    for n in range(2,limit+1):
        fs=factors(n)
        if len(fs)==1:out+=log(next(iter(fs)))*(-s*log(n)).exp()
    return out


def tail(limit,sigma):
    a=real(sigma)-1
    return (-a*log(limit)).exp()*(log(limit)/a+1/a**2)


def native(source):
    rows=[];aux=[];N=6144
    for row in source['actual_zeta_ball_checks']:
        sig=Q(row['s'][0]);s=flint.acb(real(sig),row['s'][1]);d=derivative(s);whole=-d/s.zeta()
        partial=prefix(s,N);bound=tail(N,sig);diff=(partial-whole).abs_upper()
        wrong=(partial+real(Q(1,17))*(-s*log(17)).exp()-whole).abs_lower()
        assert diff<bound and wrong>bound
        rows.append({'s':row['s'],'changed_cutoff':N,'changed_wrong_prime_index':17,'smaller_coefficient_error':'1/17',
                     'difference_upper_ball':short(diff),'tail_ball':short(bound),'wrong_difference_lower_ball':short(wrong),'all_passed':True})
        A=(s*log(2)).exp()-2
        cp=sum((log(n)*(-s*log(n)).exp() for n in range(2,N+1)),flint.acb(0))*A/s
        allowed=bound*A.abs_upper()/s.abs_lower();delta=(cp+d*A/s).abs_upper()
        assert delta<allowed
        aux.append({'s':row['s'],'cutoff':N,'difference_upper_ball':short(delta),'allowed_ball':short(allowed),'all_passed':True})
    return {'records':rows,'all_passed':True},{'records':aux,'all_passed':True}


def zeros(source):
    rows=[]
    for row in source['actual_zeta_zero_erasure_and_decoded_pole_controls']['records']:
        r=Q(row['radius']);c=flint.acb(real(Q(1,2)),row['disk_centre'][1])
        region=c+flint.acb(flint.arb(0,real(r)),flint.arb(0,real(r)))
        d=derivative(region);A=(region*log(2)).exp()-2
        direct_symbol_lower=A.abs_lower();theoretical=2-flint.arb(2)**real(Q(1,2)+r)
        assert d.abs_lower()>0 and theoretical>0 and direct_symbol_lower>0
        residue=theoretical/region.abs_upper()
        assert residue>0 and residue.overlaps(flint.arb(row['decoded_simple_pole_residue_modulus_lower_ball']))
        # Multiplication by zeta cancels the pole identically, not just at a
        # floating-point approximation to the zero. Native derivative is finite.
        assert (-d*A/region).is_finite()
        rows.append({'disk_centre':row['disk_centre'],'direct_native_symbol_modulus_lower_ball':short(direct_symbol_lower),
                     'decoded_pole_residue_lower_ball':short(residue),'new_zeta_zero_located':False,'all_passed':True})
    return {'records':rows,'all_passed':True}


def norms(source):
    rows=[]
    for row in source['scale_decoder_norm_controls']['native_squarefree_norm_auxiliaries']:
        sig=Q(row['sigma']);N=6144
        partial=sum((real(mu(n)**2)*flint.arb(n)**(-real(sig)) for n in range(1,N+1)),flint.arb(0))
        bound=real(N)**(1-real(sig))/(real(sig)-1);native=real(sig).zeta()/real(2*sig).zeta()
        wrong=(partial+real(Q(1,17))*flint.arb(2)**(-real(sig))-native).abs_lower()
        assert (partial-native).abs_upper()<bound and wrong>bound
        assert native.overlaps(flint.arb(row['native_infinite_norm_ball']))
        rows.append({'sigma':str(sig),'changed_cutoff':N,'native_infinite_norm_ball':short(native),
                     'difference_upper_ball':short((partial-native).abs_upper()),'bound_ball':short(bound),'all_passed':True})
    density=2-real(2).zeta();block=density-real(Q(1,4))
    assert block>0 and block.overlaps(flint.arb(source['scale_decoder_norm_controls']['each_power_four_sigma_one_block_lower_ball']))
    for row in source['scale_decoder_norm_controls']['finite_saturating_lower_bounds']:
        sig,N=Q(row['sigma']),row['X']
        val=sum((real(mu(n)**2)*(-real(sig)*log(n)).exp() for n in range(1,N+1)),flint.arb(0))
        assert val.overlaps(flint.arb(row['finite_generic_decoder_norm_lower_ball']))
    return {'native_auxiliary_groups':rows,'elementary_block_lower_ball':short(block),'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=640;flint.ctx.cap=2
    source=json.loads((DEST/'prime_scale_analytic.json').read_text());assert source['all_passed']
    n,aux=native(source);z=zeros(source);norm=norms(source)
    negative=real(Q(7,10)).log();assert negative<0 and flint.arb(252).log()>0
    assert negative.overlaps(flint.arb(source['positive_trace_negative_prime_contrast_control']['decoded_prime_contrast_ball']))
    assert not source['historical_novelty_established'] and not source['new_uniform_prime_distribution_estimate_proved'] and not source['new_RH_estimate_proved']
    checks={'changed_complete_prime_weight_native_zeta_groups':n['all_passed'],
            'changed_floor_trace_Mellin_coefficient_auxiliaries':aux['all_passed'],
            'actual_zero_poles_erased_in_trace_restored_by_decoder':z['all_passed'],
            'squarefree_decoder_norm_native_and_saturating_bounds':norm['all_passed'],
            'positive_trace_negative_prime_contrast':True,
            'historical_novelty_all_scale_new_bound_and_RH_scope_honest':True}
    out={'checks':checks,'native_audit':n,'floor_trace_auxiliary_audit':aux,'zero_erasure_audit':z,'decoder_norm_audit':norm,
         'production_imports':False,'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'prime_scale_analytic_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent prime-scale analytic audit:',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
