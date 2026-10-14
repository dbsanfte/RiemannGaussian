#!/usr/bin/env python3
"""Independent geometry, Euler-Maclaurin, and branch audit for size lifts.

No production module is imported. Derivatives use a finite arithmetic
Euler-Maclaurin formula, not the native zeta derivative. Fourier boxes
use binomial counts; log branches use certified argument unwrapping.
"""

from fractions import Fraction as Q
from itertools import product
from math import comb,factorial
from pathlib import Path
import json
import time

import flint
import mpmath as mp


BASE=Path(__file__).resolve().parent


def real(value):
    value=Q(value)
    return flint.arb(value.numerator)/value.denominator


def bernoulli(n):
    values=[Q(1)]
    for k in range(1,n+1):
        values.append(-sum(Q(comb(k+1,j))*values[j] for j in range(k))/Q(k+1))
    return values[n]


def derivative_from_arithmetic(s,cutoff=96,order=12,radius=Q(1,10)):
    t=flint.acb_series([s,1],2)
    value=sum(((-t*flint.arb(n).log()).exp() for n in range(1,cutoff)),flint.acb_series([0],2))
    log_n=flint.arb(cutoff).log()
    value+=((1-t)*log_n).exp()/(t-1)+(-t*log_n).exp()/2
    for k in range(1,order+1):
        rising=flint.acb_series([1],2)
        for j in range(2*k-1):rising*=t+j
        value+=real(bernoulli(2*k)/factorial(2*k))*rising*((1-t-2*k)*log_n).exp()
    sigma=s.real-real(radius)
    absolute=flint.arb(1)
    for j in range(2*order):absolute*= (s+j).abs_upper()+real(radius)
    error=real(abs(bernoulli(2*order))/factorial(2*order))*absolute
    error*=flint.arb(cutoff)**(1-sigma-2*order)/(sigma+2*order-1)
    return value[1],error/real(radius)


def independent_j1(s,base,cutoff=45):
    lb=flint.arb(base).log()
    y=((1-s)*lb).exp()
    x=(-s*lb).exp()
    tail_sum=y/((s-1)*(1-y))+x/(2*(1-x))
    for k in range(1,cutoff+1):
        a=flint.arb(base**k)
        tail_sum+=s.zeta(flint.acb(a))-a**(1-s)/(s-1)-a**(-s)/2
    derivative,derivative_error=derivative_from_arithmetic(s)
    error=s.abs_upper()/(2*s.real)*flint.arb(base)**(-(cutoff+1)*s.real)/(1-flint.arb(base)**(-s.real))
    return -derivative/lb-tail_sum,error+derivative_error/lb


def resonance_series(s,base,degree=64):
    exponents=(1,) if base==2 else (1,1) if base==6 else (2,1)
    x=(-s*flint.arb(base).log()).exp()
    power=flint.acb(1)
    value=flint.acb(1)
    coefficient=Q(1)
    for k in range(degree):
        for e in exponents:
            for j in range(e):coefficient*=Q(Q(1,2)+e*k+j,e*k+j+1)
        power*=x
        value+=real(coefficient)*power
    return value,x.abs_upper()**(degree+1)/(1-x.abs_upper())


def independent_log_zeta(sigma,height,anchor=5,steps=96):
    left=flint.arb(anchor)
    value=flint.acb(left,height).zeta().log()
    assert bool(flint.arb(anchor).zeta()-1<1)
    lows=[]
    for k in range(1,steps+1):
        right=flint.arb(anchor)+(sigma-anchor)*real(Q(k,steps))
        region=flint.acb(flint.arb((left+right)/2,(left-right).abs_upper()/2),height)
        lower=region.zeta().abs_lower()
        assert bool(lower>0),'Independent branch corridor includes zero'
        raw=flint.acb(right,height).zeta().log()
        # The interval certificate, rather than this nearest-integer guess,
        # validates the chosen continuous argument.
        winding=round(float((value.imag-raw.imag)/(2*flint.arb.pi())))
        lifted=raw+flint.acb(0,2*flint.arb.pi()*winding)
        assert bool((lifted.imag-value.imag).abs_upper()<flint.arb.pi())
        value,left=lifted,right
        lows.append(lower)
    return value,min(lows)


def exact_geometry_audit(source):
    grammar=source['volume_grammar']
    counts=[]
    for item in grammar['training_geometry']+grammar['fresh_geometry']:
        q,m=item['q'],item['mesh']
        counts.append(Q(comb(m-1,q),m**q)==Q(item['lower']) and Q(comb(m+q-1,q),m**q)==Q(item['upper']))
    fits=[]
    for family,shift,exponent,power,scale in product(('factorial','q_times_previous_factorial'),(-1,0,1,2),(-1,0,1),range(-2,3),(Q(1,4),Q(1,2),Q(1),Q(2),Q(4))):
        def model(q):
            v=factorial(q+shift) if family=='factorial' else q*factorial(q-1+shift)
            return scale*Q(v)**exponent*Q(q)**power
        if all(Q(x['lower'])<=model(x['q'])<=Q(x['upper']) for x in grammar['training_geometry']):
            failures=[x['q'] for x in grammar['fresh_geometry'] if not Q(x['lower'])<=model(x['q'])<=Q(x['upper'])]
            fits.append({'family':family,'shift':shift,'factorial_exponent':exponent,'q_power':power,'scale':str(scale),
                         'held_out_passed':not failures,'first_failed_q':failures[0] if failures else None})
    quadratures=[]
    for item in source['exact_box_resonant_geometry']:
        q,m=item['q'],item['m']
        integral=mp.quad(lambda t:t**(q-1)*mp.exp(-2j*mp.pi*m*t),(0,1))/mp.factorial(q-1)
        recorded=mp.mpc(item['value_real'],item['value_imag'])
        closed=mp.mpc(item['formula_real'],item['formula_imag'])
        quadratures.append(abs(recorded-integral)<mp.mpf(item['proved_box_error']) and abs(integral-closed)<mp.mpf('1e-35'))
    fresh=[]
    for q,m in product((1,2,3,7,13,24,40),(11,-17)):
        integral=mp.quad(lambda t:t**(q-1)*mp.exp(-2j*mp.pi*m*t),(0,1))/mp.factorial(q-1)
        w=1/(2j*mp.pi*m)
        polynomial=-sum(w**r/mp.factorial(q-r) for r in range(1,q))
        fresh.append(abs(integral-polynomial)<mp.mpf('1e-55') and (integral.imag*m>0 if q>=2 else abs(integral)<mp.mpf('1e-55')))
    return all(counts),fits==grammar['training_fits'],all(quadratures),all(fresh)


def singularity_audit(source):
    records=[]
    for item in source['artificial_singularity_checks']:
        base,m,k=item['base'],item['harmonic'],-item['epsilon_power_of_two']
        eps=flint.arb(2)**(-k)
        tau=2*flint.arb.pi()/flint.arb(base).log()
        s=flint.acb(1+eps,m*tau)
        z=s.zeta()
        j,tail=independent_j1(s,base)
        correction,correction_tail=resonance_series(s,base)
        corr_upper=correction.abs_upper()+correction_tail
        unresolved=2*eps*z.abs_upper().sqrt()*s.real.zeta().sqrt()
        x=(-s*flint.arb(base).log()).exp()
        centre=eps*(z+j)
        ceil_centre=-eps*(1/(1-x)+j)
        floor_error=unresolved+eps*tail
        ceil_error=unresolved+2*eps*z.abs_upper().sqrt()*corr_upper+eps*tail
        residue=flint.acb(0,1/(2*flint.arb.pi()*m))
        floor_good=bool((centre-residue).abs_upper()+floor_error<residue.abs_lower()/2)
        ceil_good=bool((ceil_centre+residue).abs_upper()+ceil_error<residue.abs_lower()/2)
        source_centre=flint.acb(*item['scaled_floor_centre_components'])
        source_hurwitz_tail=(s*(s+1)).abs_upper()/(12*(s.real+1))*flint.arb(base)**(-29*(s.real+1))/(1-flint.arb(base)**(-(s.real+1)))
        agrees=bool((centre-source_centre).abs_upper()<eps*(tail+source_hurwitz_tail))
        # Native zeta count replaced by a Cauchy bound on a larger disk.
        c=flint.acb(1,m*tau)
        outer=real(Q(1,100));inner=real(Q(1,30000))
        image=flint.acb(flint.arb(1,outer),flint.arb(m*tau,outer)).zeta()
        zeta_lower=c.zeta().abs_lower()-image.abs_upper()*inner/(outer-inner)
        zero_free=bool(zeta_lower>0)
        y=((1-s)*flint.arb(base).log()).exp()
        wrong=centre+eps*y/((s-1)*(1-y))
        rejected=bool((wrong-residue).abs_lower()>floor_error)
        records.append({'base':base,'harmonic':m,'epsilon_power_of_two':-k,'independent_Hurwitz_cutoff':45,
                        'arithmetic_zeta_derivative_cutoff':96,'Euler_Maclaurin_order':12,
                        'scaled_floor_centre_ball':str(centre),'floor_error_ball':str(floor_error),
                        'floor_residue_passed':floor_good,'ceiling_opposite_residue_passed':ceil_good,
                        'tight_J1_centres_agree_with_production':agrees,
                        'independent_Cauchy_zeta_zero_free_modulus_lower_ball':str(zeta_lower),
                        'actual_zeta_zero_free_neighbourhood_certified':zero_free,
                        'omitted_geometric_resonance_rejected':rejected,'all_passed':floor_good and ceil_good and agrees and zero_free and rejected})
    return records


def angular_audit(source):
    records=[]
    degree=40
    interval=Q(1,5)
    a=real(interval)/2
    ceiling=1/(degree*(flint.arb.pi()*real(interval)/2).sin()**2)
    for item in source['actual_zeta_log_angle_controls']:
        base,k=item['base'],-item['epsilon_power_of_two']
        eps=flint.arb(2)**(-k);sigma=1+eps
        tau=2*flint.arb.pi()/flint.arb(base).log()
        mass=sigma.zeta().log()
        moment_matches=[]
        wrong_branches=[]
        lower={orientation:(1-ceiling)*mass for orientation in ('floor','ceil')}
        reproduced={orientation:(1-1/(32*(flint.arb.pi()/8).sin()**2))*mass for orientation in ('floor','ceil')}
        for m in range(1,degree):
            value,corridor=independent_log_zeta(sigma,m*tau)
            angle=2*flint.arb.pi()*m*a
            c,s=angle.cos(),angle.sin()
            weight=2*(1-real(Q(m,degree)))
            lower['floor']+=weight*(c*value.real-s*value.imag)
            lower['ceil']+=weight*(c*value.real+s*value.imag)
            if m<=31:
                source_log=flint.acb(*item['modes'][m-1]['normalized_log_zeta_components'])
                moment_matches.append(bool((value-source_log).abs_upper()<real(Q(1,10**30))))
                wrong_branches.append(bool((value+flint.acb(0,2*flint.arb.pi())-source_log).abs_lower()>1))
                angle_original=flint.arb.pi()*m/4
                c0,s0=angle_original.cos(),angle_original.sin()
                weight_original=2*(1-real(Q(m,32)))
                reproduced['floor']+=weight_original*(c0*value.real-s0*value.imag)
                reproduced['ceil']+=weight_original*(c0*value.real+s0*value.imag)
        bounds=[]
        reproduced_ok=[]
        for orientation,total in lower.items():
            amount=total/degree
            bound=sum((amount**j/factorial(j) for j in range(5)),flint.arb(0)) if bool(amount>0) else flint.arb(1)
            original=next(x for x in item['mark_lower_bounds'] if x['orientation']==orientation)
            reproduced_ok.append(bool((reproduced[orientation]/32-flint.arb(original['mark_mass_interval_lower_ball'])).abs_upper()<real(Q(1,10**28))))
            bounds.append({'orientation':orientation,'mark_mass_interval_lower_ball':str(amount),'genuine_U_lower_ball':str(bound)})
        records.append({'base':base,'epsilon_power_of_two':-k,'independent_anchor':5,'independent_corridor_steps':96,
                        'independent_Fejer_degree':degree-1,'independent_mark_interval':str(interval),'independent_EXP_terms':4,
                        'source_normalized_log_branches_recomputed':all(moment_matches),'wrong_log_branch_rejected':all(wrong_branches),
                        'source_lower_mark_bounds_independently_recomputed':all(reproduced_ok),'independent_U_lower_bounds':bounds,
                        'all_passed':all(moment_matches) and all(wrong_branches) and all(reproduced_ok)})
        print(f'Independent angular certificate b={base}, epsilon=2^-{k}: {records[-1]["all_passed"]}',flush=True)
    return records


def main():
    started=time.monotonic()
    flint.ctx.prec=288
    mp.mp.dps=90
    source=json.loads((BASE/'size-results/size_resonance_probe.json').read_text())
    geometry=exact_geometry_audit(source)
    points=singularity_audit(source)
    angular=angular_audit(source)
    checks={'grid_box_counts_from_independent_binomial_formula':geometry[0],
            'all_factorial_grammar_decisions_recomputed':geometry[1],
            'numerical_Fourier_geometry_matches_independent_quadrature':geometry[2],
            'fresh_arity_and_harmonic_polynomial_laws_match_quadrature':geometry[3],
            'all_independent_infinite_lift_residue_enclosures_passed':all(x['floor_residue_passed'] and x['ceiling_opposite_residue_passed'] for x in points),
            'tight_J1_centres_agree_under_different_proved_tails':all(x['tight_J1_centres_agree_with_production'] for x in points),
            'all_spurious_sites_are_actual_zeta_zero_free_by_Cauchy_bound':all(x['actual_zeta_zero_free_neighbourhood_certified'] for x in points),
            'omitted_geometric_resonance_rejected_everywhere':all(x['omitted_geometric_resonance_rejected'] for x in points),
            'all_log_branch_and_lower_mark_certificates_recomputed':all(x['all_passed'] for x in angular)}
    result={'checks':checks,'artificial_singularity_checks':points,'actual_zeta_log_angle_controls':angular,
            'all_passed':all(checks.values()),'proof':'size_resonance_proof.txt','no_production_helper_imports':True,
            'shared_trusted_kernel':'Arb zeta/elementary interval arithmetic; independent finite EM derivative and branch assembly',
            'elapsed_seconds':time.monotonic()-started}
    (BASE/'size-results/size_resonance_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'Independent size-resonance audit: {sum(checks.values())}/{len(checks)}, elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__=='__main__':main()
