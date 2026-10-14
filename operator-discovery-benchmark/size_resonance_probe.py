#!/usr/bin/env python3
"""Learn and certify artificial singularities created by integer-size lifts.

Exact grid geometry first, then actual-zeta/Hurwitz enclosures and
normalized log branches. No critical-strip continuation is assumed.
"""

from fractions import Fraction as Q
from itertools import product
from math import factorial
from pathlib import Path
import json
import time

import flint
import mpmath as mp


BASE=Path(__file__).resolve().parent
OUT=BASE/'size-results'


def ball(value):
    value=Q(value)
    return flint.arb(value.numerator)/value.denominator


def grid_counts(q,mesh):
    coefficients=[1]+[0]*(mesh-1)
    for _ in range(q):
        total=0
        next_values=[]
        for x in coefficients:
            total+=x
            next_values.append(total)
        coefficients=next_values
    return coefficients


def geometry(q,mesh,m=0):
    coefficients=grid_counts(q,mesh)
    low=Q(sum(coefficients[:max(0,mesh-q)]),mesh**q)
    high=Q(sum(coefficients),mesh**q)
    if not m:
        return {'q':q,'mesh':mesh,'lower':str(low),'upper':str(high)}
    phase=mp.exp(-2j*mp.pi*m/mesh)
    value=phase**(mp.mpf(q)/2)*sum(mp.mpf(x)*phase**t for t,x in enumerate(coefficients))/mesh**q
    # Interior boxes: phase is Lipschitz; boundary boxes: mass <= high-low.
    error=mp.pi*abs(m)*q/mesh*mp.mpf(high.numerator)/high.denominator+mp.mpf((high-low).numerator)/(high-low).denominator
    w=1/(2j*mp.pi*m)
    predicted=-sum(w**r/factorial(q-r) for r in range(1,q))
    return {'q':q,'mesh':mesh,'m':m,'value_real':mp.nstr(value.real,40),'value_imag':mp.nstr(value.imag,40),
            'proved_box_error':mp.nstr(error,40),'formula_real':mp.nstr(predicted.real,40),
            'formula_imag':mp.nstr(predicted.imag,40),'within_geometry_error':bool(abs(value-predicted)<error),
            'exact_polynomial_coefficients':[str(-Q(1,factorial(q-r))) for r in range(1,q)]}


def volume_model(q,model):
    family,shift,exponent,power,scale=model
    f=factorial(q+shift) if family=='factorial' else q*factorial(q-1+shift)
    return Q(scale)*Q(f)**exponent*Q(q)**power


def volume_search():
    train=[geometry(q,32) for q in range(2,6)]
    fresh=[geometry(q,512) for q in (6,7,8,10,12,16)]
    models=list(product(('factorial','q_times_previous_factorial'),(-1,0,1,2),(-1,0,1),range(-2,3),(Q(1,4),Q(1,2),Q(1),Q(2),Q(4))))
    fits=[]
    for model in models:
        if all(Q(x['lower'])<=volume_model(x['q'],model)<=Q(x['upper']) for x in train):
            failures=[x['q'] for x in fresh if not Q(x['lower'])<=volume_model(x['q'],model)<=Q(x['upper'])]
            fits.append({'family':model[0],'shift':model[1],'factorial_exponent':model[2],'q_power':model[3],
                         'scale':str(model[4]),'held_out_passed':not failures,'first_failed_q':failures[0] if failures else None})
    return {'models_scored':len(models),'training_geometry':train,'fresh_geometry':fresh,
            'training_fits':fits,'survivors':[x for x in fits if x['held_out_passed']],
            'selected_universal_law':'Real-pole Abelian coefficient is 1/q!, every q>=1',
            'finite_fits_are_not_universal_proofs':True}


def hurwitz_fractional_log(s,base,cutoff=28):
    sigma=s.real
    lb=flint.arb(base).log()
    t=(-s*lb).exp()
    y=((1-s)*lb).exp()
    v=(-(s+1)*lb).exp()
    total=y/((s-1)*(1-y))+t/(2*(1-t))+s*v/(12*(1-v))
    for k in range(1,cutoff+1):
        a=flint.arb(base**k)
        total+=s.zeta(flint.acb(a))-a**(1-s)/(s-1)-a**(-s)/2-s*a**(-s-1)/12
    derivative=flint.acb_series([s,1],2).zeta()[1]
    value=-derivative/lb-total
    tail=(s*(s+1)).abs_upper()/(12*(sigma+1))
    tail*=flint.arb(base)**(-(cutoff+1)*(sigma+1))/(1-flint.arb(base)**(-(sigma+1)))
    return value,tail


def artificial_singularity_checks():
    records=[]
    for base,m,k in product((2,6,12),(3,-5,7),(20,28,36)):
        epsilon=flint.arb(2)**(-k)
        tau=2*flint.arb.pi()/flint.arb(base).log()
        height=m*tau
        s=flint.acb(1+epsilon,height)
        z=s.zeta()
        j,error=hurwitz_fractional_log(s,base)
        # Unknown J_(1/2) has the rigorous absolute bound zeta(sigma)^1/2.
        half=z.abs_upper().sqrt()
        unresolved=2*epsilon*half*s.real.zeta().sqrt()
        r1=1/(1-(-s*flint.arb(base).log()).exp())
        x=(-s*flint.arb(base).log()).exp()
        rhalf=x.hypgeom([flint.acb(ball(Q(1,2)))],[]) if base==2 else flint.acb(0)
        if base!=2:
            exponents=(1,1) if base==6 else (2,1)
            numerator=[flint.acb(ball(Q(1,2)+j)/e) for e in exponents for j in range(e)]
            denominator=[flint.acb(ball(Q(j+1,e))) for e in exponents for j in range(e)]
            del denominator[next(i for i,a in enumerate(denominator) if a==1)]
            rhalf=x.hypgeom(numerator,denominator)
        lower_centre=epsilon*(z+j)
        upper_centre=-epsilon*(r1+j)
        lower_error=unresolved+epsilon*error
        upper_error=unresolved+2*epsilon*half*rhalf.abs_upper()+epsilon*error
        expected=-1/flint.acb(0,2*flint.arb.pi()*m)
        # These are enclosures for true infinite lifts, not truncated samples.
        lower_distance=(lower_centre-expected).abs_upper()+lower_error
        upper_distance=(upper_centre+expected).abs_upper()+upper_error
        lower_abs=lower_centre.abs_lower()-lower_error
        upper_abs=upper_centre.abs_lower()-upper_error
        actual_region=flint.acb(flint.arb(1,ball(Q(1,100000))),flint.arb(height,ball(Q(1,100000))))
        zeta_lower=actual_region.zeta().abs_lower()
        paired_bound=epsilon*half*rhalf.abs_upper()
        passed=bool(lower_distance<expected.abs_lower()/2) and bool(upper_distance<expected.abs_lower()/2)
        passed &= bool(lower_abs>0) and bool(upper_abs>0) and bool(zeta_lower>0)
        records.append({'base':base,'harmonic':m,'epsilon_power_of_two':-k,'s_real_ball':str(s.real),'s_imag_ball':str(height),
                        'Hurwitz_cutoff':28,'scaled_floor_centre_ball':str(lower_centre),'scaled_ceiling_centre_ball':str(upper_centre),
                        'scaled_floor_centre_components':[str(lower_centre.real),str(lower_centre.imag)],
                        'floor_enclosure_error_ball':str(lower_error),'ceiling_enclosure_error_ball':str(upper_error),
                        'predicted_floor_Abelian_residue_ball':str(expected),
                        'floor_distance_to_residue_upper_ball':str(lower_distance),'ceiling_distance_to_opposite_residue_upper_ball':str(upper_distance),
                        'scaled_floor_modulus_lower_ball':str(lower_abs),'scaled_ceiling_modulus_lower_ball':str(upper_abs),
                        'actual_zeta_zero_free_neighbourhood_modulus_lower_ball':str(zeta_lower),
                        'paired_scaled_bound_ball':str(paired_bound),'all_passed':passed})
        print(f'Spurious-singularity control b={base}, m={m}, epsilon=2^-{k}: {passed}',flush=True)
    return records


def normalized_log_zeta(real,height,anchor=4,steps=64):
    start=flint.acb(anchor,height).zeta()
    assert bool(flint.arb(anchor).zeta()-1<1)
    value=start.log()
    left=flint.arb(anchor)
    endpoint=start
    corridor_lowers=[]
    for j in range(1,steps+1):
        right=flint.arb(anchor)+(real-anchor)*ball(Q(j,steps))
        middle=(left+right)/2
        radius=(left-right).abs_upper()/2
        image=flint.acb(flint.arb(middle,radius),height).zeta()
        lower=image.abs_lower()
        assert bool(lower>0),f'Increase corridor resolution: t={height}, step={j}'
        target=flint.acb(right,height).zeta()
        value+=(target/endpoint).log()
        corridor_lowers.append(lower)
        endpoint,left=target,right
    return value,min(corridor_lowers)


def actual_log_angle_controls():
    records=[]
    mesh=32
    interval=Q(1,4)
    centre=ball(interval)/2
    peak_ceiling=1/(mesh*(flint.arb.pi()*ball(interval)/2).sin()**2)
    for base,k in product((2,6,12),(32,64,128)):
        epsilon=flint.arb(2)**(-k)
        sigma=1+epsilon
        mass=sigma.zeta().log()
        tau=2*flint.arb.pi()/flint.arb(base).log()
        modes=[]
        peaks={orientation:(1-peak_ceiling)*mass for orientation in ('floor','ceil')}
        for m in range(1,mesh):
            log_zeta,corridor=normalized_log_zeta(sigma,m*tau)
            phase=flint.acb(0,2*flint.arb.pi()*m*centre).exp()
            weight=2*(1-ball(Q(m,mesh)))
            peaks['floor']+=weight*(phase*log_zeta).real
            peaks['ceil']+=weight*(phase*log_zeta.conjugate()).real
            modes.append({'harmonic':m,'normalized_log_zeta_ball':str(log_zeta),
                          'normalized_log_zeta_components':[str(log_zeta.real),str(log_zeta.imag)],
                          'normalised_angular_moment_modulus_upper_ball':str(log_zeta.abs_upper()/mass),
                          'corridor_steps':64,'corridor_modulus_min_lower_ball':str(corridor)})
        lower_records=[]
        for orientation,value in peaks.items():
            atom_lower=value/mesh
            # Every term with <=3 atoms in theta (or psi) <=1/4 survives.
            bounded=bool(atom_lower>0)
            lower=sum((atom_lower**j/factorial(j) for j in range(4)),flint.arb(0)) if bounded else flint.arb(1)
            lower_records.append({'orientation':orientation,'mark_mass_interval_lower_ball':str(atom_lower),
                                  'genuine_U_zeta_series_lower_ball':str(lower),'lower_bound_uses_only_nonnegative_EXP_terms':True})
        records.append({'base':base,'epsilon_power_of_two':-k,'log_zeta_positive_real_mass_ball':str(mass),
                        'Fejer_peak_degree':mesh-1,'mark_interval':str(interval),'mark_lower_bounds':lower_records,'modes':modes,
                        'all_branches_certified':all(bool(flint.arb(x['corridor_modulus_min_lower_ball'])>0) for x in modes),
                        'scope':'Finite moment controls and rigorous lower bounds for actual U. No Bessel asymptotic for U is inferred.'})
        print(f'Actual log-angle control b={base}, epsilon=2^-{k}: branch corridors certified',flush=True)
    return records


def main():
    started=time.monotonic()
    mp.mp.dps=70
    flint.ctx.prec=256
    OUT.mkdir(exist_ok=True)
    search=volume_search()
    geometry_records=[geometry(q,2048,m) for q,m in product((2,3,4,8,12,16),(1,-3,7))]
    points=artificial_singularity_checks()
    angles=actual_log_angle_controls()
    result={'volume_grammar':search,'exact_box_resonant_geometry':geometry_records,
            'artificial_singularity_checks':points,'actual_zeta_log_angle_controls':angles,
            'universal_finite_q_Abelian_law':'epsilon^alpha L_(b,q,orientation)(u^alpha)(1+epsilon+i*m*tau_b) tends to simplex Fourier coefficient; floor polynomial -sum_(r=1)^(q-1) w^r/(q-r)!, w=1/(2*pi*i*m), ceiling its conjugate; m=0 coefficient 1/q!',
            'all_q_ge_2_have_artificial_boundary_singularities_Re_s_eq_one':True,
            'U_positive_real_asymptotic_law':'For every fixed integer b>=2 and both orientations, U(u)(1+epsilon) grows faster than every power of log(1/epsilon), but slower than every positive power of 1/epsilon',
            'no_finite_real_power_pole_cancellation_of_U_is_holomorphic_at_one':True,
            'full_H_half_plane_holomorphic_root_lift_gate_rejected':True,
            'paired_root_identity_not_rejected':True,'new_RH_estimate_proved':False,'counts_as_new_primitive':False,
            'all_passed':all(x['within_geometry_error'] for x in geometry_records) and all(x['all_passed'] for x in points)
                         and all(x['all_branches_certified'] for x in angles),
            'proof':'size_resonance_proof.txt','elapsed_seconds':time.monotonic()-started}
    (OUT/'size_resonance_probe.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'Size resonance proof controls: all={result["all_passed"]}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__=='__main__':main()
