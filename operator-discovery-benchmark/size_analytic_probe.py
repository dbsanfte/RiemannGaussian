#!/usr/bin/env python3
"""Actual-zeta tests of integer-height products and their paired root law.

The individual floor lift uses a Fejer sum of vertical shifts with a
proved infinite remainder. The paired lift uses zeta^beta times a
power-index resonance series. Its correction has a separate universal
Hausdorff-moment zero-free proof on Re(s)>0.
"""

from fractions import Fraction as Q
from pathlib import Path
import json
import time

import flint

from exact_arithmetic import factorization
from global_analytic_probe import ball, error_box


BASE=Path(__file__).resolve().parent


def zeta_power(s,beta,sigma):
    assert Q(sigma)>1 and bool(ball(sigma).zeta().log()<flint.arb.pi())
    return (ball(beta)*s.zeta().log()).exp()


def resonance(s,beta,base):
    x=(-s*flint.arb(base).log()).exp()
    assert bool(x.abs_upper()<1)
    if base==2:
        return (-ball(beta)*(1-x).log()).exp()
    numerator,denominator=[],[]
    for exponent in factorization(base).values():
        numerator += [Q(beta+j,exponent) for j in range(exponent)]
        denominator += [Q(j+1,exponent) for j in range(exponent)]
    denominator.remove(Q(1))  # The hypergeometric convention supplies 1/k!.
    return x.hypgeom([flint.acb(ball(a)) for a in numerator], [flint.acb(ball(b)) for b in denominator])


def fejer_error(sigma,base,degree):
    sigma=Q(sigma)
    assert sigma>2
    n=flint.arb(degree+1)
    first_moment=(1+2*n.log())/(4*n)
    # For integer m that is not a power of b, distance(log_b m,Z)
    # >=1/(sqrt(b)*m*log(b)). Resonant m have exactly zero Fejer error.
    nonres_mass=ball(sigma).zeta()-1/(1-flint.arb(base)**(-ball(sigma)))
    nonres_first=ball(sigma-1).zeta()-1/(1-flint.arb(base)**(-ball(sigma-1)))
    return first_moment*nonres_mass+flint.arb(base).sqrt()*flint.arb(base).log()*nonres_first/(2*n)


def fractional_moments(s,sigma,beta,base,degree=512):
    f=zeta_power(s,beta,sigma)
    r=resonance(s,beta,base)
    r2=resonance(s,2*beta,base)
    one,two=flint.acb(0),flint.acb(0)
    tau=2*flint.arb.pi()/flint.arb(base).log()
    for m in range(1,degree+1):
        weight=ball(Q(degree+1-m,(degree+1)*m))
        positive=zeta_power(s-flint.acb(0,m*tau),beta,sigma)
        negative=zeta_power(s+flint.acb(0,m*tau),beta,sigma)
        one+=weight*(positive-negative)
        two+=weight*(positive**2-negative**2)
    scale=flint.acb(0,2*flint.arb.pi())
    j=f/2-r/2-one/scale
    j2=f**2/2-r2/2-two/scale
    error=fejer_error(sigma,base,degree)
    lower=f**2-2*f*j+j2
    # Omitting the exact power-index correction is a meaningful bad model.
    incorrect=f**2-2*f*(j+r/2)+(j2+r2/2)
    return f,r,lower,error*(2*f.abs_upper()+1),incorrect


def arithmetic_series(coefficients,s,cutoff):
    return sum((ball(Q(coefficients[n]))*(-s*flint.arb(n).log()).exp() for n in range(1,cutoff+1)),flint.acb(0))


def actual_zeta_checks(source):
    table={(x['base'],x['beta']):x for x in source['paired_root_identity']['records']}
    cases=((2,Q(1,2),3,'77.17'),(2,Q(1,2),3,'-83.29'),
           (6,Q(1,4),4,'173.41'),(6,Q(1,4),4,'-181.67'),
           (12,Q(1,8),6,'293.53'),(12,Q(1,8),6,'-307.19'))
    results=[]
    for base,beta,sigma,height in cases:
        item=table[base,str(beta)]
        cutoff=item['cutoff']
        s=flint.acb(sigma,height)
        lower=arithmetic_series(item['lower_square_coefficients'],s,cutoff)
        paired=arithmetic_series(item['paired_coefficients'],s,cutoff)
        f,r,spectral,spectral_error,incorrect=fractional_moments(s,sigma,beta,base)
        tail=flint.arb(cutoff)**(1-sigma)/(sigma-1)
        perturbation=ball(Q(1,7))*(-s*flint.arb(2).log()).exp()
        comparisons=[]
        for name,actual,reference,allowed in (('paired_root_hypergeometric_correction',paired,f*r,tail),
                                             ('individual_floor_root_vertical_shift_sum',lower,spectral,tail+spectral_error)):
            difference=(actual-reference).abs_upper()
            corrupted=(actual+perturbation-reference).abs_lower()
            comparisons.append({'representation':name,'difference_upper_ball':str(difference),
                                'proved_infinite_tail_bound_ball':str(allowed),'within_bound':bool(difference<allowed),
                                'coefficient_2_error_lower_ball':str(corrupted),'coefficient_error_rejected':bool(corrupted>allowed)})
        omitted=(lower-incorrect).abs_lower()
        reject_resonance=bool(omitted>tail+spectral_error)
        result={'s':[str(sigma),height],'base':base,'beta':str(beta),'arithmetic_cutoff':cutoff,'Fejer_degree':512,
                'comparisons':comparisons,'incorrect_power_index_resonance_omission_lower_ball':str(omitted),
                'incorrect_resonance_omission_rejected':reject_resonance,
                'all_passed':all(x['within_bound'] and x['coefficient_error_rejected'] for x in comparisons) and reject_resonance}
        results.append(result)
        print(f"Actual zeta size products b={base}, beta={beta}, s={sigma}+{height}i: {result['all_passed']}",flush=True)
    return results


def actual_zero_control():
    height='14.13472514173469379046'
    c=flint.acb('0.5',height)
    radius,sigma=Q(1,10000),Q(4999,10000)
    region=flint.acb(flint.arb('0.5 +/- 0.0001'),flint.arb(height+' +/- 0.0001'))
    t=flint.acb_series([c,1],3).zeta()
    ranged=flint.acb_series([region,1],3).zeta()
    linear=t[1].abs_lower()*ball(radius)
    error=t[0].abs_upper()+ranged[2].abs_upper()*ball(radius)**2
    simple=bool(error<linear)
    basepoint=c+ball(radius)
    z_lower=((basepoint-1)*basepoint.zeta()).abs_lower()
    records=[]
    for base in (2,6,12):
        moment_lower=1/(1+flint.arb(base)**(-ball(sigma)))
        for beta in (Q(1,2),Q(1,4),Q(1,8),Q(1)):
            r=resonance(region,beta,base)
            phase=(flint.acb(0,2*flint.arb.pi()*ball(beta))).exp()-1
            # For noninteger beta use a rigorously positive LOWER jump.
            jump_lower=(2*(flint.arb.pi()*ball(beta)).sin()).abs_lower()
            obstruction=moment_lower*z_lower**ball(beta)*jump_lower
            expected_branch=beta.denominator!=1
            passed=bool(r.real>0) and (bool(obstruction>0) if expected_branch else bool(phase.contains(0)))
            records.append({'base':base,'beta':str(beta),'resonance_rectangle_ball':str(r),
                            'global_Hausdorff_moment_real_part_lower_ball':str(moment_lower),
                            'actual_pole_cancelled_root_monodromy_lower_ball':str(obstruction),
                            'exponential_root_phase_change_ball':str(phase),
                            'branch_obstruction_expected':expected_branch,'all_passed':passed})
    return {'disk_centre':['1/2',height],'radius':str(radius),'actual_simple_zeta_zero_certified':simple,
            'Rouche_linear_lower_ball':str(linear),'Rouche_error_upper_ball':str(error),
            'records':records,'all_passed':simple and all(x['all_passed'] for x in records),
            'scope':'Paired root combination only; continuation of individual floor/ceiling lifts is unestablished. Boundary zero is compatible with RH.'}


def main():
    started=time.monotonic()
    flint.ctx.prec=192
    source=json.loads((BASE/'size-results/size_carry_search.json').read_text())
    audit=json.loads((BASE/'size-results/size_carry_verification.json').read_text())
    assert audit['all_passed']
    points=actual_zeta_checks(source)
    control=actual_zero_control()
    result={'actual_zeta_ball_checks':points,'actual_critical_line_zero_control':control,
            'paired_correction_holomorphic_and_zero_free_domain':'Re(s)>0, all b>=2 and beta in [0,1]',
            'individual_series_absolute_convergence_domain':'Re(s)>1',
            'certified_vertical_shift_approximation_domain':'Re(s)>2, beta and 2beta in [0,1]',
            'individual_half_plane_continuation_proved':False,'new_RH_estimate_proved':False,
            'all_passed':all(x['all_passed'] for x in points) and control['all_passed'],
            'proof':'size_carry_proof.txt','elapsed_seconds':time.monotonic()-started}
    (BASE/'size-results/size_analytic_probe.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f"Size product actual-zeta audit: all={result['all_passed']}; elapsed={result['elapsed_seconds']:.2f}s")
    assert result['all_passed']


if __name__=='__main__':main()
