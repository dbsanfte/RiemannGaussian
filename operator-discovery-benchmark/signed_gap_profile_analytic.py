#!/usr/bin/env python3
"""Analytical attempts on frozen gap profiles and the anonymous minimum lead."""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import argparse,subprocess,sys
from stable_scale_search import BASE,read,write,sha,digest


def difference_certificate(terms):
    boundary={};difference={}
    for i,j,c in terms:
        c=Q(c)
        if i==0:boundary[j]=boundary.get(j,Q(0))+c
        for k in range(i):difference[k,j]=difference.get((k,j),Q(0))+c*comb(i,k)
    boundary={k:str(v) for k,v in boundary.items() if v};difference={str(k)+','+str(j):str(v) for (k,j),v in difference.items() if v};admitted=not boundary and difference=={'2,0':'1'}
    return {'boundary_coefficients':boundary,'forward_difference_coefficients':difference,'admitted':admitted,'global_binary_prefix_minimum_bound_proved':admitted,
        'proof_method':'boundary, symbolic forward difference and monotone prefix exchange','holds_for_all_integer_dimensions_and_masses':admitted,'prime_distribution_estimate':False}


def growth(p):
    s=p['exponent_schedule'];c=p['constant_law'];L=Q(p['log_power']);k=c['kind'];category='no_finite_power_bound_supplied';kap=None
    if k=='constant':category='power_bound';kap=Q(0)
    elif k=='denominator_power':category='power_bound';kap=Q(c['power'])
    elif k=='power':
        if s['kind']=='power':category='power_bound';kap=Q(c['power'])/Q(s['power'])
        else:category='subpolynomial_in_reciprocal_epsilon';kap=Q(0)
    elif k=='exponential' and s['kind']=='exponential':
        r,a=Q(c['power']),Q(s['power'])
        if r==a:category='power_bound';kap=Q(1)
        elif r<a:category='subpolynomial_in_reciprocal_epsilon';kap=Q(0)
    elif k=='exponential' and s['kind']=='factorial' and Q(c['power'])<=1:category='subpolynomial_in_reciprocal_epsilon';kap=Q(0)
    elif k=='factorial' and s['kind']=='factorial':category='power_bound';kap=Q(1)
    elif k=='free_per_level':category='unrestricted_existential_per_level_constants'
    alpha=None if kap is None else (kap+L+3)/2;upper=None if alpha is None else alpha.numerator//alpha.denominator
    return {'growth_category':category,'kappa_or_limiting_kappa':None if kap is None else str(kap),'log_power':str(L),
        'conditional_reciprocal_pole_power':None if alpha is None else str(alpha),'conditional_critical_zero_multiplicity_upper':upper,
        'reciprocal_pole_power_is_limit_allowing_subpolynomial_factors':True,
        'would_force_simple_critical_zeros_if_global_bound_proved':upper==1,'is_claim_about_actual_zero_multiplicities':False,
        'growing_constants_do_not_automatically_avoid_extra_zero_restrictions':True}


def main(d):
    spec=read(d/'protocol.json');queue=read(d/'proof_queue.json');seal=read(d/'seal.json');v=read(d/'verification.json');assert v['all_passed']
    for n,h in seal['files'].items():assert sha(d/n)==h
    lead=queue['minimum_lead'];minimum=difference_certificate(lead['terms']) if lead else {'admitted':False,'global_binary_prefix_minimum_bound_proved':False};attempts=[]
    for row in queue['queue']:
        p=row['exact_program'];attempts.append({'program_id':row['program_id'],'exact_program_sha256':digest(p),'exact_global_claim':row['global_claim'],
            'proof_status':'unresolved_all_scale_actual_signed_half_gap','missing_lemma':'actual signed Delta bound at every dyadic scale','conditional_constant_growth_consequences':growth(p),
            'formula_or_fitted_constants_changed':False,'global_actual_critical_signed_gap_proved':False,'RH_proved':False})
    result={'source_queue_sha256':sha(d/'proof_queue.json'),'source_final_sha256':sha(d/'final_evaluation.json'),'source_detector_verification_sha256':sha(d/'verification.json'),'selection_and_final_frozen_before_analytical_attempts':True,
        'minimum_lead':lead,'minimum_proof_certificate':minimum,'minimum_analytic_status':'global_combinatorial_bound_proved' if minimum['admitted'] else 'unresolved_detected_relation',
        'quantitative_divisor_tail_obstruction':{'conditional_on_minimum_certificate':True,'quadratic_upper':'D*J-P(J)','necessary_condition_if_PSD':'P(J)<=D*J','independent_of_Gram_weight':True,
            'no_tail_position_or_periodicity_assumption':True,'cofinal_critical_tail_omission_power_ceiling':'1/2','global_arithmetic_gap_proved':False},
        'candidate_attempts':attempts,'generic_calibration':{'D_coefficient':'16','epsilon':'1','log_power':'0','all_integer_scales':True,'global_half_gap_proved':True,'ordinary_energy_power':'3','RH_strength':False},
        'prior_positive_r_simplicity_scope_correction':'For epsilon=1/q and L=0, polynomial constant powers r<1 still force simple critical zeros if the all-scale family is proved; positive r only removed boundedness, not every extra simplicity consequence.',
        'all_scale_critical_signed_bound_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False};write(d/'analytical_review.json',result)
    subprocess.run([sys.executable,str(BASE/'check_signed_gap_profile_analytic.py'),'--run-dir',str(d)],cwd=BASE,check=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);main(p.parse_args().run_dir.resolve())
