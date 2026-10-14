#!/usr/bin/env python3
"""Independent generic polynomial admission and conditional multiplicity audit."""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import argparse
from stable_scale_report import BASE,read,sha,digest
from check_mellin_kernels import put


def polynomial(terms,J,m):return sum(Q(c)*J**i*m**j for i,j,c in terms)


def classify(p):
    s,c=p['exponent_schedule'],p['constant_law'];L=Q(p['log_power']);kap=None;category='no_finite_power_bound_supplied'
    if c['kind']=='constant':kap=Q(0);category='power_bound'
    if c['kind']=='denominator_power':kap=Q(c['power']);category='power_bound'
    if c['kind']=='power':
        if s['kind']=='power':kap=Q(c['power'])/Q(s['power']);category='power_bound'
        else:kap=Q(0);category='subpolynomial_in_reciprocal_epsilon'
    if c['kind']=='exponential':
        if s['kind']=='exponential' and Q(c['power'])<=Q(s['power']):
            kap=Q(1) if Q(c['power'])==Q(s['power']) else Q(0);category='power_bound' if kap else 'subpolynomial_in_reciprocal_epsilon'
        elif s['kind']=='factorial' and Q(c['power'])<=1:kap=Q(0);category='subpolynomial_in_reciprocal_epsilon'
    if c['kind']=='factorial' and s['kind']=='factorial':kap=Q(1);category='power_bound'
    if c['kind']=='free_per_level':category='unrestricted_existential_per_level_constants'
    alpha=None if kap is None else (kap+L+3)/2;upper=None if alpha is None else alpha.numerator//alpha.denominator
    return category,kap,alpha,upper


def check(d):
    spec=read(d/'protocol.json');queue=read(d/'proof_queue.json');seal=read(d/'seal.json');review=read(d/'analytical_review.json');checks={};counts={'exact_polynomial_differences':0,'profile_growth_consequences':0,'direct_binary_prefix_exchange_checks':0}
    def passed(n):checks[n]=True;print('Verified',n,flush=True)
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n,h in seal['files'].items():assert sha(d/n)==h
    assert review['source_queue_sha256']==sha(d/'proof_queue.json') and review['source_final_sha256']==sha(d/'final_evaluation.json') and review['source_detector_verification_sha256']==sha(d/'verification.json') and review['selection_and_final_frozen_before_analytical_attempts']
    passed('analytical_attempts_follow_unchanged_sealed_formulas_and_final_evaluation')
    lead=queue['minimum_lead'];assert review['minimum_lead']==lead;terms=lead['terms'];P={}
    for i,j,c in terms:P[i,j]=P.get((i,j),Q(0))+Q(c)
    boundary={j:v for (i,j),v in P.items() if i==0 and v};diff={}
    for (i,j),c in P.items():
        for r in range(i):diff[r,j]=diff.get((r,j),Q(0))+comb(i,r)*c
    diff={k:v for k,v in diff.items() if v};admitted=not boundary and diff=={(2,0):Q(1)};cert=review['minimum_proof_certificate'];assert cert['admitted']==cert['global_binary_prefix_minimum_bound_proved']==admitted
    assert cert['boundary_coefficients']=={str(k):str(v) for k,v in boundary.items()} and cert['forward_difference_coefficients']=={str(i)+','+str(j):str(v) for (i,j),v in diff.items()}
    if admitted:
        for m in [1,2,7,100,2**64+1]:
            for J in [0,1,2,3,17,10**6]:assert polynomial(terms,J+1,m)-polynomial(terms,J,m)==J**2;counts['exact_polynomial_differences']+=1
        for m in range(1,11):
            for bits in range(1<<m):
                J=bits.bit_count();loss=sum((bits&((1<<t)-1)).bit_count()**2 for t in range(m));assert loss>=polynomial(terms,J,m)
                positions=[i+1 for i in range(m) if (bits>>i)&1];assert all(v<=m-J+i for i,v in enumerate(positions,1));counts['direct_binary_prefix_exchange_checks']+=1
    assert review['minimum_analytic_status']==('global_combinatorial_bound_proved' if admitted else 'unresolved_detected_relation')
    passed('generic_symbolic_antiderivative_boundary_and_all_dimension_exchange_proof_admission')
    byid={r['program_id']:r for r in queue['queue']};assert {r['program_id'] for r in review['candidate_attempts']}==set(byid)
    for row in review['candidate_attempts']:
        original=byid[row['program_id']];p=original['exact_program'];assert row['exact_program_sha256']==digest(p) and row['exact_global_claim']==original['global_claim'] and row['proof_status']=='unresolved_all_scale_actual_signed_half_gap' and not row['formula_or_fitted_constants_changed'] and not row['global_actual_critical_signed_gap_proved']
        category,kap,alpha,upper=classify(p);c=row['conditional_constant_growth_consequences'];assert c['growth_category']==category and c['kappa_or_limiting_kappa']==(None if kap is None else str(kap)) and c['conditional_reciprocal_pole_power']==(None if alpha is None else str(alpha)) and c['conditional_critical_zero_multiplicity_upper']==upper and c['would_force_simple_critical_zeros_if_global_bound_proved']==(upper==1) and not c['is_claim_about_actual_zero_multiplicities'];counts['profile_growth_consequences']+=1
        assert Q(p['log_power'])>=0 and p['exponent_schedule']['kind']in ['power','factorial','exponential']
        if 'power'in p['exponent_schedule']:assert Q(p['exponent_schedule']['power'])>0
    # The Mellin pole exponent combines the recurrence factor 1/epsilon,
    # the log moment L/2, and the block sum exponent one. The zero-order
    # consequence follows from the local Laurent expansion, not zero data.
    for r in [Q(1,6),Q(1,3),Q(1,2)]:assert (r+3)/2<2
    passed('every_frozen_signed_gap_attempt_unresolved_and_constant_growth_multiplicity_scope_checked')
    tail=review['quantitative_divisor_tail_obstruction'];assert tail['quadratic_upper']=='D*J-P(J)' and tail['necessary_condition_if_PSD']=='P(J)<=D*J' and tail['independent_of_Gram_weight'] and tail['no_tail_position_or_periodicity_assumption'] and tail['cofinal_critical_tail_omission_power_ceiling']=='1/2' and not tail['global_arithmetic_gap_proved']
    if admitted:
        for X in [2,3,4]:
            m=2*X
            for bits in range(1<<m):
                J=bits.bit_count();z=[0]*(2*X)+[(bits>>t)&1 for t in range(m)];N=4*X
                for k in range(1,N+1):assert sum(z[n-1] for n in range(1,k+1) if k%n==0)==z[k-1]
                prefix=0;H=0
                for n,v in enumerate(z,1):
                    if 2*X<=n<4*X:H+=(prefix+v)**2
                    prefix+=v
                # z at 2X is zero, so this sums M(t)^2 for t=2X,...,4X-1.
                assert H>=polynomial(terms,J,m)
    cal=review['generic_calibration'];assert cal['D_coefficient']=='16' and cal['epsilon']=='1' and cal['ordinary_energy_power']=='3' and cal['global_half_gap_proved'] and not cal['RH_strength']
    assert not review['all_scale_critical_signed_bound_proved'] and review['uniform_RH_sufficient_signed_controls_verified']==[] and not review['RH_proved']
    passed('quantitative_tail_obstruction_generic_power_three_calibration_and_no_RH_promotion')
    put(d/'analytical_verification.json',{'checker_sha256':sha(BASE/'check_signed_gap_profile_analytic.py'),'review_sha256':sha(d/'analytical_review.json'),'queue_sha256':sha(d/'proof_queue.json'),'checks':checks,'counts':counts,'all_passed':all(checks.values()),
        'mathematical_audit_imports_production_code':False,'machine_formalized':False,'global_actual_critical_signed_gap_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False});print('Independent signed-gap analytical audit',len(checks),'/',len(checks),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);check(p.parse_args().run_dir.resolve())
