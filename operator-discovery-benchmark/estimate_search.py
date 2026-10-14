#!/usr/bin/env python3
"""Propose estimates from arithmetic data, then attempt bounded proof search."""

from fractions import Fraction as Q
from math import comb
from pathlib import Path
from collections import Counter
import hashlib
import json
import random
import time
import flint

from estimate_grammar import (PRODUCTION_CATALOGUE, inverse_one_prefix, prefix_moments,
    polynomial_kernel, smoothed_from_moments, fit_constant, growth_bound, real,
    mellin_certificate, trivial_cancellation_certificate, dilation_candidates,
    dilation_cancellation_certificate, positive_envelope_certificate,
    envelope_constant_ball, rational_upper)

BASE = Path(__file__).resolve().parent
DEST = BASE / 'estimate-results'
TRAINING = (16,24,32,48,64,96,128,192,256,384,512,768,1024)
HELD_OUT = (2048,3072,4096,6144,8192,12288,16384,24576,32768,
            49152,65536,98304,100003,131071,131072)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def kernels():
    # Generate kernels before looking at mu, growth, moments or any zero.
    result = [tuple(Q((-1)**j*comb(d,j)) for j in range(d+1)) for d in range(1,5)]
    rng = random.Random(2026100717)
    while len(result) < 20:
        P = [Q(1)] + [Q(rng.randrange(-4,5),rng.randrange(1,4)) for _ in range(3)]
        W = P + [Q(0)]
        for j,a in enumerate(P):
            W[j+1] -= a
        c = polynomial_kernel(W)
        if c not in result:
            result.append(c)
    return result


def known_zero_gate():
    # This is a post-fit structural test, never a training target.
    verification = BASE/'shift-ratio-results/shift_ratio_analytic_verification.json'
    source = BASE/'shift-ratio-results/shift_ratio_analytic.json'
    d = json.loads(verification.read_text())
    assert d['all_passed'] and d['source_artifact_sha256'] == sha(source)
    row = d['actual_zero_and_corridor_audit']['records'][0]
    c = flint.acb(real(Q(1,2)),flint.arb(row['disk_centre'][1]))
    r = real(Q(row['fresh_nested_Rouche_radius']))
    rectangle = c + flint.acb(flint.arb(0,r),flint.arb(0,r))
    derivative = flint.acb_series([c,1],prec=2).zeta()[1]
    second = 2*flint.acb_series([rectangle,1],prec=3).zeta()[2]
    margin = derivative.abs_lower()*r-c.zeta().abs_upper()-second.abs_upper()*r*r/2
    assert margin > 0
    return rectangle, {'centre': row['disk_centre'], 'radius': str(Q(row['fresh_nested_Rouche_radius'])),
        'fresh_Rouche_margin_lower_ball': margin.lower().str(35),
        'one_simple_zero_in_disk_certified': True,
        'reflection_and_uniqueness_place_zero_on_Re_half': True,
        'zero_reflection_source': 'https://dlmf.nist.gov/25.10',
        'dependency': str(verification.relative_to(BASE)), 'dependency_sha256': sha(verification),
        'source_sha256': sha(source), 'new_zero_discovered': False}


def cancellation_search(mu, rectangle):
    generated = kernels()
    moments = prefix_moments(mu,TRAINING+HELD_OUT,max(len(c)-1 for c in generated))
    candidates = []
    coefficient_records = []
    for index,c in enumerate(generated):
        observations = {X:smoothed_from_moments(c,X,moments[X]) for X in TRAINING+HELD_OUT}
        transform = mellin_certificate(c)
        numerator = sum((real(a)/(rectangle+j) for j,a in enumerate(c)),flint.acb(0))
        visible = bool(numerator.abs_lower()>0)
        coefficient_records.append({'id': index,'kernel': list(map(str,c)),
            'observations': [{'X':X,'exact_smoothed_sum':str(S),
                              'split':'training' if X in TRAINING else 'held_out'} for X,S in observations.items()],
            'Mellin_certificate': transform,
            'Mellin_absolute_lower_at_known_zero_ball': numerator.abs_lower().str(35),
            'known_zero_visible': visible,
            'available_weak_all_scale_certificate': trivial_cancellation_certificate(c)})
        for theta in (Q(0),Q(1,4),Q(1,3),Q(1,2),Q(2,3),Q(3,4),Q(1)):
            for b in (-2,-1,0,1,2):
                C = fit_constant([(X,observations[X]) for X in TRAINING],theta,b)
                failures = [X for X in HELD_OUT if not real(abs(observations[X])) <= growth_bound(C,theta,b,X)]
                obstruction = visible and (theta<Q(1,2) or (theta==Q(1,2) and b<0))
                if obstruction:
                    status = 'ruled_out_all_scale_by_known_zero'
                    obligations = []
                elif failures:
                    status = 'falsified_on_held_out_scales'
                    obligations = []
                else:
                    weak = trivial_cancellation_certificate(c)
                    weak_C = Q(weak['constant'])
                    sufficient = theta>=1 and b>=0 and (
                        real(C)*real(2)**real(theta-1)*real(2).log()**b >= real(weak_C))
                    if sufficient:
                        status = 'proved_all_scale_by_absolute_sum'
                        obligations = []
                    else:
                        status = 'numerical_conjecture_missing_uniform_cancellation_certificate'
                        obligations = ['Prove |sum mu(n) W(n/X)| <= C X^theta (log X)^b for every integer X>=2; finite fits do not certify this',
                                       'A new signed-cancellation identity, positive decomposition or scale recurrence is required; no available backend proves this candidate']
                candidates.append({'id': len(candidates), 'kernel_id': index,
                    'target':'absolute smoothed sum of the Dirichlet inverse of constant one',
                    'domain':'every integer X >= 2', 'constant':str(C),'theta':str(theta),'log_power':str(b),
                    'training_constant_margin':'5/4','training_rounding_denominator':1024,
                    'held_out_passed': not failures,'held_out_failure_scales': failures,
                    'post_fit_known_zero_obstruction': bool(obstruction),
                    'nonvanishing_Mellin_RH_relevance': bool(theta==Q(1,2) and b>=0 and
                        transform['nonvanishing_Re_s_ge_zero_certified']),
                    'status': status,'obligations': obligations,
                    'historical_novelty_established': False})
    plateau = [r for r in candidates if r['kernel_id']==3 and r['theta']=='0' and r['log_power']=='0'][0]
    assert plateau['held_out_passed'] and plateau['post_fit_known_zero_obstruction']
    return {'kernel_generation_seed':2026100717,'kernels_generated_before_arithmetic_observations':True,
        'training_scales':list(TRAINING),'held_out_scales':list(HELD_OUT),
        'records':coefficient_records,'candidate_estimates':candidates,
        'status_counts':dict(Counter(r['status'] for r in candidates)),
        'finite_survivor_but_mathematically_impossible_control': plateau,
        'global_cancellation_estimate_beating_linear_growth_proved':False}


def learned_dilations(mu):
    rows = dilation_candidates(mu)
    certificates = []
    for row in rows:
        p = row['multiplier']
        if row['held_out_passed'] and row['lambda']==-1 and flint.fmpz(p).is_prime():
            certificate = dilation_cancellation_certificate(p)
            # Determine the finite identity using the complete input rows too.
            for X in TRAINING+HELD_OUT:
                M = sum(mu[1:X+1])
                paired = sum(mu[n] for n in range(X//p+1,X+1) if n%p)
                count = X-2*(X//p)+X//(p*p)
                assert M==paired and abs(M)<=count
                assert Q(count)<=Q(certificate['linear_constant'])*X+Q(certificate['boundary_cost'])
            certificates.append(certificate)
    best = min(certificates,key=lambda r:Q(r['linear_constant']))
    assert best['prime']==2 and best['linear_constant']=='1/4' and best['boundary_cost']=='3/4'
    return {'searched_multipliers':[2,20],'searched_row_constants':[-2,-1,0,1,2],
        'learned_row_laws':rows,'all_scale_certificates':certificates,'best_linear_bound':best,
        'composite_row_is_full_prime_partition_claimed':False,
        'new_sublinear_Mertens_bound_proved':False}


def envelope_search():
    proof_path = BASE/'shift_ratio_proof.txt'
    check_path = BASE/'shift-ratio-results/shift_ratio_verification.json'
    source_path = BASE/'shift-ratio-results/shift_ratio_search.json'
    arithmetic = json.loads(check_path.read_text())
    assert arithmetic['all_passed'] and arithmetic['source_artifact_sha256']==sha(source_path)
    mixtures = [[{'weight':'1','v':str(v)}] for v in (Q(1,5),Q(1,2),Q(4,5),Q(1))]
    mixtures += [[{'weight':'1/3','v':'2/7'},{'weight':'2/3','v':'7/9'}],
                 [{'weight':'2/5','v':'1/3'},{'weight':'3/5','v':'5/6'}]]
    rows = []
    for mixture in mixtures:
        for q in (1,2,4):
            certificate = positive_envelope_certificate(mixture,q,'Fan_Pomerance_Theorem_A')
            if q>1:
                C = envelope_constant_ball(mixture,q)
                certificate['constant_native_integral_ball'] = C.str(35)
                certificate['constant_rational_upper'] = str(rational_upper(C))
                if q==2:
                    jensen = 2*(1+sum((Q(a['weight'])/Q(a['v']) for a in mixture),Q(0)))
                    certificate['existing_Jensen_constant'] = str(jensen)
                    certificate['strictly_improves_Jensen_for_this_mixture'] = bool(C.upper()<real(jensen))
            rows.append(certificate)
    improvement = next(r for r in rows if r.get('moment_order')==2 and len(r.get('mixture',[]))==2)
    assert improvement['strictly_improves_Jensen_for_this_mixture']
    return {'searched_positive_mixtures':mixtures,'searched_moment_orders':[1,2,4],
        'score_envelope_proof_dependency':{'proof':str(proof_path.relative_to(BASE)),
            'proof_sha256':sha(proof_path),'verification':str(check_path.relative_to(BASE)),
            'verification_sha256':sha(check_path),'source_sha256':sha(source_path)},
        'imported_theorem_cached_primary_pdf_sha256':sha(BASE/'literature/roughness/fan_pomerance_rough_numbers.pdf'),
        'records':rows, 'automatically_synthesized_finite_all_scale_bounds':sum(r['moment_order']>1 for r in rows),
        'critical_origin_divergence_reported_as_missing_proof_not_disproof':True,
        'new_sieve_theorem_discovered':False, 'QRH_bound_used_as_training_target':False}


def main():
    start = time.monotonic()
    flint.ctx.prec = 320
    N = max(HELD_OUT)
    mu = inverse_one_prefix(N)
    assert all(a in (-1,0,1) for a in mu)
    rectangle,zero = known_zero_gate()
    cancellation = cancellation_search(mu,rectangle)
    dilations = learned_dilations(mu)
    print('Estimate proposals',len(cancellation['candidate_estimates']),cancellation['status_counts'],flush=True)
    energy = envelope_search()
    out = {'coefficient_cutoff':N,
        'producer_code_sha256':sha(BASE/'estimate_search.py'),
        'grammar_code_sha256':sha(BASE/'estimate_grammar.py'),
        'proof_sha256':sha(BASE/'estimate_proof.txt'),
        'production_coefficient_engine_uses_prime_or_factor_oracle':False,
        'inverse_coefficients_sha256':hashlib.sha256(bytes(a+1 for a in mu)).hexdigest(),
        'cancellation_estimate_search':cancellation,'learned_cancellation_certificates':dilations,
        'positive_energy_estimate_search':energy,'known_zero_obstruction_certificate':zero,
        'production_catalogue':PRODUCTION_CATALOGUE,
        'proof_scope':'Exact elementary certificate backends and named classical theorem composition; finite successes remain conjectures',
        'new_independent_prime_distribution_estimate_proved':False,
        'new_RH_estimate_proved':False,'verified_new_operators':[],
        'all_passed':True,'seconds':time.monotonic()-start}
    DEST.mkdir(exist_ok=True)
    (DEST/'estimate_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Estimate search passed seconds',out['seconds'],flush=True)


if __name__=='__main__':
    main()
