#!/usr/bin/env python3
"""Feed unresolved estimate goals into exact arithmetic preconditioners."""

from fractions import Fraction as Q
from collections import Counter
from itertools import combinations
from math import gcd
from pathlib import Path
import hashlib
import json
import time
import flint

from estimate_grammar import (inverse_one_prefix,prefix_moments,smoothed_from_moments,
    real,growth_bound,fit_constant,rational_upper)
from cancellation_rewrite_grammar import certificate,divisors_with_sign,PRODUCTION_CATALOGUE

BASE = Path(__file__).resolve().parent
DEST = BASE/'estimate-results'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def monotone_tail(proof,C,theta,b,limit):
    if theta<1 or b<0:
        return None
    choices = sorted({min(2**j,limit) for j in range(1,limit.bit_length()+1)}|{limit})
    for X in choices:
        left = real(C)*real(X)**real(theta-1)*real(X).log()**b
        right = real(Q(proof['linear_constant'])+Q(proof['boundary_cost'])/X)
        if left>=right:
            return X
    return None


def finite_initial_proof(observations,C,theta,b,threshold):
    records = []
    for X in range(2,threshold):
        actual = observations[X]
        bound = growth_bound(C,theta,b,X)
        if not real(abs(actual))<=bound:
            if real(abs(actual))>bound:
                return {'status':'falsified_at_initial_scale','X':X,'exact_sum':str(actual)}
            return {'status':'finite_ball_comparison_undecided','X':X}
        records.append([X,str(actual)])
    return {'status':'certified_all_initial_integer_scales','count':len(records),
            'exact_observations_sha256':hashlib.sha256(json.dumps(records).encode()).hexdigest()}


def main():
    start = time.monotonic()
    flint.ctx.prec = 320
    source_path = DEST/'estimate_search.json'
    check_path = DEST/'estimate_verification.json'
    source = json.loads(source_path.read_text())
    checked = json.loads(check_path.read_text())
    assert checked['all_passed'] and checked['source_artifact_sha256']==sha(source_path)
    pool = [r['prime'] for r in source['learned_cancellation_certificates']['all_scale_certificates']][:4]
    sets = [tuple(row) for size in (1,2,3) for row in combinations(pool,size)]
    scales = (19,71,293,997,4099)
    mu = inverse_one_prefix(max(scales))
    moments = prefix_moments(mu,scales,4)
    records = []
    for primes in sets:
        P = 1
        for p in primes:
            P *= p
        ds = divisors_with_sign(primes)
        requested = {X//d for X in scales for d,sign in ds if X//d>0}
        rough = [0]+[mu[n] if gcd(n,P)==1 else 0 for n in range(1,len(mu))]
        rough_moments = prefix_moments(rough,requested,4)
        for row in source['cancellation_estimate_search']['records']:
            c = tuple(map(Q,row['kernel']))
            proof = certificate(primes,c)
            observations = []
            for X in scales:
                expected = smoothed_from_moments(c,X,moments[X])
                actual = Q(0)
                for d,sign in ds:
                    Y = X//d
                    if not Y:
                        continue
                    actual += sign*sum((a*Q(d**j*rough_moments[Y][j],X**j)
                                        for j,a in enumerate(c)),Q(0))
                assert actual==expected
                assert abs(actual)<=Q(proof['linear_constant'])*X+Q(proof['boundary_cost'])
                observations.append({'X':X,'exact_rewritten_target':str(actual)})
            records.append({'id':len(records),'kernel_id':row['id'],'certificate':proof,
                'changed_scale_identity_controls':observations,
                'weak_original_absolute_constant':row['available_weak_all_scale_certificate']['constant'],
                'strict_linear_slope_improvement':Q(proof['linear_constant'])<Q(row['available_weak_all_scale_certificate']['constant'])})
    # Each obligation retains its original bound; rewriting changes its
    # representation, not its target or its mathematical status.
    feedback = []
    all_moments = prefix_moments(mu,range(2,max(scales)+1),4)
    observation_cache = {}
    for candidate in source['cancellation_estimate_search']['candidate_estimates']:
        if candidate['status']!='numerical_conjecture_missing_uniform_cancellation_certificate':
            continue
        options = [r for r in records if r['kernel_id']==candidate['kernel_id']]
        best = min(options,key=lambda r:(Q(r['certificate']['linear_constant']),Q(r['certificate']['boundary_cost'])))
        result = {'estimate_id':candidate['id'],'kernel_id':candidate['kernel_id'],
            'target_constant':candidate['constant'],'target_theta':candidate['theta'],'target_log_power':candidate['log_power'],
            'rewrite_candidate_id':best['id'],'conditioned_prime_set':best['certificate']['primes'],
            'available_linear_constant':best['certificate']['linear_constant'],
            'available_boundary_cost':best['certificate']['boundary_cost'],
            'status':'uniform_cancellation_obligation_still_open',
            'new_subgoal':'Prove the requested signed bound on the exact coprime Mobius row with the generated piecewise dilation kernel; retain the same Mellin numerator and all boundary terms',
            'available_affine_bound_implies_requested_growth_bound':False}
        theta,b,C = Q(candidate['theta']),int(candidate['log_power']),Q(candidate['constant'])
        kernel_id = candidate['kernel_id']
        if kernel_id not in observation_cache:
            c = tuple(map(Q,source['cancellation_estimate_search']['records'][kernel_id]['kernel']))
            observation_cache[kernel_id] = {X:smoothed_from_moments(c,X,M) for X,M in all_moments.items()}
        observations = observation_cache[kernel_id]
        early = finite_initial_proof(observations,C,theta,b,16)
        if early['status']=='falsified_at_initial_scale':
            result.update(status='original_estimate_falsified_at_initial_scale',
                          initial_scale_proof_attempt=early,new_subgoal=None)
        if theta>=1 and b>=0:
            attempts = [(monotone_tail(r['certificate'],C,theta,b,max(scales)),r) for r in options]
            attempts = [(X,r) for X,r in attempts if X is not None]
            if attempts:
                threshold,selected = min(attempts,key=lambda pair:pair[0])
                initial = finite_initial_proof(observations,C,theta,b,threshold)
                result['initial_scale_proof_attempt'] = initial
                if initial['status']=='certified_all_initial_integer_scales':
                    result.update(status='proved_original_estimate_by_finite_prefix_and_monotone_tail',
                        rewrite_candidate_id=selected['id'],tail_threshold=threshold,
                        conditioned_prime_set=selected['certificate']['primes'],
                        available_linear_constant=selected['certificate']['linear_constant'],
                        available_boundary_cost=selected['certificate']['boundary_cost'],
                        available_affine_bound_implies_requested_growth_bound=True)
                    result['new_subgoal'] = None
                elif initial['status']=='falsified_at_initial_scale':
                    result['status'] = 'original_estimate_falsified_at_initial_scale'
                    result['new_subgoal'] = None
            # Synthesize a repaired constant from finite data plus the
            # certificate's tail cost; neither alone is treated as proof.
            prefix_C = fit_constant(list(observations.items()),theta,b)
            repairs = []
            for option in options:
                proof = option['certificate']
                N = max(scales)
                tail_C = (real(Q(proof['linear_constant'])+Q(proof['boundary_cost'])/N) /
                          (real(N)**real(theta-1)*real(N).log()**b))
                fixed_C = max(prefix_C,rational_upper(tail_C,1024))
                threshold = monotone_tail(proof,fixed_C,theta,b,N)
                if threshold is not None:
                    repairs.append((fixed_C,threshold,option))
            if repairs:
                fixed_C,threshold,selected = min(repairs,key=lambda row:(row[0],row[1]))
                initial = finite_initial_proof(observations,fixed_C,theta,b,threshold)
                assert initial['status']=='certified_all_initial_integer_scales'
                result['synthesized_repaired_estimate'] = {'constant':str(fixed_C),'theta':str(theta),'log_power':str(b),
                    'domain':'every integer X >= 2','rewrite_candidate_id':selected['id'],
                    'tail_threshold':threshold,'finite_prefix_proof':initial,
                    'status':'proved_all_scale_by_finite_prefix_and_monotone_tail',
                    'new_sublinear_cancellation':False}
        feedback.append(result)
    first = [r for r in records if r['kernel_id']==0 and r['certificate']['primes']==[2]][0]
    assert first['certificate']['linear_constant']=='1/8' and first['certificate']['boundary_cost']=='1'
    out = {'source_estimate_search_sha256':sha(source_path),'source_estimate_verification_sha256':sha(check_path),
        'producer_code_sha256':sha(BASE/'cancellation_rewrite_search.py'),
        'grammar_code_sha256':sha(BASE/'cancellation_rewrite_grammar.py'),
        'proof_sha256':sha(BASE/'cancellation_rewrite_proof.txt'),
        'learned_prime_pool':pool,'prime_sets_searched':list(map(list,sets)),
        'coefficient_cutoff':max(scales),'records':records,'estimate_obligation_feedback':feedback,
        'classic_smoothing_calibration':first,
        'proved_affine_bounds':len(records),'unresolved_estimate_goals_rewritten':len(feedback),
        'feedback_status_counts':dict(Counter(r['status'] for r in feedback)),
        'repaired_all_scale_estimates_proved':sum('synthesized_repaired_estimate' in r for r in feedback),
        'production_catalogue':PRODUCTION_CATALOGUE,
        'sublinear_cancellation_certificate_discovered':False,
        'new_independent_prime_distribution_estimate_proved':False,
        'new_RH_estimate_proved':False,'verified_new_operators':[],
        'all_passed':True,'seconds':time.monotonic()-start}
    (DEST/'cancellation_rewrite_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Cancellation rewrite search',len(records),'certified affine bounds;',len(feedback),'open goals rewritten; seconds',out['seconds'],flush=True)


if __name__=='__main__':
    main()
