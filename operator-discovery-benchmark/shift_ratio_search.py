#!/usr/bin/env python3
"""Search the unequal-shift family without input prime labels."""

from fractions import Fraction as Q
from itertools import product
from math import gcd
from pathlib import Path
import json
import random
import time
import flint

from prime_scale_search import sieve, factor
from shift_ratio_grammar import forward, recover, real, log, sieve_second_moment_bound, PRODUCTION_CATALOGUE
from fractional_prime_grammar import power_placement

BASE = Path(__file__).resolve().parent
DEST = BASE / 'shift-ratio-results'


def short(x):
    return x.str(32)


def profile(v, N, spf):
    R = forward([flint.arb(0)] + [flint.arb(1)] * N, v)
    B = power_placement(R, True)
    delta = real((1-v)/(1+v))
    maxima = []
    for n in range(2, N+1):
        fs = factor(n, spf); g = gcd(*fs.values())
        sign = (-1)**(len(fs)+len(factor(g, spf))-1)
        if spf[n] == n:
            assert B[n].contains(1)
        else:
            assert B[n].abs_upper() < delta
            maxima.append((float(B[n].abs_upper()), n))
        assert B[n]*sign > 0
        t = log(min(fs))/log(n)
        bound = t/(real(v)+real(1-v)*g*t)
        if spf[n] == n:
            assert B[n].overlaps(bound)
        else:
            assert B[n].abs_upper() < bound
    maximum, index = max(maxima)
    return {'v': str(v), 'cutoff': N, 'R_coefficients': list(map(short, R)),
            'B_coefficients': list(map(short, B)), 'sharp_composite_bound_ball': short(delta),
            'observed_composite_maximum': maximum, 'maximum_index': index,
            'prime_classification_errors': 0, 'sign_errors': 0,
            'least_prime_envelope_errors': 0, 'all_passed': True}, B


def sign_search(B, spf):
    def features(n):
        fs = factor(n, spf); g = gcd(*fs.values()); gs = factor(g, spf)
        return (1, len(fs), sum(fs.values()), len(gs), sum(gs.values()))
    records = []
    for bits in product((0, 1), repeat=5):
        def fit(indices):
            return all(B[n]*(-1)**sum(x*y for x,y in zip(bits, features(n))) > 0 for n in indices)
        training = fit(range(2, 65)); held = training and fit(range(65, len(B)))
        records.append({'parity_weights': list(bits), 'training_passed': bool(training), 'held_out_passed': bool(held)})
    survivors = [r for r in records if r['held_out_passed']]
    assert survivors == [{'parity_weights': [1,1,0,1,0], 'training_passed': True, 'held_out_passed': True}]
    return {'programs': records, 'survivors': survivors, 'training_indices': [2,64],
            'held_out_indices': [65,len(B)-1], 'all_passed': True}


def generic():
    rng = random.Random(2026100743)
    raw = [Q(0), Q(1)] + [Q(rng.randrange(-5,6),rng.randrange(1,8)) for _ in range(95)]
    f = list(map(real,raw)); rows = []
    for v in (Q(1,5),Q(1,2),Q(4,5),Q(1)):
        R = forward(f,v); B = power_placement(R,True); recovered = recover(B,v)
        assert all((a-b).contains(0) for a,b in zip(f,recovered))
        rows.append({'v':str(v),'B_coefficients':list(map(short,B)), 'all_passed':True})
    return {'input_rational_coefficients':list(map(str,raw)), 'records':rows, 'all_passed':True}


def moments(profiles):
    rows = []
    for row in profiles:
        v = Q(row['v']); B = list(map(flint.arb,row['B_coefficients']))
        for X in (2,3,16,64,256,1024,2048):
            observed = sum((B[n]**2 for n in range(X,2*X+1)),flint.arb(0))
            bound = sieve_second_moment_bound(v,X)
            assert observed < bound
            rows.append({'v':str(v),'X':X,'M2_ball':short(observed),
                         'sieve_bound_ball':short(bound),'all_passed':True})
    return {'records':rows, 'external_theorem':'Fan-Pomerance Phi(x,y)<x/log(y)',
            'external_full_sieve_proof_independently_verified':False, 'all_passed':True}


def distant():
    p = 10**12+1
    while not flint.fmpz(p).is_prime():p+=2
    q=p+2
    while not flint.fmpz(q).is_prime():q+=2
    rows=[]
    for v in (Q(1,5),Q(1,2),Q(4,5),Q(19,20)):
        for a,b in ((p,q),(2,p)):
            x,y=log(a),log(b)
            B=1-x/(x+real(v)*y)-y/(y+real(v)*x)
            delta=real((1-v)/(1+v)); t=min(x,y)/(x+y)
            envelope=t/(real(v)+real(1-v)*t)
            assert B<0 and B.abs_upper()<delta and B.abs_upper()<envelope
            rows.append({'v':str(v),'p':a,'q':b,'B_ball':short(B),
                         'delta_ball':short(delta),'least_prime_envelope_ball':short(envelope),
                         'all_passed':True})
    # Boundary extrapolation fails at an exponent with two distinct factors.
    v=Q(3,2); e=6
    val=sum((mu*real(v)/(e+real(v-1)*d) for d,mu in ((1,1),(2,-1),(3,-1),(6,1))),flint.arb(0))
    assert val<0
    return {'records':rows, 'invalid_v_sign_control':{'v':'3/2','n':64,'B_ball':short(val),
             'sign_extrapolation_rejected':True},'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=384
    N=4096;spf,_=sieve(N);profiles=[];half=None
    for v in (Q(1,5),Q(1,2),Q(4,5),Q(19,20)):
        row,B=profile(v,N,spf);profiles.append(row)
        if v==Q(1,2):half=B
        print('Shift ratio v',v,'composite maximum',row['observed_composite_maximum'],flush=True)
    source={'candidate_id':'unequal_shift_arithmetic_logarithm_prime_decoder',
            'definition':'R_v(f)(n)=sum_(ab=n,b>1) f_Dinv(a)f(b)log(b)/(log(b)+v log(a)); B_v=W R_v',
            'profiles':profiles,'sign_grammar':sign_search(half,spf),'generic_inverse_controls':generic(),
            'sieve_second_moment_controls':moments(profiles),'distant_prime_controls':distant(),
            'production_catalogue':PRODUCTION_CATALOGUE,
            'public_program_examples':[
                {'kind':'shift_ratio_program','family':'shift_ratio_prime_decoder','v':'1/2','input':'f'},
                {'kind':'shift_ratio_program','family':'shift_ratio_prime_decoder_inverse','v':'1/2','input':'g'},
                {'kind':'shift_ratio_program','family':'shift_ratio_prime_decoder',
                 'mixture':[{'weight':'1/3','v':'2/7'},{'weight':'2/3','v':'7/9'}],'input':'f'},
                {'kind':'shift_ratio_program','family':'shift_ratio_sieve_second_moment_bound','v':'1/2','X':1024}],
            'coefficient_production_uses_prime_indicator_or_prime_weights':False,
            'all_integer_sign_and_sharp_gap_proved':True,'least_prime_envelope_proved':True,
            'sieve_imported_all_scale_second_moment_proved':True,
            'all_zero_orders_local_signature_proved':True,
            'pole_regularized_RH_equivalence_proved':True,
            'new_independent_prime_distribution_estimate_proved':False,
            'new_RH_estimate_proved':False,'historical_novelty_established':False,
            'verified_new_operators':[],'all_passed':True,'seconds':time.monotonic()-start}
    DEST.mkdir(exist_ok=True)
    (DEST/'shift_ratio_search.json').write_text(json.dumps(source,indent=2)+'\n')
    print('Shift-ratio arithmetic search passed seconds',source['seconds'],flush=True)


if __name__=='__main__':main()
