#!/usr/bin/env python3
"""Learn signed arithmetic cancellation without training on a desired bound."""

from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import hashlib
import json
import random
import time
import flint
import sympy as sp

from fractional_prime_grammar import power_placement
from shift_ratio_grammar import forward,recover,real,log
from compensated_shift_grammar import atoms,arithmetic_certificate,PRODUCTION_CATALOGUE
from prime_scale_search import sieve

BASE = Path(__file__).resolve().parent
DEST = BASE/'compensated-shift-results'
SHIFTS = (Q(1,5),Q(1,3),Q(3,7),Q(1,2),Q(2,3),Q(5,7),Q(4,5))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def short(x):
    return x.str(35)


def rational_guess(x):
    provisional = Q(float(x.mid())).limit_denominator(10000)
    assert x.overlaps(real(provisional))
    return provisional


def learn_atomic_pair_model(v,B):
    rows = []
    for p,q in ((2,3),(2,5),(3,7),(5,11),(7,17),(11,31)):
        t = log(p)/log(p*q)
        z = t*(1-t)
        y = -z/B[p*q]
        rows.append({'p':p,'q':q,'z_ball':short(z),'reciprocal_pair_response_ball':short(y)})
    z1,z2 = map(flint.arb,(rows[0]['z_ball'],rows[1]['z_ball']))
    y1,y2 = map(flint.arb,(rows[0]['reciprocal_pair_response_ball'],rows[1]['reciprocal_pair_response_ball']))
    slope = rational_guess((y1-y2)/(z1-z2))
    intercept = rational_guess(y1-real(slope)*z1)
    assert intercept>0
    for row in rows:
        z,y = flint.arb(row['z_ball']),flint.arb(row['reciprocal_pair_response_ball'])
        assert (y-real(intercept)-real(slope)*z).contains(0)
    return {'v':str(v),'training_pair_count':2,'held_out_pair_count':4,
        'learned_reciprocal_affine_intercept':str(intercept),
        'learned_reciprocal_affine_slope':str(slope),
        'inferred_unbalanced_pair_first_order':str(1/intercept),
        'records':rows,'all_finite_pair_fits_passed':True}


def coefficient_from_factors(fs,v):
    g = sp.igcd(*fs.values()) if len(fs)>1 else next(iter(fs.values()))
    out = flint.arb(0)
    for k in range(1,int(g)+1):
        if g%k:
            continue
        f = flint.fmpz(k).factor()
        sign = 0 if any(e>1 for p,e in f) else (-1)**len(f)
        if not sign:
            continue
        ln = sum((e//k*log(p) for p,e in fs.items()),flint.arb(0))
        R = flint.arb(0)
        for bits in product((0,1),repeat=len(fs)):
            la = sum((log(p) for p,b in zip(fs,bits) if b),flint.arb(0))
            lb = ln-la
            # A complete squarefree divisor is excluded when b=1.
            if all(bits) and all(e//k==1 for e in fs.values()):
                continue
            R += (-1)**sum(bits)*lb/(lb+real(v)*la)
        out += real(Q(sign,k))*R
    return out


def generic_controls():
    rng = random.Random(2026100791)
    raw = [Q(0),Q(1)]+[Q(rng.randrange(-7,8),rng.randrange(1,9)) for _ in range(126)]
    values = list(map(real,raw))
    records = []
    for u,v in ((Q(1,3),Q(2,3)),(Q(1,5),Q(4,5)),(Q(3,7),Q(5,7))):
        A = atoms(u,v)
        B = power_placement(forward(values,A),True)
        recovered = recover(B,A)
        assert all((a-b).contains(0) for a,b in zip(values,recovered))
        records.append({'left':str(u),'right':str(v),'decoder_coefficients':list(map(short,B)),
                        'generic_triangular_inverse_passed':True})
    return {'rational_input':list(map(str,raw)),'records':records}


def actual_large_prime_control(u,v):
    p = 10**12+1
    while not flint.fmpz(p).is_prime():
        p += 2
    q = p+2
    while not flint.fmpz(q).is_prime():
        q += 2
    A = atoms(u,v)
    fs = {2:1,p:1,q:1}
    actual = sum((real(w)*coefficient_from_factors(fs,x) for w,x in A),flint.arb(0))
    t = log(2)/(log(2)+log(p)+log(q))
    K = Q(arithmetic_certificate(u,v)['two_prime_least_prime_square_envelope_constant'])
    assert actual.abs_lower()>real(K)*t*t
    x = sp.Symbol('x')
    h = sum(sp.Rational(w.numerator,w.denominator)*x/
            (sp.Rational(a.numerator,a.denominator)+(1-sp.Rational(a.numerator,a.denominator))*x)
            for w,a in A)
    hp = sp.diff(h,x)
    first = sp.simplify(hp.subs(x,1)+hp.subs(x,0)-2*hp.subs(x,sp.Rational(1,2)))
    assert first!=0
    return {'p':p,'q':q,'query_factorization':[[2,1],[p,1],[q,1]],
        'complete_one_coefficient_ball':short(actual),'least_prime_log_ratio_ball':short(t),
        'failed_two_prime_bound_ball':short(real(K)*t*t),
        'triple_linear_asymptotic_coefficient':str(first),
        'universal_square_envelope_rejected_by_unbounded_actual_prime_sequence':True,
        'full_prefix_at_large_index_claimed':False,
        'prime_factors_used_only_in_control_query':True}


def main():
    start = time.monotonic()
    flint.ctx.prec = 320
    N = 4096
    values = [flint.arb(0)]+[flint.arb(1)]*N
    spf,_ = sieve(N)
    profiles,learned = {},[]
    for v in SHIFTS:
        B = power_placement(forward(values,v),True)
        profiles[v] = B
        learned.append(learn_atomic_pair_model(v,B))
    # Recover the common first-order feature from five rational node fits.
    exponents = list(range(-2,3))
    matrix = sp.Matrix([[sp.Rational(v.numerator,v.denominator)**j for j in exponents] for v in SHIFTS[:5]])
    rhs = sp.Matrix([sp.Rational(Q(r['inferred_unbalanced_pair_first_order']).numerator,
                                Q(r['inferred_unbalanced_pair_first_order']).denominator) for r in learned[:5]])
    fit = list(matrix.inv()*rhs)
    assert list(map(str,fit))==['0','1','0','-1','0']
    for v,row in zip(SHIFTS[5:],learned[5:]):
        assert sum(a*sp.Rational(v.numerator,v.denominator)**j for a,j in zip(fit,exponents))==sp.Rational(row['inferred_unbalanced_pair_first_order'])
    records = []
    chosen = None
    for u,v in combinations(SHIFTS,2):
        i,j = SHIFTS.index(u),SHIFTS.index(v)
        a,b = Q(learned[i]['inferred_unbalanced_pair_first_order']),Q(learned[j]['inferred_unbalanced_pair_first_order'])
        weights = (-b/(a-b),a/(a-b))
        assert tuple(w for w,x in atoms(u,v))==weights
        cert = arithmetic_certificate(u,v)
        B = [real(weights[0])*x+real(weights[1])*y for x,y in zip(profiles[u],profiles[v])]
        prime_errors = sum(not B[n].contains(1) for n in range(2,N+1) if spf[n]==n)
        composite = [(float(B[n].abs_upper()),n) for n in range(2,N+1) if spf[n]!=n]
        bound = Q(cert['universal_composite_upper'])
        assert prime_errors==0 and all(B[n].abs_upper()<real(bound) for _,n in composite)
        row = {'left':str(u),'right':str(v),'learned_weights':list(map(str,weights)),
            'certificate':cert,'prime_classification_errors':prime_errors,
            'finite_composite_maximum':max(composite)[0],'maximum_index':max(composite)[1],
            'fitted_global_gap':cert['sharp_two_distinct_prime_product_gap'],
            'fitted_global_gap_passes_complete_prefix':all(B[n].abs_upper()<real(Q(cert['sharp_two_distinct_prime_product_gap'])) for _,n in composite),
            'all_scale_global_sharp_gap_proved':False,
            'whole_prefix_checked':N,'all_passed':True}
        if (u,v)==(Q(1,3),Q(2,3)):
            row['B_coefficients'] = list(map(short,B))
            selected_pair = (u,v)
            square_K = real(Q(cert['two_prime_least_prime_square_envelope_constant']))
            failures = [n for n in range(2,N+1) if spf[n]!=n and
                         B[n].abs_lower()>square_K*(log(spf[n])/log(n))*(log(spf[n])/log(n))]
            assert failures
            row['incorrect_universal_square_envelope_first_counterexample'] = failures[0]
            chosen = row
        records.append(row)
    assert chosen is not None
    root_fault = next(r for r in records if r['certificate']['root_signature_certificate']['zero_leading_signature_orders'])
    assert root_fault['left']=='3/7' and root_fault['right']=='5/7'
    out = {'candidate_id':'signed_pair_compensated_arithmetic_logarithm',
        'producer_code_sha256':sha(BASE/'compensated_shift_search.py'),
        'grammar_code_sha256':sha(BASE/'compensated_shift_grammar.py'),
        'proof_sha256':sha(BASE/'compensated_shift_proof.txt'),
        'coefficient_cutoff':N,'atomic_pair_models':learned,
        'first_order_feature_search':{'basis_exponents':exponents,'learned_coefficients':list(map(str,fit)),
                                    'training_shift_count':5,'held_out_shift_count':2},
        'pair_compensators':records,'selected_operator':chosen,
        'all_order_leading_signature_failure_control':root_fault,
        'large_actual_prime_three_factor_control':actual_large_prime_control(*selected_pair),
        'generic_inverse_controls':generic_controls(),'production_catalogue':PRODUCTION_CATALOGUE,
        'coefficient_operator_uses_prime_or_factor_oracle':False,
        'historical_novelty_established':False,'new_independent_prime_distribution_estimate_proved':False,
        'new_RH_estimate_proved':False,'verified_new_operators':[],'all_passed':True,
        'seconds':time.monotonic()-start}
    DEST.mkdir(exist_ok=True)
    (DEST/'compensated_shift_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Compensated shift search',len(records),'signed operators; generic inverses and controls passed; seconds',out['seconds'],flush=True)


if __name__=='__main__':
    main()
