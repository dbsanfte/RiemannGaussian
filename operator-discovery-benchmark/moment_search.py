#!/usr/bin/env python3
"""Exact discovery of moment-annihilating prime shears and coefficient drift."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, factorial, isqrt
from pathlib import Path
import json
import time
import flint

from exact_arithmetic import formal_exp, formal_log, normalized_power

BASE = Path(__file__).resolve().parent
DEST = BASE / 'moment-results'


def primes(N):
    sieve = [True] * (N + 1)
    sieve[:2] = [False, False]
    for p in range(2, isqrt(N) + 1):
        if sieve[p]:
            sieve[p*p::p] = [False] * len(sieve[p*p::p])
    return tuple(p for p in range(2, N + 1) if sieve[p])


@lru_cache(maxsize=None)
def annihilator(m):
    # Solve all m moment constraints, fixing the first weight to one.
    a = [[Q(j ** k) for j in range(1, m + 1)] + [Q(-int(k == 0))]
         for k in range(m)]
    for col in range(m):
        pivot = next(row for row in range(col, m) if a[row][col])
        a[col], a[pivot] = a[pivot], a[col]
        scale = a[col][col]
        a[col] = [v / scale for v in a[col]]
        for row in range(m):
            if row != col:
                scale = a[row][col]
                a[row] = [v - scale*w for v, w in zip(a[row], a[col])]
    return [Q(1)] + [row[-1] for row in a]


def grammar():
    rows = []
    for m, bound in ((2, 3), (4, 6)):
        fits, held, scored = [], [], 0
        for tail in product(range(-bound, bound + 1), repeat=m):
            scored += 1
            w = [1] + list(tail)
            if all(sum(w[j]*j**k for j in range(m+1)) == 0 for k in range(m-1)):
                fits.append(w)
                if sum(w[j]*j**(m-1) for j in range(m+1)) == 0:
                    held.append(w)
        rows.append({'m': m, 'coefficient_bound': bound, 'models_scored': scored,
                     'training_fit_count': len(fits), 'held_out_survivors': held})
    high = []
    for m in (6, 8, 10, 12, 16):
        w = annihilator(m)
        residual = sum(w[j]*j**m for j in range(m+1))
        high.append({'m': m, 'weights': list(map(str, w)),
                     'all_lower_moments_zero': all(sum(w[j]*j**k for j in range(m+1)) == 0 for k in range(m)),
                     'first_nonzero_moment': str(residual),
                     'held_out_binomial_pattern': w == [Q((-1)**j * comb(m, j)) for j in range(m+1)]})
    return {'bounded_search': rows, 'higher_order_linear_constraint_checks': high,
            'calibration': 'Classical binomial finite differences, independently recovered',
            'weights_are_known': True}


def kernel(h, m, gap_min=2):
    out = {}
    ps = [p for p in sorted(h) if p >= 2 and h[p] and flint.fmpz(p).is_prime()]
    for i, p in enumerate(ps):
        for q in ps[i+1:]:
            d = q-p
            if d < gap_min:
                continue
            for j, w in enumerate(annihilator(m)):
                n = p**(m-j) * q**j * d**(m+2)
                out[n] = out.get(n, Q(0)) + w*h[p]*h[q]
    return {n: v for n, v in out.items() if v}


def flow(h, t, m):
    K = kernel(h, m)
    return {n: v for n in h.keys() | K.keys()
            if (v := h.get(n, Q(0)) + t*K.get(n, Q(0)))}


def exp_query_prime(h, n):
    # Exact coefficient of EXP_D of a prime-supported logarithm.
    out = Q(1)
    for p in sorted(h):
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            out *= h.get(p, Q(0))**e / factorial(e)
        if n == 1:
            break
    if n > 1:
        return Q(0)
    return out


def exact_laws():
    h = {2: Q(-2, 3), 3: Q(3, 5), 5: Q(-1, 7), 7: Q(2, 9), 11: Q(1, 4)}
    rows = []
    # Full sparse output, including arbitrarily large encoded indices.
    for m in (2, 4, 6, 8, 12, 16):
        K, t, u = kernel(h, m), Q(2, 3), Q(-3, 5)
        first = min(K)
        n0 = 4*6**m
        roots = kernel({p: v/2 for p, v in h.items()}, m)
        checks = {'complete_sparse_group': flow(flow(h, t, m), u, m) == flow(h, t+u, m),
                  'complete_sparse_inverse': flow(flow(h, t, m), -t, m) == h,
                  'prime_log_projection_fixed': all(not flint.fmpz(n).is_prime() for n in K),
                  'minimal_image_index': first == n0,
                  'first_correction_coefficient': K[n0] == h[3]*h[5],
                  'quadratic_input_root_degree': roots == {n: v/4 for n, v in K.items()},
                  'ordinary_root_commutation_rejected': roots != {n: v/2 for n, v in K.items()},
                  'binomial_order_is_not_input_degree': m == 2 or roots != {n: v/(2**m) for n, v in K.items()}}
        original = exp_query_prime(h, n0)
        rows.append({'m': m, 'input_log': {str(n): str(v) for n,v in h.items()},
                     'correction': {str(n): str(v) for n,v in sorted(K.items())},
                     'first_index': n0, 'first_original_EXP_coefficient': str(original),
                     'first_transformed_EXP_coefficient': str(original+t*h[3]*h[5]),
                     'parameter': str(t), 'checks': checks})
    # A full ordinary convolution EXP/LOG/root computation where the first
    # changed coefficient is within the prefix; sparse high-order proofs above
    # are not disguised as ordinary dense EXP computations.
    m, N = 2, 256
    log = [Q(0)]*(N+1)
    for p,v in h.items():
        log[p] = v
    K = kernel(h, m)
    correction = [K.get(n, Q(0)) for n in range(N+1)]
    output = formal_exp([a+b for a,b in zip(log,correction)])
    half_input = formal_exp([a/2+b/4 for a,b in zip(log,correction)])
    half_output = normalized_power(output, Q(1,2))
    dense = {'m': m, 'cutoff': N, 'output': list(map(str,output)),
             'input_half_root_output': list(map(str,half_input)),
             'output_half_root': list(map(str,half_output)),
             'log_bridge': formal_log(output)==[a+b for a,b in zip(log,correction)],
             'root_anomaly_detected': half_input != half_output}
    return {'records': rows, 'dense_ordinary_EXP_check': dense,
            'all_passed': all(all(row['checks'].values()) for row in rows) and dense['log_bridge'] and dense['root_anomaly_detected']}


def profiles():
    ps = primes(43)
    rows = []
    for m in (2,4,6,8,12,16):
        values = kernel({p:Q(1) for p in ps}, m)
        rows.append({'m':m, 'prime_input_cutoff':43,
                     'finite_prime_input_coefficients':{str(n):str(v) for n,v in sorted(values.items())},
                     'first_index':min(values), 'first_coefficient':str(values[min(values)]),
                     'sign_separation': all((v>0)==(isqrt(n)**2==n) for n,v in values.items())})
    return rows


def complete_prefix():
    rows=[]
    for m in (2,4):
        N=8192
        # Any face below N satisfies p**m<=N and d**(m+2)<=N/2**m.
        pmax=dmax=1
        while (pmax+1)**m<=N:
            pmax+=1
        while (dmax+1)**(m+2)<=N//2**m:
            dmax+=1
        cutoff=pmax+dmax
        K=kernel({p:Q(1) for p in primes(cutoff)},m)
        rows.append({'m':m,'encoded_cutoff':N,'complete_prime_input_cutoff':cutoff,
                     'coefficients':{str(n):str(v) for n,v in K.items() if n<=N}})
    return rows


def mask_grammar():
    # Finite-envelope discovery only. The universal bound for the selected
    # mask is a separate theorem in moment_proof.txt, not an extrapolation.
    rows=[]
    for gap_min in range(1,7):
        edges=[]
        for cutoff in (127,251):
            ps=primes(cutoff)
            eligible=[(float(Q(1,p*(q-p)))**.5+float(Q(1,q*(q-p)))**.5,p,q)
                      for p in ps for q in ps if q-p>=gap_min]
            top,p,q=max(eligible)
            excluded=sum(1 for p in ps for q in ps if 0<q-p<gap_min)
            edges.append({'prime_cutoff':cutoff,'maximum_half_line_envelope':top,
                          'maximizing_edge':[p,q],'edges_removed':excluded,'envelope_below_one':top<1})
        rows.append({'gap_minimum':gap_min,'training':edges[0],'held_out':edges[1]})
    selected=min(row['gap_minimum'] for row in rows if row['training']['envelope_below_one'] and row['held_out']['envelope_below_one'])
    return {'models_scored':len(rows),'records':rows,'smallest_stable_gap_mask':selected,
            'finite_floating_point_discovery_only':True,'universal_selected_mask_proof':'moment_proof.txt sections 4-5'}


def image_grammar(zeta):
    first={row['m']:row['first_index'] for row in zeta}
    fits=[]
    for A in range(1,17):
        for B in range(2,17):
            if all(A*B**m==first[m] for m in (2,4,6)):
                fits.append({'A':A,'B':B,'held_out_passed':all(A*B**m==first[m] for m in (8,12,16))})
    return {'models_scored':16*15,'training_orders':[2,4,6],'held_out_orders':[8,12,16],
            'fits':fits,'law':'first_index=4*6**m','coefficientwise_identity_limit':True}


def main():
    start=time.monotonic()
    g, laws, zeta = grammar(), exact_laws(), profiles()
    masks,images=mask_grammar(),image_grammar(zeta)
    passed = (laws['all_passed'] and all(row['sign_separation'] for row in zeta)
              and all(len(row['held_out_survivors'])==1 for row in g['bounded_search'])
              and all(row['all_lower_moments_zero'] and row['held_out_binomial_pattern'] for row in g['higher_order_linear_constraint_checks'])
              and masks['smallest_stable_gap_mask']==2 and images['fits']==[{'A':4,'B':6,'held_out_passed':True}])
    out = {'moment_annihilation_grammar':g, 'generic_shear_laws':laws,
           'finite_prime_input_zeta_profiles':zeta, 'complete_zeta_prefixes':complete_prefix(),
           'image_scale_fit':images,'gap_support_mask_grammar':masks,
           'ordinary_correction_absolute_domain_proved':'Re(s)>1/m',
           'paired_correction_domain_proved':'Re(s)>1/(m+1)',
           'gap_minimum':2, 'only_removed_prime_edge':[2,3],
           'counts_as_new_primitive':False, 'historical_novelty_established':False,
           'new_RH_estimate_proved':False, 'all_passed':passed, 'seconds':time.monotonic()-start}
    DEST.mkdir(exist_ok=True)
    (DEST/'moment_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Moment exact grammar and sparse shear:',passed,'seconds',out['seconds'],flush=True)
    assert passed


if __name__=='__main__':
    main()
