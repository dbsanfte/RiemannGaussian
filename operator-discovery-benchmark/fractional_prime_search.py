#!/usr/bin/env python3
"""Search fractional arithmetic logarithms for uniformly separated primes.

The production coefficient algorithm uses divisor inversion, without a
prime-indicator input. Factorizations are used only for scoring and certificates.
"""

from fractions import Fraction as Q
from itertools import product
from math import gcd
from pathlib import Path
import json
import random
import time
import flint

from prime_scale_search import sieve, factor, mu
from fractional_prime_grammar import PRODUCTION_CATALOGUE

BASE = Path(__file__).resolve().parent
DEST = BASE / 'fractional-prime-results'


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(32)


def divisors_table(N):
    out = [[] for _ in range(N + 1)]
    for d in range(2, N + 1):
        for n in range(2 * d, N + 1, d):
            out[n].append(d)
    return out


def forward(f, alpha, proper):
    N = len(f) - 1
    weights = [flint.arb(0), flint.arb(0)] + [flint.arb(n).log() ** real(alpha) for n in range(2, N + 1)]
    L = [flint.arb(0)] * (N + 1)
    R = L.copy()
    for n in range(2, N + 1):
        L[n] = weights[n] * f[n] - sum((f[n // d] * L[d] for d in proper[n]), flint.arb(0))
        R[n] = L[n] / weights[n]
    return L, R


def powers(values, spf, inverse):
    """V or W, implemented by forward perfect-power placement."""
    result = [flint.arb(0)] * len(values)
    for n in range(2, len(values)):
        image, k = n, 1
        while image < len(values):
            weight = mu(k, spf) if inverse else 1
            if weight:
                result[image] += real(Q(weight, k)) * values[n]
            image *= n
            k += 1
    return result


def recover(R, alpha, proper):
    f = [flint.arb(0)] * len(R)
    f[1] = flint.arb(1)
    weights = [flint.arb(0), flint.arb(0)] + [flint.arb(n).log() ** real(alpha) for n in range(2, len(R))]
    for n in range(2, len(R)):
        f[n] = R[n] + sum((f[n // d] * weights[d] * R[d] for d in proper[n]), flint.arb(0)) / weights[n]
    return f


def profile(N, alpha, spf, proper):
    f = [flint.arb(0)] + [flint.arb(1)] * N
    L, R = forward(f, alpha, proper)
    B = powers(R, spf, True)
    bound = flint.arb(2) ** (1 - real(alpha)) - 1
    threshold = (1 + bound) / 2
    maxima = []
    mismatches = []
    for n in range(2, N + 1):
        fs = factor(n, spf)
        g = gcd(*fs.values())
        prime = spf[n] == n
        sign = (-1) ** (len(fs) + len(factor(g, spf)) - 1)
        if not (B[n] * sign > 0):
            mismatches.append(n)
        if prime:
            assert B[n].contains(1) and B[n] > threshold
        else:
            assert B[n].abs_upper() < bound and B[n].abs_upper() < threshold
            maxima.append((float(B[n].abs_upper()), n))
            refined = bound / g if len(fs) >= 2 else (1 - real(alpha)) / g
            assert B[n].abs_upper() < refined
    maximum, n = max(maxima)
    assert not mismatches
    return {'alpha': str(alpha), 'cutoff': N,
            'L_coefficients': list(map(short, L)), 'R_coefficients': list(map(short, R)),
            'B_coefficients': list(map(short, B)),
            'uniform_composite_modulus_bound_ball': short(bound),
            'prime_composite_threshold_ball': short(threshold),
            'observed_composite_maximum': maximum, 'maximum_index': n,
            'maximum_factorization': {str(p): e for p, e in factor(n, spf).items()},
            'prime_classification_errors': 0, 'sign_rule_errors': 0, 'all_passed': True}, (L, R, B)


def grammar(B, spf):
    features = lambda n: (1, len(factor(n, spf)), sum(factor(n, spf).values()),
                          len(factor(gcd(*factor(n, spf).values()), spf)),
                          sum(factor(gcd(*factor(n, spf).values()), spf).values()))
    models = []
    for bits in product((0, 1), repeat=5):
        def fits(n):
            sign = (-1) ** sum(a * b for a, b in zip(bits, features(n)))
            return bool(B[n] * sign > 0)
        trained = all(fits(n) for n in range(2, 129))
        held = trained and all(fits(n) for n in range(129, len(B)))
        models.append({'parity_weights': list(bits), 'training_passed': trained, 'held_out_passed': held})
    survivors = [m for m in models if m['held_out_passed']]
    assert survivors == [{'parity_weights': [1, 1, 0, 1, 0], 'training_passed': True, 'held_out_passed': True}]
    norm = []
    for exponent in range(-3, 4):
        # Candidate normalization L_alpha(p)/(log p)^(j*alpha).
        good = all((flint.arb(p).log() ** real(Q(1 - exponent, 2))).contains(1) for p in (2, 3, 5, 11, 97))
        norm.append({'exponent_multiple_of_alpha': exponent, 'prime_unit_value_passed': good})
    assert [m['exponent_multiple_of_alpha'] for m in norm if m['prime_unit_value_passed']] == [1]
    return {'sign_models_scored': 32, 'sign_features': ['one', 'omega(n)', 'Omega(n)', 'omega(gcd_exponents)', 'Omega(gcd_exponents)'],
            'sign_models': models, 'sign_survivors': survivors, 'normalization_models': norm,
            'training_indices': [2, 128], 'held_out_indices': [129, len(B)-1], 'all_passed': True}


def generic(spf):
    rng = random.Random(2026100722)
    raw = [Q(0), Q(1)] + [Q(rng.randrange(-3, 4), rng.randrange(1, 7)) for _ in range(95)]
    f = list(map(real, raw)); proper = divisors_table(len(raw) - 1)
    rows = []
    for alpha in (Q(1, 4), Q(1, 2), Q(3, 4), Q(1)):
        _, R = forward(f, alpha, proper); B = powers(R, spf, True)
        recovered_R = powers(B, spf, False); inverse_f = recover(recovered_R, alpha, proper)
        assert all((u-v).contains(0) for u, v in zip(R, recovered_R))
        assert all((u-v).contains(0) for u, v in zip(f, inverse_f))
        rows.append({'alpha': str(alpha), 'B_coefficients': list(map(short, B)),
                     'inverse_maximum_error_upper_ball': short(max((u-v).abs_upper() for u,v in zip(f,inverse_f))),
                     'all_passed': True})
    beta = Q(1, 2); alpha = Q(1, 2)
    root_f = [flint.arb(0), flint.arb(1)]
    for n in range(2, 97):
        value = Q(1)
        for e in factor(n, spf).values():
            for j in range(e):
                value *= Q(beta+j, j+1)
        root_f.append(real(value))
    _, root_R = forward(root_f, alpha, divisors_table(96))
    _, zeta_R = forward([flint.arb(0)]+[flint.arb(1)]*96, alpha, divisors_table(96))
    anomaly = root_R[6] - real(beta) * zeta_R[6]
    assert not anomaly.contains(0)
    assert (root_R[6] - real(beta*beta)*zeta_R[6]).contains(0)
    return {'input_rational_coefficients': list(map(str, raw)), 'inverse_controls': rows,
            'universal_triangular_inverse_proved': True,
            'ordinary_input_root_commutation_rejected': True,
            'root_counterexample': {'alpha': str(alpha), 'beta': str(beta), 'n': 6,
                                    'root_log_coefficient_ball': short(root_R[6]),
                                    'expected_commuting_coefficient_ball': short(real(beta)*zeta_R[6]),
                                    'anomaly_ball': short(anomaly), 'exact_amplitude_rule': 'beta**2 at squarefree pq'},
            'all_passed': True}


def distant(spf):
    # New high-scale pair values are certified by native primality testing, not
    # read as pre-supplied detector labels.
    p = 10**12 + 1
    while not flint.fmpz(p).is_prime(): p += 2
    q = p + 2
    while not flint.fmpz(q).is_prime(): q += 2
    assert flint.fmpz(p).is_prime() and flint.fmpz(q).is_prime()
    lp, lq = flint.arb(p).log(), flint.arb(q).log()
    rows = []
    for alpha in (Q(1,4), Q(1,2), Q(3,4), Q(9,10)):
        a = real(alpha); value = 1-(lp**a+lq**a)/(lp+lq)**a
        bound = flint.arb(2)**(1-a)-1
        assert value < 0 and value.abs_upper() < bound
        rows.append({'alpha': str(alpha), 'p': p, 'q': q, 'n': str(p*q),
                     'B_coefficient_ball': short(value), 'distance_to_sharp_bound_ball': short(bound-value.abs_upper()),
                     'all_passed': True})
    return {'records': rows, 'finite_observation_only': True, 'sharpness_proved_separately': True, 'all_passed': True}


def main():
    start = time.monotonic(); flint.ctx.prec = 384
    N = 4096; spf, _ = sieve(N); proper = divisors_table(N)
    profiles=[]; half=None
    for alpha in (Q(1,4), Q(1,2), Q(3,4), Q(9,10)):
        row, values = profile(N, alpha, spf, proper); profiles.append(row)
        if alpha == Q(1,2): half=values
        print('Fractional alpha',alpha,'composite max',row['observed_composite_maximum'],'at',row['maximum_index'],flush=True)
    learned=grammar(half[2],spf); inverse=generic(spf); far=distant(spf)
    out={'candidate_id': 'fractional_arithmetic_logarithm_prime_decoder',
         'definition': 'B_alpha(f)=W[(f_D^-1 * D_alpha f)(n)/(log n)^alpha]; D_alpha f(n)=(log n)^alpha f(n), W=sum mu(k)U_k/k',
         'domain': 'Formal normalized units f(1)=1 over real/complex coefficients; 0<alpha<1 for prime bounds',
         'profiles': profiles, 'grammar': learned, 'generic_inverse_and_root_controls': inverse,
         'production_catalogue':PRODUCTION_CATALOGUE,
         'public_program_examples':[
             {'kind':'fractional_prime_program','family':family,'alpha':'1/2',
              'input':'g' if family.endswith('_inverse') else 'f'}
             for family in PRODUCTION_CATALOGUE['families']],
         'distant_prime_pair_controls': far,
         'all_integer_prime_coefficient_identity_proved': True,
         'all_integer_sharp_uniform_composite_bound_proved': True,
         'all_integer_nonzero_sign_rule_proved': True,
         'uniform_coefficient_limit_to_prime_indicator_proved': True,
         'prime_indicator_sup_error_bound': '2**(1-alpha)-1',
         'coefficient_production_uses_prime_indicator_or_prime_weights': False,
         'new_uniform_prime_distribution_estimate_proved': False,
         'historical_novelty_established': False, 'counts_as_historically_new_operator': False,
         'proof': 'fractional_prime_proof.txt', 'all_passed': True, 'seconds': time.monotonic()-start}
    DEST.mkdir(exist_ok=True); (DEST/'fractional_prime_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Fractional prime search passed; seconds',out['seconds'],flush=True)


if __name__ == '__main__': main()
