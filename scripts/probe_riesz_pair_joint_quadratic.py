#!/usr/bin/env python3
"""Optional unjoined factorial/Selberg bookkeeping and finite-prime replay.

The output preserves each leg's factorial order, orientation, common phase
and support signature before collection. It tests the newly paid whole
square correction, not the independent signed 399/5000 inequality. The
pure-selected-mode rows are synthetic null tests, not arithmetic evidence.
No discovery credit is assigned to a finite fixed prime universe.
"""

import argparse
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import itertools
import json
import math
from pathlib import Path

import mpmath as mp


def digest(path):
    return dict(path=str(path), sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest())


def raw(N, diagonal=False):
    M, K = N+1, 13*N//32
    records = []
    for left, right in ((0, 0),) if diagonal else ((0, 1), (1, 0)):
        def add(component, i, j, c=0, inv=0):
            records.append(dict(component=component, incidence=[left, right],
                factorialOrders=[i, j], support='complete-symmetric-finite-pairs',
                phaseIdentity='prime(p)^(-s)*prime(q)^(-s)',
                constant=str(F(c)), inverseL=str(F(inv))))
        for k in range(M+1):
            add('full_order_M', k, M-k, F(M, 2))
        for k in range(M+2):
            add('full_order_M_plus_one', k, M+1-k, inv=-F(M*(M+1), 2))
        for k in range(K+1):
            add('prefix_unlogged', M-k, k, -M)
            add('prefix_shifted_log', M-k+1, k, inv=M*(M-k+1))
        # The Selberg pair subtraction is a POSITIVE logged convolution.
        # Neither of its logged legs has ordinary-prime order zero.
        for k in range(N):
            add('selberg_pair_trace', k+1, N-k, F((k+1)*(N-k), N))
    return records


def collect(records):
    grouped = defaultdict(lambda: [F(0), F(0)])
    for row in records:
        key = (row['support'], tuple(sorted(zip(row['incidence'], row['factorialOrders']))))
        grouped[key][0] += F(row['constant'])
        grouped[key][1] += F(row['inverseL'])
    return grouped


def expected(N, diagonal, key):
    M, K = N+1, 13*N//32
    (_, i), (_, j) = key[1]
    lo = min(i, j)
    symmetry = F(1, 2) if diagonal and i == j else F(1)
    if i+j == M:
        return (symmetry*((M if K < lo else 0)+F(2*i*j, N)), F(0))
    assert i+j == M+1
    return F(0), -symmetry*M*(M+1) if K < lo else -F(M*lo)


def exact_checks():
    checks, templates = [], []
    for N in (*range(1, 97), 256, 640, 1536, 3584, 8192):
        for diagonal in (False, True):
            records, M, K = raw(N, diagonal), N+1, 13*N//32
            grouped = collect(records)
            for key, coefficients in grouped.items():
                assert tuple(coefficients) == expected(N, diagonal, key)
            endpoints = [key for key in grouped if any(i == 0 for _, i in key[1])]
            assert endpoints and all(grouped[key] == [0, 0] for key in endpoints)
            selberg = collect([r for r in records if r['component'] == 'selberg_pair_trace'])
            assert all(c > 0 and inv == 0 for c, inv in selberg.values())
            assert all(all(i > 0 for _, i in key[1]) for key in selberg)
            checks.append(dict(N=N, repeatedPrimeDiagonal=diagonal, rawTerms=len(records),
                collectedMonomials=len(grouped), exactlyZeroEndpoints=len(endpoints),
                selbergMonomials=len(selberg), selbergCoefficientsStrictlyPositive=True,
                unloggedCentralRetained=True, successorAndLoggedTermsRetained=True))
            if N in (1, 8, 256):
                templates.append(dict(N=N, repeatedPrimeDiagonal=diagonal, raw=records))
    # Regressions must catch omissions, incorrect signs and mask identification.
    records = raw(8)
    wrong = [dict(r, constant=str(-F(r['constant']))) if
             r['component'] == 'selberg_pair_trace' else r for r in records]
    assert collect(records) != collect(wrong)
    different = [dict(r, support='unpaid-different-mask') if
                 r['component'] == 'selberg_pair_trace' else r for r in records]
    assert collect(records) != collect(different)
    return dict(checks=checks, templates=templates, exactRationalArithmetic=True,
        wrongSelbergSignRejected=True, differingMasksNotIdentified=True,
        everyZeroOrderEndpointCancels=True, selbergReinforcesOrderM=True)


def lower(M, K, q):
    return sum(math.comb(M, k)*q**k*(1-q)**(M-k) for k in range(K+1))


def encode(value):
    return dict(re=mp.nstr(mp.re(value), 85), im=mp.nstr(mp.im(value), 85))


def finite_prime_checks():
    primes = [2, 3, 5, 7, 11, 97, 257, 1009, 5003, 9973, 100003]
    assert all(p>1 and all(p%d for d in range(2, math.isqrt(p)+1)) for p in primes)
    mp.mp.dps = 90
    rows = []
    for N, u, y in itertools.product((1, 4, 8, 16, 32, 64),
                                    (mp.mpf(1)/2, mp.mpf(10001)/20000), (0, 54, 142)):
        M, K, L = N+1, 13*N//32, mp.mpf(7)*(N+1)/5
        s = mp.mpf(3)/2+1j*y
        moments = [sum(mp.log(p)**k/mp.factorial(k)*mp.exp(-s*mp.log(p))
                       for p in primes) for k in range(N+3)]
        H = [sum(mp.log(p)**(k+1)/mp.factorial(k)*mp.exp(-s*mp.log(p))
                 for p in primes) for k in range(N)]
        parts = dict(central=M/2*sum(moments[k]*moments[M-k] for k in range(K+1, M-K)),
            successor=-M*(M+1)/(2*L)*sum(moments[k]*moments[M+1-k]
                                            for k in range(K+1, M+1-K)),
            logged=-M/L*sum(k*moments[k]*moments[M+1-k] for k in range(1, K+1)),
            selbergTrace=sum(H[k]*H[N-1-k] for k in range(N))/N)
        quadratic = sum(parts.values())
        sq = [sum(mp.log(p)*(2*mp.log(p))**k/mp.factorial(k)*mp.exp(-s*2*mp.log(p))
                  for p in primes) for k in (N, N+1)]
        f = lower(M, K, mp.mpf(1)/2)
        diagonal = (2*f-mp.mpf(3)/2)*sq[0]+M/L*(1-f)*sq[1]
        direct, selberg, prefix_diagonal = 0j, 0j, 0j
        for p, q in itertools.combinations(primes, 2):
            x, z, T = mp.log(p), mp.log(q), mp.log(p*q)
            fx, fz = lower(M, K, x/T), lower(M, K, z/T)
            Q = T*(1-T/L)-T/L*((L-x)*fz+(L-z)*fx)
            S = -2*x*z/T
            kernel = T**N/mp.factorial(N)*mp.exp(-s*T)
            direct += (Q-S)*kernel
            selberg += S*kernel
        for p in primes:
            x = mp.log(p)
            Q = 2*(1-2*f)*x+4/L*(f-1)*x*x
            prefix_diagonal += Q*(2*x)**N/mp.factorial(N)*mp.exp(-s*2*x)/2
        selberg_error = abs(selberg+parts['selbergTrace']-sq[0]/2)
        diag_error = abs(diagonal+prefix_diagonal+sq[0]/2)
        joined_error = abs(u**M*(direct-quadratic-diagonal))
        finite_mass = sum(mp.log(n)/mp.mpf(n)**(mp.mpf(3)/2) for n in primes)
        square_budget = mp.mpf(17)/6*u*finite_mass*(4*u/3)**N
        assert abs(u**M*diagonal) <= square_budget
        assert max(selberg_error, diag_error, joined_error) < mp.mpf('1e-70')
        if N == 1 and y == 0:
            assert abs(u**M*(direct-quadratic)) > mp.mpf('1e-3')
            assert abs(u**M*(direct-quadratic-2*diagonal)) > mp.mpf('1e-3')
        rows.append(dict(N=N, u=mp.nstr(u, 40), y=y, finitePrimeUniverse=primes,
            regressionLength='7*(N+1)/5; generic algebra, not literal moving length',
            sourceScaledDirect=encode(u**M*direct), sourceScaledQuadratic=encode(u**M*quadratic),
            sourceScaledJoinedSquare=encode(u**M*diagonal),
            sourceScaledParts={k: encode(u**M*v) for k, v in parts.items()},
            finiteSquareBudget=mp.nstr(square_budget, 80),
            exactSelbergError=float(selberg_error), exactDiagonalError=float(diag_error),
            joinedReplayError=float(joined_error), belowFormalThreshold=True))
    return rows


def pure_selected_model():
    """Algebraic null test: W_k=-1, with the literal moving length.

    This is NOT a prime population or an independent floor estimate. It
    prevents mistaking the joined coefficient cancellation for a universal
    399/5000 bound on arbitrary moment arrays.
    """
    mp.mp.dps = 90
    rows = []
    for N in (256, 640, 1536, 3584, 8192, 18432, 40960, 90112, 196608, 425984):
        for num, den in ((1, 2), (10001, 20000)):
            u, M, K = mp.mpf(num)/den, N+1, 13*N//32
            D = den**N//((N+1)*num**N)
            L = 2*mp.log(D+2)
            parts = dict(central=mp.harmonic(M-K-1)-mp.harmonic(K),
                successor=-M/(L*u)*(mp.harmonic(M-K)-mp.harmonic(K)),
                logged=-M/(L*u)*(mp.harmonic(M)-mp.harmonic(M-K)),
                selbergTrace=mp.mpf(1))
            value = sum(parts.values())
            limit = 1+mp.log(mp.mpf(19)/13)-mp.log(mp.mpf(32)/13)/(-2*u*mp.log(u))
            assert limit > mp.mpf(399)/5000
            rows.append(dict(N=N, u=mp.nstr(u, 40), length=mp.nstr(L, 80),
                hypotheticalPureSelectedParts={k: mp.nstr(v, 80) for k, v in parts.items()},
                hypotheticalPureSelectedValue=mp.nstr(value, 80), sourceLimit=mp.nstr(limit, 80),
                contradictionMargin=mp.nstr(limit-mp.mpf(399)/5000, 80),
                sourceLimitMinusValue=mp.nstr(limit-value, 80), literalPrimePopulation=False,
                independentArithmeticBound=False, cofinalFloorCredit=0))
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-joint-quadratic/probe.json'))
    args = ap.parse_args()
    result = dict(sources=[digest(p) for p in (
            'scripts/probe_riesz_pair_joint_quadratic.py',
            'RiemannGaussian/ZetaRieszPairJointQuadratic.lean')],
        exactAlgebra=exact_checks(), finitePrimeRegressions=finite_prime_checks(),
        pureSelectedModeNullTest=pure_selected_model(), sourceNormalizationUsed=True,
        finiteSampleIsExhaustiveLiteralCarrier=False, optionalOutsideCI=True,
        independentSignedMainBoundProved=False, floorCredit=0)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(exactCases=len(result['exactAlgebra']['checks']),
        finitePrimeCases=len(result['finitePrimeRegressions']),
        maxReplayError=max(r['joinedReplayError'] for r in result['finitePrimeRegressions']),
        selectedModeIsSynthetic=True, independentSignedMainBound=False, floorCredit=0)))


if __name__ == '__main__':
    main()
