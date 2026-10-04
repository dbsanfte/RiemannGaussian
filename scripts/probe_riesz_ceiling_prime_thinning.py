#!/usr/bin/env python3
"""Genuine-prime thinning control, not a bound for complete primes.

All numerical prime rows are finite, at the target radius and fixed y=54.
The cofinal fractional control is proved separately in Lean. Binary rows
test cumulative rounding only; no infinite binary witness is claimed.
Exact factorial endpoint bookkeeping precedes numerical evaluation.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.special import gammaln

from probe_riesz_pair_algebra import raw_terms, survivor_terms, collect, equal_collections


def primes_to(limit):
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(limit ** .5) + 1):
        if sieve[p]:
            sieve[p*p::p] = False
    return np.flatnonzero(sieve)


def endpoint_audit(M, K):
    """Collect products by BOTH factorial indices, including swaps/diagonal."""
    def collect(orders, amount, bag):
        for k in orders:
            key = tuple(sorted((k, M-k)))
            bag[key] = bag.get(key, Fraction(0)) + amount
    bag = {}
    collect(range(M+1), Fraction(1), bag)
    collect(range(K+1), Fraction(-1), bag)
    collect(range(M-K, M+1), Fraction(-1), bag)
    middle = {}
    collect(range(K+1, M-K), Fraction(1), middle)
    bag = {key: value for key, value in bag.items() if value}
    assert bag == middle
    assert (0, M) not in bag
    return {'totalOrder': M, 'prefixEndpoint': K,
            'collectedProducts': len(bag), 'exactEndpointCancellation': True,
            'swappedIncidencesCollected': True,
            'diagonalMultiplicity': int(bag.get((M//2, M//2), 0)) if M % 2 == 0 else 0}


def joined(a, N, u):
    K = 13*N//32
    # EXACT repo length log((floor(u^(-N)/(N+1))+2)^2).
    # The target radius is rational, so its cutoff floor is exact here.
    cutoff_ratio = Fraction(20000, 10001)**N / (N+1)
    cutoff = cutoff_ratio.numerator // cutoff_ratio.denominator
    length = 2*mp.log(cutoff + 2)
    lam = (N+1)/(mp.mpf(u)*length)
    central = sum(a[k-1]*a[N-k]/(N+1-k) for k in range(K+1, N-K+1))
    prefix = sum(a[k-1]*a[N+1-k]/(N+2-k) for k in range(1, N+2-K))
    return a[N]-central+float(lam)*prefix


def restoration(retained, removed, N, u):
    K = 13*N//32
    cutoff_ratio = Fraction(20000, 10001)**N / (N+1)
    cutoff = cutoff_ratio.numerator // cutoff_ratio.denominator
    lam = float((N+1)/(mp.mpf(u)*2*mp.log(cutoff+2)))
    cross = -sum((retained[k-1]*removed[N-k]+removed[k-1]*retained[N-k])/(N+1-k)
                 for k in range(K+1, N-K+1))
    cross += lam*sum((retained[k-1]*removed[N+1-k]+removed[k-1]*retained[N+1-k])/(N+2-k)
                     for k in range(1, N+2-K))
    return {'removedLinear': encode(removed[N]),
            'removedQuadratic': encode(joined(removed, N, u)-removed[N]),
            'retainedRemovedCross': encode(cross)}


def encode(z):
    return [float(z.real), float(z.imag)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prime-limit', type=int, default=2**20)
    args = parser.parse_args()
    mp.mp.dps = 85
    component_rows = []
    for N in (*range(33), 256, 640, 1536):
        for diagonal in (False, True):
            raw_terms_N, survivors_N = raw_terms(N, diagonal), survivor_terms(N, diagonal)
            original_terms, joined_terms = collect(raw_terms_N), collect(survivors_N)
            assert equal_collections(original_terms, joined_terms)
            endpoints = [key for key in original_terms if any(order == 0 for _, order in key[1])]
            assert endpoints and all(original_terms[key] == (0, 0) for key in endpoints)
            component_rows.append({'order': N, 'oneRepeatedPrimeDiagonal': diagonal,
                                   'rawComponentTerms': len(raw_terms_N),
                                   'survivingCollectedProducts': len(joined_terms),
                                   'allOrderZeroEndpointsCancel': True,
                                   'bothFactorialIndicesStayAttachedToTheirPrimeLeg': True})
    u, y = 10001/20000, 54.
    p = primes_to(args.prime_limit)
    logs = np.log(p.astype(float))
    raw = 4*np.exp(-(u-.5)*logs)*(1+np.cos(y*logs))
    clipped = np.minimum(1., raw)
    assert np.all(clipped >= 0) and np.all(clipped <= 1)
    cdf = np.cumsum(clipped)
    floor = np.floor(cdf).astype(np.int64)
    removal = np.diff(floor, prepend=0)
    assert np.all((removal == 0) | (removal == 1))
    assert int(removal.sum()) == int(floor[-1])
    assert np.all((cdf-floor >= 0) & (cdf-floor < 1))
    assert np.all(p[np.flatnonzero(removal)] >= 2)

    distance = np.minimum(cdf-floor, floor+1-cdf)
    critical = np.argsort(distance)[:24]
    replay_targets = set(int(i) for i in critical)
    # One high-precision cumulative pass, not 24 repeated summations.
    replay, mp_cdf = [], mp.mpf(0)
    for i, prime in enumerate(p):
        t = mp.log(int(prime))
        rw = 4*mp.exp(-(mp.mpf(10001)/20000-mp.mpf('.5'))*t)*(1+mp.cos(54*t))
        mp_cdf += min(mp.mpf(1), rw)
        if i in replay_targets:
            assert int(mp.floor(mp_cdf)) == int(floor[i])
            replay.append({'prime': int(prime), 'primeIndex': i,
                           'floorAgrees': True,
                           'cdfReplayError': mp.nstr(abs(mp_cdf-float(cdf[i])), 30)})
        if i >= max(replay_targets):
            break

    original, fractional, binary = [], [], []
    kernel_checks, rows = [], []
    s0 = 1.5+1j*y
    spot = np.linspace(0, len(p)-1, 9, dtype=int)
    for k in range(35):
        kernel = np.exp((k+1)*np.log(u)+(k+1)*np.log(logs)
                        -gammaln(k+1)-1.5*logs)*np.exp(-1j*y*logs)
        original.append(complex(np.sum(kernel)))
        fractional.append(complex(np.sum((1-clipped)*kernel)))
        binary.append(complex(np.sum((1-removal)*kernel)))
        if k not in (0, 1, 2, 4, 8, 12, 16, 24, 32):
            continue
        for i in spot:
            t = mp.log(int(p[i]))
            ref = (mp.mpf(10001)/20000)**(k+1)*t**(k+1)/mp.factorial(k)*mp.exp(-mp.mpc('1.5', 54)*t)
            assert abs(kernel[i]-complex(ref)) <= 3e-12*abs(complex(ref))+1e-30
            kernel_checks.append({'order': k, 'prime': int(p[i]), 'agrees': True})
        # Raw three-centre identity: full log factorial kernel, not n^k.
        def tilted(phase):
            return np.exp((k+1)*np.log(u)+(k+1)*np.log(logs)
                          -gammaln(k+1)-(1+u)*logs)*np.exp(-1j*phase*logs)
        raw_sum = complex(np.sum(raw*kernel))
        three_sum = complex(np.sum(4*tilted(y)+2*tilted(0)+2*tilted(2*y)))
        assert abs(raw_sum-three_sum) <= 2e-11*(1+abs(raw_sum))
        error = abs(binary[k]-fractional[k])
        # Bounded cumulative discrepancy and the explicit finite endpoint.
        price = (2*(k+1)*(1+abs(s0)/1.5)*(u/1.5)**(k+1)
                 +2*abs(kernel[-1]))
        assert error <= price
        rows.append({'order': k, 'finiteCompletePrimeMoment': encode(original[k]),
                     'finiteRetainedFractionalMoment': encode(fractional[k]),
                     'finiteRetainedUnitPrimeMoment': encode(binary[k]),
                     'binaryFractionalError': error, 'finiteAbelPrice': price,
                     'rawThreeCentreIdentityError': abs(raw_sum-three_sum)})

    endpoint_rows = [endpoint_audit(M, 13*(M-1)//32) for M in range(2, 129)]
    joint_rows = [{'order': N, 'finiteComplete': encode(joined(original, N, u)),
                   'finiteFractional': encode(joined(fractional, N, u)),
                   'finiteBinary': encode(joined(binary, N, u)),
                   'exactMovingCutoffFloor': (Fraction(20000,10001)**N/(N+1)).__floor__(),
                   'fractionalRestoration': restoration(fractional,
                       [a-b for a,b in zip(original,fractional)],N,u),
                   'allEndpointsAndOneDiagonalRetained': True}
                  for N in (2, 4, 8, 12, 16, 24, 32)]
    for row in joint_rows:
        pieces = row['fractionalRestoration']
        restored = complex(*row['finiteFractional'])+sum(complex(*v) for v in pieces.values())
        assert abs(restored-complex(*row['finiteComplete'])) < 2e-12*(1+abs(restored))
    U = mp.mpf(10001)/20000
    retained = mp.log(mp.mpf(32)/13)/(-2*U*mp.log(U))-mp.log(mp.mpf(19)/13)
    result = {
        'classification': 'Genuine-prime thinning detector control; not complete prime coverage',
        'parameters': {'u': '10001/20000', 'height': 54,
                       'primeUpperCutoff': args.prime_limit, 'insideTargetRadius': True},
        'finitePrimeCount': len(p), 'finiteBinaryRemovedCount': int(removal.sum()),
        'finiteBinaryRetainedCount': int(len(p)-removal.sum()),
        'primeListSha256': hashlib.sha256(p.astype('<i8').tobytes()).hexdigest(),
        'rawWeight': '4*p^(-(u-1/2))*(1+cos(y*log(p)))',
        'fractionalRemovalWeight': 'min(1,rawWeight)',
        'unitRemovalRule': 'floor(sum_{q<=p} clippedWeight(q))-floor(sum_{q<p} clippedWeight(q))',
        'allComputedRemovalAtomsZeroOrOne': True,
        'allRemovedAndRetainedLabelsGenuinePrimes': True,
        'completePrimeSetUsedForFiniteReferenceOnly': True,
        'cdfDiscrepancyBound': 1, 'criticalFloorReplays': replay,
        'allFloorsBallCertified': False, 'kernelSpotChecks': kernel_checks,
        'finiteMomentRows': rows, 'finiteJoinedRows': joint_rows,
        'exactEndpointRows': endpoint_rows, 'exactComponentRows': component_rows,
        'fractionalCofinalSourceFromLean': '-2+4*retainedCost(10001/20000)',
        'fractionalCofinalSourceScalar': mp.nstr(-2+4*retained, 65),
        'scalarReverseCeilingMargin': mp.nstr(-2+4*retained-mp.mpf(42)/25, 65),
        'finiteRowsEstablishCofinalSource': False,
        'infiniteBinaryMomentBridgeLeanFormalized': False,
        'completePrimeCeilingCounterexampleClaimed': False,
        'independentCeilingProved': False, 'ceilingCredit': 0,
        'zeroExclusionProved': False, 'entryOrderCertified': False,
        'limitations': [
            'Thinning omits a source-sized component of the complete prime measure.',
            'Finite rows do not approach or certify the eventual source crossing.',
            'The binary infinite Abel bridge is not inferred from floating rounding.',
            'All finite factorial endpoints, phase and one diagonal stay in the joined evaluator.',
            'The cofinal fractional control is a negative test of a generic method, not an arithmetic payment.',
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'finitePrimeCount': len(p), 'binaryRemoved': int(removal.sum()),
                      'floorReplays': len(replay), 'endpointAudits': len(endpoint_rows),
                      'cofinalCeilingCredit': 0}))


if __name__ == '__main__':
    main()
