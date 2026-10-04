#!/usr/bin/env python3
"""Optional integer-rounding control for the signed ceiling detector.

Integer atoms here are not the complete ordinary-prime set. The enumerable
control uses u=3/4, outside the target strip. Separate exact scalar rows
evaluate the derived rounding-error price at u=10001/20000; they do not
enumerate an astronomical carrier or certify a cofinal entry order.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.special import expi, gammaln


def tail_leg(z, k, T):
    return mp.exp(-z*T)*sum(mp.mpf(T)**j/mp.factorial(j)/z**(k-j+1)
                           for j in range(k+1))


def kernel(n, k, u, y):
    t = mp.log(n)
    return mp.mpf(u)**(k+1)*t**(k+1)/mp.factorial(k)*mp.exp(-mp.mpc('1.5', y)*t)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    mp.mp.dps = 85
    u, beta, y, B = .75, .75, 54., 8.
    M = 2**20
    first = int(np.exp(B))
    n = np.arange(first, M+1, dtype=np.int64)
    t = np.log(n.astype(float))
    cdf = expi(t)-float(expi(B))-4*np.real(
        expi((beta+1j*y)*t)-expi((beta+1j*y)*B))
    cdf[t < B] = 0
    counts = np.floor(cdf).astype(np.int64)
    weights = np.diff(counts, prepend=0)
    assert np.all((weights == 0) | (weights == 1))
    assert np.all(np.diff(cdf) >= 0)
    assert np.max(np.diff(cdf)) < 1
    assert int(weights.sum()) == int(counts[-1])

    # Independently replay the floor decisions nearest to an integer.
    # This is a sensitivity test, not a ball certificate for every row.
    active = np.flatnonzero(t >= B)
    fraction_distance = np.minimum(cdf-np.floor(cdf), np.ceil(cdf)-cdf)
    critical = active[np.argsort(fraction_distance[active])[:32]]
    floor_checks = []
    for i in critical:
        ti = mp.log(int(n[i]))
        z = mp.mpc(beta, y)
        value = mp.ei(ti)-mp.ei(B)-4*mp.re(mp.ei(z*ti)-mp.ei(z*B))
        assert int(mp.floor(value)) == int(counts[i])
        floor_checks.append({'integer': int(n[i]),
                             'absoluteCdfReplayError': mp.nstr(abs(value-float(cdf[i])), 25),
                             'floorAgrees': True})

    selected = n[weights == 1].astype(float)
    logs = np.log(selected)
    phase = np.exp(-1j*y*logs)
    rows = []
    for k in [0, 1, 2, 4, 8, 12, 16]:
        # The power is (log n)^(k+1), not n^(k+1).
        terms = np.exp((k+1)*np.log(u)+(k+1)*np.log(logs)
                       -gammaln(k+1)-1.5*logs)*phase
        atom = complex(np.sum(terms))
        for i in np.linspace(0, len(selected)-1, 9, dtype=int):
            ref = complex(kernel(int(selected[i]), k, u, y))
            assert abs(terms[i]-ref) <= 2e-11*abs(ref)+1e-25
        upper = mp.log(M)
        z0, z1, z2 = mp.mpc('.5', y), mp.mpf(u), mp.mpc(u, 2*y)
        continuous = mp.mpf(u)**(k+1)*(
            tail_leg(z0, k, B)-tail_leg(z0, k, upper)
            -2*(tail_leg(z1, k, B)-tail_leg(z1, k, upper))
            -2*(tail_leg(z2, k, B)-tail_leg(z2, k, upper)))
        price = (2*(k+1)*(1+abs(mp.mpc('1.5', y))/mp.mpf('1.5'))
                 *(mp.mpf(u)/mp.mpf('1.5'))**(k+1)+2*abs(kernel(M, k, u, y)))
        error = abs(mp.mpc(atom)-continuous)
        assert error <= price
        rows.append({'order': k,
                     'finiteUnitIntegerMoment': [atom.real, atom.imag],
                     'finiteContinuousMoment': [float(mp.re(continuous)), float(mp.im(continuous))],
                     'roundingError': mp.nstr(error, 40),
                     'statedFiniteAbelPrice': mp.nstr(price, 40)})

    target_u = F(10001, 20000)
    ratio = target_u / F(3, 2)
    assert ratio == F(10001, 30000) < F(1, 2)
    numeric_ratio = mp.mpf(ratio.numerator)/ratio.denominator
    target_price_constant = 2*(1+abs(mp.mpc('1.5', 54))/mp.mpf('1.5'))
    target_rows = []
    for N in [256, 640, 1536, 8192, 65536, 1048576]:
        target_rows.append({'order': N,
            'log10OfDerivedInfiniteRoundingPrice': mp.nstr(
                mp.log10(target_price_constant*(N+1))+(N+1)*mp.log10(numeric_ratio), 45),
            'literalTargetPrimeSumEvaluated': False})

    source_u = mp.mpf(10001)/20000
    retained = mp.log(mp.mpf(32)/13)/(-2*source_u*mp.log(source_u))-mp.log(mp.mpf(19)/13)
    source = -2+4*retained
    result = {
        'classification': 'Integer-rounding detector control; not ordinary primes',
        'controlParameters': {'u': '3/4', 'beta': '3/4', 'y': 54, 'lowerLogCutoff': 8,
                              'integerUpperCutoff': M, 'outsideTargetRadius': True},
        'integerAtoms': int(len(n)), 'selectedUnitAtoms': int(weights.sum()),
        'allComputedWeightsZeroOrOne': True,
        'cumulativeCountsTelescope': True,
        'allActualPrimesUsed': False,
        'primeSupportClaimed': False,
        'maximumComputedCdfIncrement': float(np.max(np.diff(cdf))),
        'minimumComputedDistanceToFloorBoundary': float(np.min(fraction_distance[active])),
        'criticalFloorReplays': floor_checks,
        'allFloorDecisionsBallCertified': False,
        'phase': 'exp(-(3/2+iy)*log(n))',
        'allLoggedOrdersIncludingZeroRetained': True,
        'finiteRows': rows,
        'targetScalarRatio': str(ratio),
        'targetRoundingPrice': '2*(k+1)*(1+abs(3/2+iy)/(3/2))*(u/(3/2))^(k+1)',
        'targetScalarRows': target_rows,
        'existingContinuousDoubleSource': mp.nstr(source, 70),
        'existingSourceAboveCeiling': mp.nstr(source-mp.mpf(42)/25, 70),
        'infiniteBinaryCounterexampleLeanFormalized': False,
        'independentCeilingProved': False, 'ceilingCredit': 0,
        'zeroExclusionProved': False, 'nativeEntryOrderCertified': False,
        'limitations': [
            'The enumerable control is outside the target radius and does not consist of all ordinary primes.',
            'Target rows price a derived rounding error; they do not enumerate target atoms.',
            'Floating floor replay is not a complete ball certificate.',
            'The infinite count-to-density Abel identification is an analytic argument, not a new checked arithmetic ceiling.',
            'A prime-specific identity or signed estimate is still required.',
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'integerAtoms': len(n), 'selectedUnitAtoms': int(weights.sum()),
                      'criticalFloorChecks': len(floor_checks),
                      'maximumFiniteMomentError': max(float(r['roundingError']) for r in rows),
                      'targetRatio': str(ratio), 'ceilingCredit': 0}))


if __name__ == '__main__':
    main()
