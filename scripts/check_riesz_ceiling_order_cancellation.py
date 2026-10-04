#!/usr/bin/env python3
"""Independent raw four-slot/Selberg replay of the optional ceiling probe."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from flint import fmpz
import mpmath as mp


def read_complex(x):
    return mp.mpc(x['re'], x['im'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('probe', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    mp.mp.dps = 120
    data = json.loads(args.probe.read_text())
    assert data['ceilingProved'] is False and data['zeroExclusion'] is False
    coefficient_checks = 0
    for row in data['exactChecks']['cases']:
        N, lam = row['N'], F(row['lambda'])
        K = 13*N//32
        assert row['commonOrders'] == N-2*K
        assert row['outerOrders'] == K+1
        for k in range(K+1, N-K+1):
            x, y = 1/F(N+1-k), lam/F(N+2-k)
            # Independent equivalent inequalities: 9*y<=13*x and
            # 9*x<=13*y imply the 2/11 price, retaining both orders.
            assert 9*y <= 13*x and 9*x <= 13*y
            coefficient_checks += 1
    worst = mp.mpf(0)
    for row in data['finitePrimeReplays']:
        N, primes, y = row['N'], row['primeUniverse'], row['height']
        u, K, s = mp.mpf(10001)/20000, 13*N//32, mp.mpf(3)/2+1j*y
        assert all(fmpz(p).is_prime() for p in primes)
        D = fmpz(20000)**N // ((N+1)*fmpz(10001)**N)
        L = 2*mp.log(mp.mpf(int(D+2)))
        assert abs(L-mp.mpf(row['literalMovingLength'])) < mp.mpf('1e-60')
        P = [sum(mp.log(p)**k/mp.factorial(k)*mp.exp(-s*mp.log(p)) for p in primes)
             for k in range(N+3)]
        H = [sum(mp.log(p)**(k+1)/mp.factorial(k)*mp.exp(-s*mp.log(p)) for p in primes)
             for k in range(N+1)]
        trace = sum(H[k]*H[N-1-k] for k in range(N))/N
        raw = (N+1)/2*sum(P[k]*P[N+1-k] for k in range(K+1, N+1-K))
        raw -= (N+1)*(N+2)/(2*L)*sum(P[k]*P[N+2-k] for k in range(K+1, N+2-K))
        raw -= (N+1)/L*sum(k*P[k]*P[N+2-k] for k in range(1, K+1))
        raw += trace
        full_selberg = -H[N]-trace
        whole = -u**(N+1)*(raw+full_selberg)
        saved = read_complex(row['normalizedMomentMain'])
        rel = abs(whole-saved)/max(abs(whole), abs(saved), mp.mpf('1e-1000'))
        assert rel < mp.mpf('1e-60')
        worst = max(worst, rel)
    for row in data['sourceRegressions']:
        assert row['independentCeilingProved'] is False
        assert row['belowFormalThreshold'] == (row['N'] < 65536)
        old, joined, removed = (mp.mpf(row[k]) for k in
            ('oldSeparateCentralPrice', 'exactJoinedCentralPrice', 'centralPriceRemoved'))
        assert abs(old-joined-removed) < mp.mpf('1e-60')
        if row['coefficientContractionApplicable']:
            assert joined <= mp.mpf(2)/11*old
            assert mp.mpf(row['contractedUpperEvaluation']) >= mp.mpf(row['exactJointSourceEvaluation'])
        else:
            assert row['contractedUpperEvaluation'] is None
        if row['multiplicity'] >= 2:
            assert mp.mpf(row['sourceLimit']) > mp.mpf(42)/25
    output = {'independentRawFourSlotReplay': True,
        'completeSelbergTraceCancelsBeforePricing': True,
        'exactCoefficientChecks': coefficient_checks,
        'genuinePrimeReplays': len(data['finitePrimeReplays']),
        'worstRelativeRawReplayError': mp.nstr(worst, 12),
        'literalLengthFloorRetained': True, 'ceilingProved': False,
        'sourceAndFiniteRegressionsNotPromotedToArithmeticBounds': True}
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(output))


if __name__ == '__main__':
    main()
