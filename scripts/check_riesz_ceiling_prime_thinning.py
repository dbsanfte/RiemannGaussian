#!/usr/bin/env python3
"""Independent finite-prime and exact-factorial replay of the thinning gate.

FLINT primality replaces the producer's sieve. Direct factorial powers
replace logarithmic gamma evaluation. No producer helper is imported.
This rejects any upgrade to complete-prime/cofinal ceiling credit.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

from flint import fmpz
import mpmath as mp
import numpy as np


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    assert data['parameters']['u'] == '10001/20000'
    assert data['parameters']['height'] == 54
    assert data['parameters']['insideTargetRadius'] is True
    assert data['allComputedRemovalAtomsZeroOrOne'] is True
    assert data['allRemovedAndRetainedLabelsGenuinePrimes'] is True
    for field in ['finiteRowsEstablishCofinalSource', 'allFloorsBallCertified',
                  'infiniteBinaryMomentBridgeLeanFormalized',
                  'completePrimeCeilingCounterexampleClaimed', 'independentCeilingProved',
                  'zeroExclusionProved', 'entryOrderCertified']:
        assert data[field] is False, field
    assert data['ceilingCredit'] == 0

    limit = data['parameters']['primeUpperCutoff']
    primes = np.array([n for n in range(2, limit+1) if fmpz(n).is_prime()], dtype=np.int64)
    assert len(primes) == data['finitePrimeCount']
    assert hashlib.sha256(primes.astype('<i8').tobytes()).hexdigest() == data['primeListSha256']
    u, y = 10001/20000, 54
    logs = np.log(primes.astype(float))
    raw = 4*np.exp(-(u-.5)*logs)*(1+np.cos(y*logs))
    clipped = np.minimum(1, raw)
    prefixes = np.cumsum(clipped)
    counts = np.floor(prefixes).astype(np.int64)
    removed = np.diff(counts, prepend=0)
    assert np.all((removed == 0) | (removed == 1))
    assert int(removed.sum()) == data['finiteBinaryRemovedCount']
    assert len(primes)-int(removed.sum()) == data['finiteBinaryRetainedCount']

    # A separate direct recurrence in the LOG powers includes k=0 and 1.
    originals, fractionals, binaries = [], [], []
    phase = np.cos(y*logs)-1j*np.sin(y*logs)
    kernel = u*logs/(primes.astype(float)**1.5)*phase
    for k in range(35):
        if k:
            kernel = kernel*(u*logs/k)
        originals.append(complex(np.sum(kernel)))
        fractionals.append(complex(np.sum(kernel*(1-clipped))))
        binaries.append(complex(np.sum(kernel*(1-removed))))
    for row in data['finiteMomentRows']:
        k = row['order']
        for key, reference in [('finiteCompletePrimeMoment',originals[k]),
                               ('finiteRetainedFractionalMoment',fractionals[k]),
                               ('finiteRetainedUnitPrimeMoment',binaries[k])]:
            assert abs(complex(*row[key])-reference) < 3e-12*(1+abs(reference)), (k,key)
        error = abs(binaries[k]-fractionals[k])
        price = 2*(k+1)*(1+abs(1.5+54j)/1.5)*(u/1.5)**(k+1)
        end = u**(k+1)*float(logs[-1])**(k+1)/math.factorial(k)*int(primes[-1])**(-1.5-54j)
        price += 2*abs(end)
        assert abs(row['finiteAbelPrice']-price) < 3e-12*(1+price)
        assert error <= price

    mp.mp.dps = 85
    U = mp.mpf(10001)/20000
    def evaluate(a, N):
        K = 13*N//32
        rational = Fraction(20000,10001)**N/(N+1)
        floor = rational.numerator//rational.denominator
        lam = float((N+1)/(U*2*mp.log(floor+2)))
        return (a[N]-sum(a[k-1]*a[N-k]/(N+1-k) for k in range(K+1,N-K+1))
                +lam*sum(a[k-1]*a[N+1-k]/(N+2-k) for k in range(1,N+2-K)))
    for row in data['finiteJoinedRows']:
        N = row['order']
        for key, a in [('finiteComplete',originals),('finiteFractional',fractionals),('finiteBinary',binaries)]:
            reference = evaluate(a, N)
            assert abs(complex(*row[key])-reference) < 3e-12*(1+abs(reference))
        rational = Fraction(20000,10001)**N/(N+1)
        assert row['exactMovingCutoffFloor'] == rational.numerator//rational.denominator
        restored = complex(*row['finiteFractional'])+sum(complex(*v)
                    for v in row['fractionalRestoration'].values())
        assert abs(restored-complex(*row['finiteComplete'])) < 3e-12*(1+abs(restored))

    # Check exact endpoint coefficients by counting incidences independently.
    for row in data['exactEndpointRows']:
        M, K = row['totalOrder'], row['prefixEndpoint']
        coeff = {}
        for k in range(M+1):
            key = tuple(sorted((k,M-k)))
            value = 1-int(k<=K)-int(k>=M-K)
            coeff[key] = coeff.get(key,0)+value
        assert coeff[(0,M)] == 0
        nonzero = sum(bool(v) for v in coeff.values())
        assert nonzero == row['collectedProducts']
    assert len(data['exactComponentRows']) == 72
    assert all(r['bothFactorialIndicesStayAttachedToTheirPrimeLeg'] and r['allOrderZeroEndpointsCancel']
               for r in data['exactComponentRows'])

    c = mp.log(mp.mpf(32)/13)/(-2*U*mp.log(U))-mp.log(mp.mpf(19)/13)
    assert abs(mp.mpf(data['fractionalCofinalSourceScalar'])-(-2+4*c)) < mp.mpf('1e-62')
    assert abs(mp.mpf(data['scalarReverseCeilingMargin'])-(-2+4*c-mp.mpf(42)/25)) < mp.mpf('1e-65')
    result = {'independentFlintPrimeCount': len(primes),
              'independentDirectFactorialRows': len(data['finiteMomentRows']),
              'independentJoinedRows': len(data['finiteJoinedRows']),
              'exactEndpointRows': len(data['exactEndpointRows']),
              'allFloatFloorsBallCertified': False,
              'infiniteBinaryWitnessCertified': False,
              'completePrimeCeilingCredit': 0}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
