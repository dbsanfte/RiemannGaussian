#!/usr/bin/env python3
"""Independent recurrence/phase replay; imports no numerical producer."""

import argparse
from decimal import Decimal, localcontext
import hashlib
import itertools
import json
from pathlib import Path

import mpmath as mp


def lower_tail(M, K, x):
    value, total = (1-x)**M, mp.mpf(0)
    for k in range(K+1):
        total += value
        value *= (M-k)*x/((k+1)*(1-x))
    return total


def decode(value):
    return mp.mpc(value['re'], value['im'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path('.lake/riesz-pair-whole-completion/probe.json'))
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-whole-completion/validation.json'))
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    mp.mp.dps = 110
    errors = []
    for row in data['finitePrimeRegressions']:
        N, u, y = row['N'], mp.mpf(row['u']), row['y']
        L, s, width = mp.mpf(7)*(N+1)/5, mp.mpf(3)/2+1j*y, 2*mp.pi/abs(y)
        full, kept, exterior_A, exterior_B, count = 0j, 0j, 0j, 0j, 0
        for p, q in itertools.combinations(row['finitePrimeUniverse'], 2):
            # Separate prime phases provide an independent product-phase replay.
            x, z, T = mp.log(p), mp.log(q), mp.log(p*q)
            fx, fz = lower_tail(N+1, 13*N//32, x/T), lower_tail(N+1, 13*N//32, z/T)
            A = T*(1-fx-fz)+2*x*z/T
            B = -T+x*fz+z*fx
            kernel = T**N/mp.factorial(N)*mp.exp(-s*x)*mp.exp(-s*z)
            atom = (A+T/L*B)*kernel
            full += atom
            left = mp.floor(T/width)*width
            if mp.mpf(1971)*N/1000 <= left and left+width <= mp.mpf(2029)*N/1000:
                kept += atom
                count += 1
            else:
                exterior_A += A*kernel
                exterior_B += T/L*B*kernel
        assert count == row['retainedPairs']
        for key, actual in (('sourceScaledFinite', full), ('sourceScaledLiteral', kept),
                            ('sourceScaledExteriorIntercept', exterior_A),
                            ('sourceScaledExteriorSlope', exterior_B)):
            error = abs(decode(row[key])-u**(N+1)*actual)
            assert error < mp.mpf('1e-75')
            errors.append(error)
    with localcontext() as ctx:
        ctx.prec = 105
        U, sigma = Decimal(10001)/20000, 1+Decimal(1)/10000000
        for row in data['tiltDiagnostics']:
            b = Decimal(row['radialSlope'])
            exponent = (U*b).ln()+1+(sigma-Decimal('1.5'))*b
            assert exponent < -Decimal(1)/1000000
            assert abs(exponent-Decimal(row['exponent'])) < Decimal('1e-79')
    assert not data['independentSignedMainBoundProved'] and data['floorCredit'] == 0
    assert not data['finiteUniverseIsExhaustiveLiteralCarrier']
    output = dict(inputSha256=hashlib.sha256(args.input.read_bytes()).hexdigest(),
                  checkerSha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  independentPrimePhaseRecurrenceReplay=True, independentDecimalTiltReplay=True,
                  cases=len(data['finitePrimeRegressions']), maxReplayError=float(max(errors)),
                  allSamplesBelowFormalThreshold=True, floorCredit=0, passed=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(output))


if __name__ == '__main__':
    main()
