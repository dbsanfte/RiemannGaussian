#!/usr/bin/env python3
"""Independent optional recurrence replay; imports no producer.

The lattice integers are replayed exactly. Phases use direct mpmath complex
exponentials, not the producer's reduced-angle sine/cosine. Compare the
original four factorial slots plus ONE square correction with direct
unordered pairs before reporting the relative finite signed response.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

from flint import arb, ctx
import mpmath as mp


def check_ball(encoded, value):
    # The independently evaluated point has much more precision than the
    # stored 70-digit balls. Rounded reference points are not certificates.
    assert arb(encoded).contains(arb(mp.nstr(value, 300))), (encoded, mp.nstr(value, 80))


def lower(order, cutoff, share):
    # Independent binomial formula, not the producer's running recurrence.
    return mp.fsum(math.comb(order, k)*share**k*(1-share)**(order-k)
                   for k in range(cutoff+1))


def replay(data):
    source = Path(data['frozenInput']['path'])
    assert hashlib.sha256(source.read_bytes()).hexdigest() == data['frozenInput']['sha256']
    row = next(r for r in json.loads(source.read_text())['rows'] if r['id'] == data['frozenRow'])
    assert data['primes'] == row['left']['primes'][:4]+row['right']['primes'][:4]
    assert row['left']['provedByFLINT'] and row['right']['provedByFLINT']
    primes = list(map(int, data['primes']))
    n, y = data['N'], int(data['height'])
    scale = int(data['latticeScale'])
    assert scale == 10**data['scaleDigits'] and y >= 54
    phases, logs, phase_error = [], [], []
    # Precision depends on the full height, not only on the modest prime size.
    with mp.workdps(data['scaleDigits']+160):
        for p, lattice, bound in zip(primes, data['lattice'], data['perPrimePhaseErrors']):
            t = mp.log(p)
            frequency = t/(2*mp.pi)
            a = int(mp.floor(scale*frequency+mp.mpf(1)/2))
            nearest = int(lattice['nearestHeightFrequency'])
            assert str(a) == lattice['roundedFrequency']
            assert y*a-nearest*scale == int(lattice['exactLatticeResidual'])
            phase = mp.exp(-mp.j*y*t)
            error = abs(phase-1)
            assert error < mp.mpf('1e-100')
            check_ball(bound, error)
            check_ball(lattice['reducedAngle'], 2*mp.pi*(y*frequency-nearest))
            phases.append(phase)
            logs.append(t)
            phase_error.append(error)
    mp.mp.dps = 350
    ctx.prec = 2048
    u, m, k = mp.mpf(10001)/20000, n+1, 13*n//32
    damped = 20000**n//((n+1)*10001**n)
    length = 2*mp.log(damped+2)
    zero, response = mp.mpf(0), mp.mpc(0)
    for case in data['pairCases']:
        i, j = case['indices']
        assert i < j and primes[i] != primes[j]
        x, z, total = logs[i], logs[j], mp.log(primes[i]*primes[j])
        assert mp.mpf(1971)/1000*n+1 < total < mp.mpf(2029)/1000*n-1
        assert min(x, z) > 16*mp.log(n+1) and max(x, z) < 2*length
        coefficient = total*(1-total/length)-total/length*((length-x)*lower(m, k, z/total)
                                              +(length-z)*lower(m, k, x/total))
        coefficient += 2*x*z/total
        assert coefficient > 0
        atom = u**m*coefficient*total**n/mp.factorial(n)*mp.exp(-mp.mpf(3)/2*total)
        # Use the product label's DIRECT logarithm/phase as a third check.
        with mp.workdps(data['scaleDigits']+160):
            phase = mp.exp(-mp.j*y*mp.log(primes[i]*primes[j]))
            assert abs(phase-phases[i]*phases[j]) < mp.mpf('1e-320')
        assert phase.real > 1-mp.mpf('1e-90')
        check_ball(case['joinedCoefficient'], coefficient)
        check_ball(case['sourceScaledZeroHeightAtom'], atom)
        check_ball(case['productPhaseReal'], phase.real)
        zero += atom
        response += atom*phase
    check_ball(data['sourceScaledZeroHeightSignedSum'], zero)
    check_ball(data['sourceScaledRecurrentSignedSum']['re'], response.real)
    check_ball(data['sourceScaledRecurrentSignedSum']['im'], response.imag)
    assert abs(response-zero)/zero < mp.mpf('1e-90')
    assert zero < mp.mpf(399)/5000  # This tiny population is not a floor counterexample.

    arrays = []
    for t, phase in zip(logs, phases):
        values = [mp.exp(-mp.mpf(3)/2*t)*phase]
        for order in range(1, n+3):
            values.append(values[-1]*t/order)
        arrays.append(values)
    moments = [mp.fsum(values[order] for values in arrays) for order in range(n+3)]
    central = mp.mpf(m)/2*mp.fsum(moments[i]*moments[m-i] for i in range(k+1, m-k))
    successor = -mp.mpf(m)*(m+1)/(2*length)*mp.fsum(
        moments[i]*moments[m+1-i] for i in range(k+1, m+1-k))
    prefix = -mp.mpf(m)/length*mp.fsum(i*moments[i]*moments[m+1-i] for i in range(1, k+1))
    trace = mp.fsum(mp.mpf((i+1)*(n-i))*moments[i+1]*moments[n-i] for i in range(n))/n
    square = [mp.fsum(t*(2*t)**order/mp.factorial(order)*mp.exp(-3*t)*phase**2
                     for t, phase in zip(logs, phases)) for order in (n, n+1)]
    mass = lower(m, k, mp.mpf(1)/2)
    diagonal = (2*mass-mp.mpf(3)/2)*square[0]+m/length*(1-mass)*square[1]
    replay_error = abs(u**m*(central+successor+prefix+trace+diagonal)-response)/zero
    assert replay_error < mp.mpf('1e-300')
    check_ball(data['heightLog'], mp.log(y))
    assert mp.log(y+3) > 1800
    assert not data['independentFloorProved'] and not data['newArithmeticFloorSaving']
    assert not data['fixedHeightCofinalTargetTested'] and not data['primePopulationComplete']
    return {'classification': 'Independent finite actual-prime recurrence replay; no arithmetic saving',
        'genuineFrozenPrimes': len(primes), 'unorderedPairsReplayed': len(data['pairCases']),
        'latticeEqualitiesReplayedExactly': True, 'directLargeHeightComplexPhasesReplayed': True,
        'originalFourSlotsAndSingleDiagonalReplayed': True,
        'fourSlotRelativeReplayError': mp.nstr(replay_error, 35),
        'largestActualPrimePhaseError': mp.nstr(max(phase_error), 35),
        'relativeSignedRecurrenceError': mp.nstr(abs(response-zero)/zero, 35),
        'zeroHeightSourceScaledResponse': mp.nstr(zero, 35),
        'independentFloorProved': False, 'newArithmeticFloorSaving': False, 'newZeroExclusion': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    ctx.prec = 2048
    result = replay(json.loads(args.input.read_text()))
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
