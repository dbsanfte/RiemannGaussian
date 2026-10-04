#!/usr/bin/env python3
"""Optional genuine-prime recurrence test after exact factorial collection.

This finds a HEIGHT at which a fixed, incomplete frozen prime population
aligns. It is not a fixed-height, cofinal-order experiment or floor credit.
No sampling, prime-density transport or hypothetical zero is used.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

from flint import arb, ctx, fmpz_mat


def pin(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def ball(value, digits=70):
    return value.str(digits, radius=True)


def lower_mass(order, cutoff, share):
    term = (1-share)**order
    total = term
    for k in range(cutoff):
        term *= arb(order-k)/arb(k+1)*share/(1-share)
        total += term
    return total


def run(scale_digits):
    source = Path('.lake/riesz-pair-joint/new-primes.json')
    row = next(r for r in json.loads(source.read_text())['rows']
               if r['id'] == '1536-balanced-731')
    assert row['left']['provedByFLINT'] and row['right']['provedByFLINT']
    selected = row['left']['primes'][:4]+row['right']['primes'][:4]
    primes = [int(p) for p in selected]
    assert len(primes) == len(set(primes)) == 8
    order = row['N']
    # The frozen FLINT primality proofs are not rerun and are not Lean proofs.
    ctx.prec = math.ceil(scale_digits*math.log2(10))+4096
    scale = 10**scale_digits
    logs = [arb(p).log() for p in primes]
    frequency = [t/(2*arb.pi()) for t in logs]
    rounded = [(alpha*scale+arb(1)/2).floor().unique_fmpz() for alpha in frequency]
    assert all(a is not None for a in rounded)
    basis = [[1, *map(int, rounded)]]
    for i in range(len(primes)):
        basis.append([0]+[scale if i == j else 0 for j in range(len(primes))])
    matrix = fmpz_mat(basis)
    reduced, transform = matrix.lll(transform=True)
    assert transform*matrix == reduced
    chosen = next(i for i in range(reduced.nrows()) if abs(int(reduced[i, 0])) >= 54)
    sign = 1 if reduced[chosen, 0] > 0 else -1
    height = sign*int(reduced[chosen, 0])
    multiples = [-sign*int(transform[chosen, i+1]) for i in range(len(primes))]
    phases, phase_errors, lattice = [], [], []
    for i, (alpha, integer) in enumerate(zip(frequency, multiples)):
        residual_integer = height*int(rounded[i])-integer*scale
        assert residual_integer == sign*int(reduced[chosen, i+1])
        reduced_angle = 2*arb.pi()*(height*alpha-integer)
        sine, cosine = reduced_angle.sin_cos()
        error = ((cosine-1)**2+sine**2).sqrt()
        assert error < arb(10)**-100
        phases.append((cosine, -sine))
        phase_errors.append(error)
        lattice.append({'roundedFrequency': str(rounded[i]),
                        'nearestHeightFrequency': str(integer),
                        'exactLatticeResidual': str(residual_integer),
                        'reducedAngle': ball(reduced_angle)})
    assert arb(height+3).log() > 1800
    ctx.prec = 512
    u = arb(10001)/20000
    # Evaluate the exact moving length and finite prefix BEFORE any sign test.
    damped = 20000**order//((order+1)*10001**order)
    length = 2*arb(damped+2).log()
    cutoff = 13*order//32
    at_zero, at_height_re, at_height_im = arb(0), arb(0), arb(0)
    cases = []
    for i, j in itertools.combinations(range(len(primes)), 2):
        x, z = logs[i], logs[j]
        total = x+z
        prefix = total*(1-total/length)-total/length*((length-x)*lower_mass(order+1, cutoff, z/total)
                                    +(length-z)*lower_mass(order+1, cutoff, x/total))
        selberg = -2*x*z/total
        coefficient = prefix-selberg
        assert coefficient > 0
        scalar = u**(order+1)*coefficient*total**order/arb(math.factorial(order))*(-arb(3)/2*total).exp()
        re = phases[i][0]*phases[j][0]-phases[i][1]*phases[j][1]
        im = phases[i][0]*phases[j][1]+phases[i][1]*phases[j][0]
        # Strict one-unit interior implies period membership for every |y|>=54.
        assert arb(1971)/1000*order+1 < total < arb(2029)/1000*order-1
        assert x > 16*arb(order+1).log() and z > 16*arb(order+1).log()
        assert max(x, z) < 2*length
        assert abs(x/total-arb(1)/2) < arb(1)/40
        assert re > 1-arb(10)**-90
        at_zero += scalar
        at_height_re += scalar*re
        at_height_im += scalar*im
        cases.append({'indices': [i, j], 'joinedCoefficient': ball(coefficient),
                      'sourceScaledZeroHeightAtom': ball(scalar), 'productPhaseReal': ball(re),
                      'radialInteriorWithUnitMargin': True, 'physicalRoughThresholdRetained': True,
                      'exactMovingLengthUsed': True, 'distinctSquarefreePair': True,
                      'fullFactorialPrefixUsed': True})
    error = (abs(at_height_re-at_zero)+abs(at_height_im))/at_zero
    assert at_zero > 0 and error < arb(10)**-90
    return {'classification': 'Finite actual-prime recurrence countertest; no cofinal floor saving',
        'frozenInput': pin(source), 'frozenRow': row['id'], 'N': order,
        'formalOrderThreshold': 65536, 'belowFormalThreshold': True,
        'scaleDigits': scale_digits, 'latticeScale': str(scale), 'height': str(height),
        'heightLog': ball(arb(height).log()), 'primes': selected, 'lattice': lattice,
        'perPrimePhaseErrors': [ball(e) for e in phase_errors], 'pairCases': cases,
        'sourceScaledZeroHeightSignedSum': ball(at_zero),
        'sourceScaledRecurrentSignedSum': {'re': ball(at_height_re), 'im': ball(at_height_im)},
        'relativeSignedResponseReplayError': ball(error), 'latticeTransformationReplayedExactly': True,
        'primePopulationComplete': False, 'fixedHeightCofinalTargetTested': False,
        'heightVariesWithChosenFinitePopulation': True,
        'independentFloorProved': False, 'newArithmeticFloorSaving': False, 'newZeroExclusion': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scale-digits', type=int, default=2200)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert args.scale_digits >= 2200
    report = run(args.scale_digits)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ('N', 'heightLog', 'relativeSignedResponseReplayError',
          'independentFloorProved', 'newArithmeticFloorSaving')}))


if __name__ == '__main__':
    main()
