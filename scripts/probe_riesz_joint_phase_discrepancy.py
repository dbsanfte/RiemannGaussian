#!/usr/bin/env python3
"""Optional joint circular phase-discrepancy test, outside builds and CI.

Join ALL literal balanced toy atoms and the SAME full signed correction
before forming the centered cumulative discrepancy. The total signed mass
is subtracted as a uniform circular measure, whose first harmonic is zero.
The centered primitive's L2 energy gives a whole signed bound without a
separate count/prime price. It is NOT a native/cofinal certificate.

No phase is frozen or rotated by prime/count. No new completion, density
estimate, artificial allocation or independence assumption is used.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
import probe_riesz_balanced_joint as base
import probe_riesz_joint_phase_transport as transport


def encode(z):
    return dict(re=float(z.real), im=float(z.imag))


def discrepancy(theta, amplitude):
    period = 2*math.pi
    permutation = np.argsort(theta)
    theta, amplitude = theta[permutation], amplitude[permutation]
    delta = math.fsum(amplitude.tolist())
    axis = np.r_[0., theta, period]
    lengths = np.diff(axis)
    assert np.min(lengths) >= 0
    mid = (axis[:-1]+axis[1:])/2
    cumulative = np.r_[0., np.cumsum(amplitude)]
    # Piecewise AFFINE primitive of the exact signed atom measure minus
    # uniform signed mass. Center by its own mean, which costs no harmonic.
    centered = cumulative-delta*mid/period
    mean = math.fsum((lengths*centered).tolist())/period
    centered -= mean
    energy = math.fsum((lengths*(centered**2+
        delta**2*lengths**2/(12*period**2))).tolist())
    assert energy >= 0
    phase_total = complex(np.dot(amplitude, np.exp(-1j*theta)))
    # Integrate the affine primitive times sin(theta) exactly on each
    # interval. Retain its SIGNED correlation; this is an identity check.
    left, right = axis[:-1], axis[1:]
    constant = cumulative-mean
    integral_sin = math.fsum((constant*(np.cos(left)-np.cos(right))+
        delta/period*(right*np.cos(right)-left*np.cos(left)
                     -np.sin(right)+np.sin(left))).tolist())
    assert abs(integral_sin-phase_total.real) < 3e-12
    price = math.sqrt(math.pi*energy)
    assert abs(phase_total.real) <= price+1e-12
    # The first harmonic is an exact, NONNEGATIVE part of this energy.
    # The rest is reported explicitly. A small high-frequency residual
    # cannot be used to delete the source-bearing first harmonic.
    first_energy = abs(phase_total)**2/math.pi
    assert first_energy <= energy+1e-12
    return dict(signedTotal=encode(phase_total), signedArithmeticMass=delta,
        centeredPrimitiveEnergy=energy, firstHarmonicEnergy=first_energy,
        higherHarmonicEnergy=energy-first_energy,
        firstHarmonicEnergyFraction=(first_energy/energy if energy else None),
        wholeSignedCauchyPrice=price,
        signedIntegralOfPrimitive=integral_sin,
        circularMeanRemovedExactly=True, fullComplexPhaseRetained=True,
        noSourceHarmonicDeleted=True, noCofinalFloorProved=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders', nargs='+', type=int, default=[6, 7])
    ap.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    ap.add_argument('--output', type=Path,
        default=Path('.lake/riesz-joint-phase-discrepancy/probe.json'))
    args = ap.parse_args()
    assert all(n in [6, 7, 8] for n in args.orders)
    assert all(y >= 54 for y in args.heights)
    frozen_path = Path('.lake/riesz-balanced-critical-shell/probe.json')
    frozen = {(c['N'], c['height'], tuple(c['window'])): c
              for c in json.loads(frozen_path.read_text())['cases']}
    previous_paths = [Path('.lake/riesz-joint-phase-transport/cubic-probe.json'),
                      Path('.lake/riesz-joint-phase-transport/cubic-order8.json')]
    previous = {(c['N'], c['height'], tuple(c['window'])): c
                for p in previous_paths for c in json.loads(p.read_text())['cases']}
    cases, regressions = [], 0
    for N in args.orders:
        print(json.dumps(dict(event='prepare', N=N)), flush=True)
        data = base.prepare(N, 10001/20000)
        for window in [(1.95, 2.03), (1.971, 2.029)]:
            pos, neg, counts = transport.masses(data, window)
            T = np.r_[pos[:, 1], neg[:, 1]]
            amplitude = np.r_[pos[:, 0], -neg[:, 0]]
            for y in args.heights:
                d = discrepancy((y*T)%(2*math.pi), amplitude)
                # Compare with the original UNREDUCED Fourier phases.
                actual = complex(np.dot(amplitude, np.exp(-1j*y*T)))
                decoded = complex(d['signedTotal']['re'], d['signedTotal']['im'])
                assert abs(decoded-actual) < 3e-12
                key = N, y, window
                if key in frozen:
                    old = frozen[key]['signedJoint']
                    assert abs(actual-complex(old['re'], old['im'])) < 3e-12
                    regressions += 1
                row = dict(N=N, height=y, window=list(window),
                    counts=counts, nonzeroMainAndHeadAtoms=len(amplitude), **d)
                if key in previous:
                    p = previous[key]
                    old = p.get('previousOptimizedWholePrice')
                    if old is not None:
                        row['previousFundedPrice'] = old
                        row['improvesPreviousFundedPrice'] = d['wholeSignedCauchyPrice'] < old
                    row['previousCubicSignedPrice'] = p['cubicBest']['cubicWholeFloorCost']
                    row['improvesPreviousCubicSignedPrice'] = (
                        d['wholeSignedCauchyPrice'] < max(0., row['previousCubicSignedPrice']))
                cases.append(row)
                print(json.dumps({k: row[k] for k in ['N', 'height', 'window',
                    'signedTotal', 'wholeSignedCauchyPrice', 'firstHarmonicEnergyFraction',
                    'improvesPreviousFundedPrice', 'improvesPreviousCubicSignedPrice']
                    if k in row}, allow_nan=False), flush=True)
    paths = [Path(__file__), Path(base.__file__), Path(transport.__file__), frozen_path,
             *previous_paths]
    result = dict(schemaVersion=1, cases=cases, frozenComplexTotalRegressions=regressions,
        sources=[dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                 for p in paths],
        scope=dict(optionalOutsideBuildsCI=True, toyLength='-2N log(10001/20000)',
            nativeMovingLength=False, nativeDyadicSchedule=False, fullNativeDeletionMasks=False,
            allCountsAndSameFullCorrectionJoinedBeforeEnergy=True,
            noGenericIndependenceOrOrthogonalityAssumed=True,
            firstSourceHarmonicRetained=True, noNativeOrCofinalEstimateProved=True))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')


if __name__ == '__main__':
    main()
