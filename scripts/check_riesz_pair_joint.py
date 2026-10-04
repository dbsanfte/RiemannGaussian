#!/usr/bin/env python3
"""Focused independent replay of the five joined actual-prime scans.

Checks exact-product complete-period masks, signed matching ledgers and
independent high-precision shifted phases. This is optional numerical
validation, not a prime-population bound or a Lean certificate.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import numpy as np
from flint import arb, ctx

import probe_riesz_pair_joint as probe
from probe_riesz_pair_prefix import digest


def unpack(value):
    return complex(value['re'], value['im'])


def independent_period_counts(row, label):
    """Use log(product) and integer period endpoints, not the scan's leg sum."""
    N = row['N']
    y = probe.correlations.parse_height(label)
    ctx.prec = max(1200, y.bit_length()+1024,
                   math.ceil(2*N/math.log(2))+256)
    width = 2*arb.pi()/y
    first = (arb(1971)*N/1000/width).ceil().unique_fmpz()
    last = (arb(2029)*N/1000/width).floor().unique_fmpz()
    assert first is not None and last is not None
    last -= 1
    lo = (arb(1971)*N/1000).exp().floor().unique_fmpz()
    hi = (arb(2029)*N/1000).exp().floor().unique_fmpz()
    assert lo is not None and hi is not None
    kept = outside = partial = 0
    for p in map(int, row['left']['primes']):
        for q in map(int, row['right']['primes']):
            product = p*q
            central = int(lo) < product <= int(hi)
            index = (arb(product).log()/width).floor().unique_fmpz()
            assert index is not None
            complete = first <= index <= last
            kept += central and complete
            outside += not central
            partial += central and not complete
    return dict(retainedCompletePeriodLabels=kept,
                outsideOriginalRadialFlag=outside,
                centralButPartialPeriod=partial)


def phase_replays(fresh):
    chosen = [next(r for r in fresh['rows'] if r['id'] == name) for name in
              ('640-share-0-731', '640-share-7-732', '1536-balanced-732')]
    checks = []
    for label in probe.HEIGHTS:
        y = probe.correlations.parse_height(label)
        height_digits = int(label.split('^')[1])+1 if '^' in label else len(label)
        for row in chosen:
            p, q = int(row['left']['primes'][0]), int(row['right']['primes'][0])
            ctx.prec = max(1200, y.bit_length()+1024,
                           math.ceil(2*row['N']/math.log(2))+256)
            # At N=1536 the geometry precision is higher than the phase
            # minimum. Independent replay must exceed that precision too.
            replay_digits = max(390, math.ceil((ctx.prec-y.bit_length())*math.log10(2))+50)
            guard = max(460, replay_digits+80)
            for offset in (-16, 16):
                with mp.workdps(height_digits+guard):
                    argument = -(mp.mpf(y)+offset)*mp.log(mp.mpf(p*q))
                    re, im = mp.cos(argument), mp.sin(argument)
                    value, radius = probe.reduced_phase(
                        -(arb(y)+offset)*arb(p*q).log())
                    period = 2*arb.pi()
                    actual = -(arb(y)+offset)*arb(p*q).log()
                    quotient = (actual/period).floor().unique_fmpz()
                    assert quotient is not None
                    angle = actual-period*quotient
                    assert angle.cos().contains(arb(mp.nstr(re, replay_digits)))
                    assert angle.sin().contains(arb(mp.nstr(im, replay_digits)))
                    difference = abs(complex(float(re), float(im))-value)
                    assert difference <= 5e-16
                    checks.append(dict(height=label, N=row['N'], seed=row['seed'],
                        row=row['id'], offset=offset,
                        productSha256=hashlib.sha256(str(p*q).encode()).hexdigest(),
                        productBitLength=(p*q).bit_length(),
                        arbRadiusUpper=radius, independentMidpointDifference=difference,
                        independentReplayDecimalDigits=replay_digits,
                        extraDecimalGuardDigits=guard,
                        independentReplayContainedByArbBalls=True))
        print(json.dumps(dict(stage='independent shifted-phase replay',
                              height=label, checks=6)), flush=True)
    return checks


def coefficient_replays(boxes):
    """Independent finite binomial recurrence, without SciPy's CDF."""
    checks = []
    with mp.workdps(110):
        for box in boxes:
            N, M, K = box['N'], box['N']+1, 13*box['N']//32
            p, q = box['p'][0], box['q'][0]
            x, z = mp.log(mp.mpf(p)), mp.log(mp.mpf(q))
            T = x+z
            D = 20000**N//((N+1)*10001**N)
            L = mp.log(mp.mpf((D+2)**2))

            def cdf(v):
                term = (1-v)**M
                total = term
                for k in range(K):
                    term *= mp.mpf(M-k)/(k+1)*v/(1-v)
                    total += term
                return total

            Q = T*(1-T/L)-T/L*((L-x)*cdf(z/T)+(L-z)*cdf(x/T))
            central = mp.mpf(1971)*N/1000 < T <= mp.mpf(2029)*N/1000
            R = L-max(L-x, 0)-max(L-z, 0)+max(L-T, 0)
            if not central:
                Q += T*R/L
            expected = Q+2*x*z/T
            error = abs(float(expected)-box['prefixDefectCoefficient'][0, 0])
            assert error < 2e-10*max(1, N)
            assert bool(central) == bool(box['coefficient']['central'][0, 0])
            checks.append(dict(box=box['id'], N=N,
                independentBinomialRecurrenceReplayError=error,
                originalRadialFlagRetained=True))
    return checks


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--scan', type=Path, default=Path('.lake/riesz-pair-joint/scan.json'))
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-joint/validation.json'))
    args = ap.parse_args()
    scan = json.loads(args.scan.read_text())
    for source in scan['sources']:
        assert digest(source['path']) == source, source['path']
    assert not scan['floor'] and not scan['RH'] and scan['cofinalFloorCredit'] == 0
    fresh = json.loads(Path('.lake/riesz-pair-joint/new-primes.json').read_text())
    assert fresh['complete'] and len(fresh['rows']) == len(fresh['plan']) == 30
    assert len(scan['signedBandProfiles']) == 16
    assert len(scan['exactTransitionBoundaries']) == 48
    assert len(scan['nearbyProductMatching']) == 16
    assert scan['coverage']['orders'] == [256, 640, 1536]
    assert scan['coverage']['boxes'] == 50
    assert scan['coverage']['dyadicPhaseOffsetStep'] == '1/64'
    assert scan['coverage']['phaseOffsets'] == 2049
    boxes = probe.prepare(Path('.lake/riesz-pair-structure/scan.primes.json'),
                          Path('.lake/riesz-pair-joint/new-primes.json'),
                          Path('.lake/riesz-balanced-prime-sampling/result.primes.json'))
    coefficient_checks = coefficient_replays(boxes)
    rows = {r['id']: r for r in fresh['rows']}
    mask_checks = []
    for boundary in scan['exactTransitionBoundaries']:
        row = rows[boundary['box']]
        counts = independent_period_counts(row, boundary['height'])
        assert all(boundary[key] == value for key, value in counts.items())
        assert sum(counts.values()) == boundary['sampledPairIncidences']
        mask_checks.append(dict(row=row['id'], height=boundary['height'], **counts))
    reconstruction_max = 0.
    for match in scan['nearbyProductMatching']:
        assert abs(match['positiveSampledMass']+match['negativeSampledMass']-1) < 2e-11
        assert abs(2*match['matchedMass']+match['unmatchedAbsoluteMass']-1) < 2e-11
        assert abs(unpack(match['signedUnmatched'])) <= match['unmatchedAbsoluteMass']+2e-11
        assert abs(unpack(match['signedMatched'])) <= match['geometricPhaseDifferenceCost']+2e-11
        assert match['geometricPhaseDifferenceCost'] <= match['maximumTrivialMatchingCost']+2e-11
        assert abs(unpack(match['phaseCircleMatching']['signedMatched'])) <= (
            match['phaseCircleMatching']['observedChordCost']+2e-11)
        profile = next(p for p in scan['signedBandProfiles'] if
                       (p['N'], p['seed'], p['height']) ==
                       (match['N'], match['seed'], match['height']))
        reconstruction = abs(unpack(match['signedMatched'])+unpack(match['signedUnmatched'])-
                             unpack(profile['signedAtBase']))
        assert reconstruction < 2e-11
        reconstruction_max = max(reconstruction_max, reconstruction)
        assert all(b['exactFiniteReplay'] and not b['completePrimeLegConvergenceUsed'] and
                   0 < b['phaseBallRadiusUpper'] < 1e-100 for b in profile['blocks'])
        assert profile['directShiftedHeightAtomReplayMaxError'] < 2e-11
    for result in scan['seedSignComparisons']:
        expected = min(1., result['familySize']*result['maximumSeedReferenceRank'])
        assert abs(expected-result['familyAdjustedReplicationDiagnostic']) < 1e-15
    checks = phase_replays(fresh)
    result = dict(classification='Independent finite-product/mask/phase replay; no carrier bound',
        sources=[digest(p) for p in ('scripts/check_riesz_pair_joint.py', args.scan,
                                    '.lake/riesz-pair-joint/new-primes.json')],
        allScanSourcePinsMatch=True, completePeriodMaskChecks=mask_checks,
        completePeriodMasksReplayedViaExactLogProduct=True,
        matchingReconstructionMaxError=reconstruction_max,
        matchingUnmatchedMassAndCostChecks=16,
        allSvdModesRetained=True, shiftedPhaseChecks=checks,
        independentCoefficientChecks=coefficient_checks,
        independentBinomialRecurrenceReplayErrorMax=max(
            c['independentBinomialRecurrenceReplayError'] for c in coefficient_checks),
        independentMidpointDifferenceMax=max(c['independentMidpointDifference'] for c in checks),
        mpmathReplayNotIntervalCertificate=True,
        primalityInheritedFromFrozenFLINTProducer=True,
        primalityReproved=False, floor=False, cofinalFloorCredit=0,
        allPassed=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(output=str(args.output), allPassed=True,
        maskChecks=len(mask_checks), phaseChecks=len(checks), floor=False)))


if __name__ == '__main__':
    main()
