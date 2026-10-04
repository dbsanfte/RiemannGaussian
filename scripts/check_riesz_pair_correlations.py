#!/usr/bin/env python3
"""Optional independent checks of the exact-height pair discovery scan.

This validates numerical discovery data, not an asymptotic prime estimate.
The independent mpmath replay uses exact integer heights and 420 extra
decimal digits; it is checked against the Arb phase balls before binary64
rounding. Nothing is attached to ordinary builds or CI.
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

import probe_riesz_pair_correlations as probe
from probe_riesz_pair_prefix import digest


def character_controls(boxes, names):
    """Finite sensitivity checks; these phases are synthetic, not zeta data.

    Use one constant-coefficient-sign box per seed so no global cancellation
    between box charges conceals the control signal. All normalizations and
    shared-leg quartile permutations match the discovery procedure.
    """
    results = []
    for seed in sorted({b['row']['seed'] for b in boxes}):
        b = next(b for b in boxes if b['row']['seed'] == seed and
                 (np.all(b['weights'] > 0) or np.all(b['weights'] < 0)))
        w = b['weights']/np.abs(b['weights']).sum()
        f = b['features']
        cp = np.array([1 if p % 4 == 1 else -1 for p in b['p']])
        cq = np.array([1 if q % 4 == 1 else -1 for q in b['q']])
        assert len(set(cp)) == len(set(cq)) == 2
        observed = np.einsum('ij,ijf->f', w*cp[:, None]*cq[None, :], f)
        variance = np.einsum('ij,ijf->f', np.abs(w), f*f)
        scale = np.sqrt(np.maximum(variance, 1e-20))
        effect = np.abs(observed)/scale
        rng = np.random.default_rng(seed+17513)
        pp = probe.stratified_permutations(cp, b['x'][:, 0], rng, 255)
        qq = probe.stratified_permutations(cq, b['z'][0], rng, 255)
        phases = pp[:, :, None]*qq[:, None, :]
        null = phases.reshape(255, -1)@(w[:, :, None]*f).reshape(-1, len(names))
        maxima = (np.abs(null)/scale[None, :]).max(axis=1)
        rank = (1+np.sum(maxima[:, None] >= effect[None, :], axis=0))/256
        k = names.index('reciprocity_product')
        assert rank[k] <= .05
        # Phase depends only on the left prime: the fitted row indicators
        # should remove it, with the original weight sign retained.
        marginal = np.einsum('ij,ijf->f', w*cp[:, None], f)
        max_marginal = float(np.max(np.abs(marginal)))
        assert max_marginal < 1e-10
        results.append(dict(seed=seed, box=b['row']['box'],
            phase='chi_4(p)*chi_4(q), synthetic sensitivity control only',
            expectedFeature='reciprocity_product',
            recoveredStandardizedEffect=float(effect[k]),
            maximumStatisticRank=float(rank[k]),
            marginalOnlyCorrelationMax=max_marginal, passed=True,
            actualZetaPhaseUsed=False, floorCredit=0))
    return results


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--scan', type=Path, default=Path('.lake/riesz-pair-correlations/scan.json'))
    ap.add_argument('--cache', type=Path, default=Path('.lake/riesz-pair-structure/scan.primes.json'))
    ap.add_argument('--output', type=Path,
                    default=Path('.lake/riesz-pair-correlations/phase-validation.json'))
    args = ap.parse_args()
    scan = json.loads(args.scan.read_text())
    for entry in scan['sources']:
        assert digest(entry['path']) == entry, entry['path']
    assert not scan['independentSignedMainBound'] and not scan['floor']
    boxes, names, _ = probe.prepare(args.cache)
    assert len(names) == len(scan['coverage']['featureNames'])
    assert names == scan['coverage']['featureNames']
    assert sum(b['T'].size for b in boxes) == scan['coverage']['actualPairIncidences']
    max_projection_error = max(b['projection_error'] for b in boxes)
    assert max_projection_error < 1e-10

    coverage = probe.height_coverage(probe.REGRESSION_HEIGHTS+
                                    probe.DISCOVERY_HEIGHTS+probe.VALIDATION_HEIGHTS)
    assert coverage == scan['zeroFreeCoverage']
    for result in scan['results']:
        assert len(result['allScores']) == len(names)
        assert result['testedFeatures'] == len(names)
        expected = [s for s in result['allScores'] if s['maxStatisticPermutationRank'] <= .05]
        assert expected == result['maxStatisticFlagsAt005']
        for record in result['boxDiagnostics']:
            assert record['completePeriodSupportVerifiedViaStrictInterior']
            assert 0 < record['phaseBallRadiusUpper'] < 1e-100
    # This slice's negative conclusion is scoped to this exact saved scan.
    assert not any(r['maxStatisticFlagsAt005'] for r in scan['results'])
    assert not scan['sameHeightSeedReplications']
    controls = character_controls(boxes, names)

    # Three boxes across both seeds, with both legs represented.
    chosen = [(boxes[i][side][0], i, side) for i in (0, len(boxes)//2-1, len(boxes)-1)
              for side in ('p', 'q')]
    checks = []
    for label in probe.DISCOVERY_HEIGHTS+probe.VALIDATION_HEIGHTS:
        y = probe.parse_height(label)
        ctx.prec = max(1200, y.bit_length()+1024)
        values, upper = probe.integer_height_phase([v[0] for v in chosen], y)
        exponent = int(label.split('^')[1])
        with mp.workdps(exponent+420):
            for i, (p, box, side) in enumerate(chosen):
                # Independent implementation and reduction, with no float y.
                argument = -mp.mpf(y)*mp.log(mp.mpf(p))
                independent_re, independent_im = mp.cos(argument), mp.sin(argument)
                period = 2*arb.pi()
                actual = -y*arb(p).log()
                quotient = (actual/period).floor().unique_fmpz()
                assert quotient is not None
                angle = actual-period*quotient
                assert angle >= 0 and angle < period
                real, imag = angle.cos(), angle.sin()
                # Rounded independent decimal strings are far more accurate
                # than these ~1e-306 Arb phase radii. mpmath is a regression
                # implementation, not an independent interval certificate.
                mr = arb(mp.nstr(independent_re, 350))
                mi = arb(mp.nstr(independent_im, 350))
                assert real.contains(mr) and imag.contains(mi)
                rounded = complex(float(independent_re), float(independent_im))
                difference = abs(rounded-values[i])
                assert difference <= 5e-16
                checks.append(dict(height=label, box=box, leg=side,
                    primeBitLength=p.bit_length(),
                    primeSha256=hashlib.sha256(str(p).encode()).hexdigest(),
                    independentMidpointDifference=difference,
                    independent350DigitReplayContainedByArbBall=True,
                    arbRadiusUpper=upper, binary64MidpointRoundingSeparate=True))
        print(json.dumps(dict(validatedHeight=label, checks=len(chosen))), flush=True)

    result = dict(classification='Independent high-precision replay of pair discovery phases; no carrier bound',
        sources=[digest(p) for p in ('scripts/check_riesz_pair_correlations.py',
            'scripts/probe_riesz_pair_correlations.py', args.scan, args.cache)],
        checks=checks, count=len(checks),
        maxMidpointDifference=max(v['independentMidpointDifference'] for v in checks),
        geometryProjectionNormalEquationErrorMax=max_projection_error,
        independentGuardDecimalDigits=420, independentReplayDigits=350,
        allReplayDecimalsContainedByArbBalls=True, mpmathNotAnIntervalCertificate=True,
        scanSourcePinsMatch=True, heightCoverageMatches=True,
        maxStatisticFlags=0, sameHeightReplications=[], allPassed=True,
        syntheticCharacterSensitivityControls=controls,
        floorBound=False, cofinalSaving=0)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(output=str(args.output), count=len(checks), allPassed=True, floorBound=False)))


if __name__ == '__main__':
    main()
