#!/usr/bin/env python3
"""Audit elliptic trace channels of the literal signed divisor convolution.

Optional finite-universe numerical research, outside builds and CI. Every
selected squarefree label, divisor incidence, original allocation, physical
mask and complex phase is retained. Residues and cutoff membership are exact
integers; logs, prime status, amplitudes and floating evaluation are not
interval-certified. One common amplitude rescaling is recorded per universe.

This tests a precise obstruction to direct trace projection: translated
Legendre-family traces detect the centered residue vector, whereas the
original joined sum is its constant channel. No prime transport, population
estimate, native floor credit or cofinal rate is inferred.
"""

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import time

import mpmath as mp
import numpy as np

from probe_riesz_joined_count_correlation import population


def elliptic_trace(modulus):
    """Exact cubic character sum, including both degenerate fibers.

    For v != 0,1 this is the Frobenius trace of y^2=x(x-1)(x-v).
    Retaining v=0,1 gives its full character-sum continuation and exact
    zero mean. Deleting these fibers introduces a stated constant channel.
    """
    assert modulus > 2 and all(modulus % d for d in range(2, math.isqrt(modulus)+1))
    chi = -np.ones(modulus, dtype=np.int64)
    chi[0] = 0
    chi[np.asarray([(x*x) % modulus for x in range(1, modulus)])] = 1
    x = np.arange(modulus, dtype=np.int64)[:, None]
    v = np.arange(modulus, dtype=np.int64)[None, :]
    raw = -np.sum(chi[(x*(x-1)*(x-v)) % modulus], axis=0, dtype=np.int64)
    assert int(raw.sum()) == 0
    assert all(int(a)**2 <= 4*modulus for a in raw[2:])
    return raw


def pair_hinge(owner, cofactor_divisor, physical):
    """The actual two-hinge difference, with exact integer membership."""
    if cofactor_divisor >= physical:
        return math.log(owner)
    if owner*cofactor_divisor <= physical:
        return 0.
    return float(mp.log(mp.mpf(owner*cofactor_divisor)/physical))


def convolution(row, physical):
    owner = max(row['factors'])
    a = row['label']//owner
    assert a*owner == row['label'] and math.gcd(owner, a) == 1
    incidences = [(b, sign, pair_hinge(owner, b, physical))
                  for b, sign in row['divisors'] if a % b == 0]
    value = math.fsum(sign*hinge for _, sign, hinge in incidences)
    direct = -math.fsum(sign*float(mp.log(mp.mpf(physical)/d))
                       for d, sign in row['divisors'] if d < physical)
    assert abs(value-direct) <= 1e-10*max(1., abs(value), abs(direct))
    return incidences, direct


def channel_audit(g, raw):
    q = len(raw)
    kernel = raw/math.sqrt(q)
    total = np.sum(g)
    mean = total/q
    centered = g-mean
    fk = np.fft.fft(kernel)
    correlations = np.fft.ifft(np.fft.fft(g)*np.conj(fk))
    assert np.allclose(correlations[0], g@kernel, rtol=1e-10, atol=1e-10)
    assert np.allclose(correlations[1], g@np.roll(kernel, 1), rtol=1e-10, atol=1e-10)
    assert abs(np.sum(correlations)) <= 1e-9*max(1., float(np.sum(np.abs(correlations))))
    # The full translate family has no nonzero Fourier zero for these
    # tested moduli. This numerical reconstruction is NOT a general theorem.
    assert np.min(np.abs(fk[1:])) > 1e-9
    fg = np.zeros(q, dtype=complex)
    fg[1:] = np.fft.fft(correlations)[1:]/np.conj(fk[1:])
    recovered = np.fft.ifft(fg)
    reconstruction = float(np.max(np.abs(recovered-centered)))
    assert reconstruction <= 1e-8*max(1., float(np.max(np.abs(g))))
    # Regression on the missing channel, separate from the actual carrier.
    # Adding a constant changes the sum but leaves ALL trace twists unchanged.
    shift = 2+3j
    shifted = g+shift/q
    changed = np.fft.ifft(np.fft.fft(shifted)*np.conj(fk))
    invariance = float(np.max(np.abs(changed-correlations)))
    assert invariance <= 1e-8*max(1., float(np.max(np.abs(correlations))))
    energy = float(np.vdot(g, g).real)
    constant_energy = float(abs(total)**2/q)
    punctured = kernel.copy()
    punctured[:2] = 0
    punctured_mean = float(np.mean(punctured))
    return dict(modulus=q, exactFullTraceSum=int(raw.sum()),
        degenerateFiberTraces=raw[:2].tolist(),
        puncturedNormalizedTraceMean=punctured_mean,
        realJoinedSum=float(total.real), imaginaryJoinedSum=float(total.imag),
        principalChannelCapturesEntireSignedSum=True,
        residueEnergy=energy, constantChannelEnergy=constant_energy,
        constantChannelEnergyFraction=constant_energy/energy if energy else None,
        maximumTraceTwistNorm=float(np.max(np.abs(correlations))),
        centeredResidueReconstructionError=reconstruction,
        reconstructionLosesTheJoinedSum=True,
        syntheticConstantShift=[shift.real, shift.imag],
        maximumTraceChangeUnderConstantShift=invariance,
        minimumNonzeroTraceFourierMagnitude=float(np.min(np.abs(fk[1:]))),
        traceTwistsSupplyNativeFloorBound=False)


def self_test():
    traces = {q: elliptic_trace(q) for q in [7, 17, 31, 61, 127, 251, 503]}
    for q, raw in traces.items():
        audit = channel_audit(np.ones(q, dtype=complex), raw)
        assert abs(audit['maximumTraceTwistNorm']) < 1e-8
        assert audit['realJoinedSum'] == q
    factors = (2, 3, 5)
    divisors = [(1, 1)]
    for p in factors:
        divisors += [(d*p, -sign) for d, sign in list(divisors)]
    row = dict(factors=factors, label=30, divisors=divisors)
    for threshold in [2, 3, 6, 10, 15, 30, 31]:
        convolution(row, threshold)
    return dict(passed=True, moduli=list(traces),
        allConstantWitnessesChecked=True, twoHingeRegressions=7)


def experiment(order, seed, heights, moduli):
    started = time.monotonic()
    ceiling = {256: 8, 640: 16, 1536: 32}[order]
    pars, rows, excluded = population(order, ceiling, seed)
    scale = max(r['log_amplitude'] for r in rows)
    amplitude = np.exp([r['log_amplitude']-scale for r in rows])
    phases = np.asarray(heights)[:, None]*np.asarray([r['total'] for r in rows])
    weight = amplitude[None, :]*np.exp(-1j*phases)
    residue = {q: np.zeros((len(heights), q), dtype=complex) for q in moduli}
    literal = np.zeros(len(heights), dtype=complex)
    incidences = 0
    for index, row in enumerate(rows):
        terms, direct = convolution(row, pars['physical'])
        literal += weight[:, index]*direct
        incidences += len(terms)
        for b, sign, hinge in terms:
            if hinge:
                atom = weight[:, index]*(sign*hinge)
                for q in moduli:
                    residue[q][:, b % q] += atom
    cases = []
    traces = {q: elliptic_trace(q) for q in moduli}
    for ih, height in enumerate(heights):
        channels = []
        for q in moduli:
            assert abs(residue[q][ih].sum()-literal[ih]) <= 1e-8*max(1., abs(literal[ih]))
            channels.append(channel_audit(residue[q][ih], traces[q]))
        cases.append(dict(height=height, realLiteralSubset=float(literal[ih].real),
            imaginaryLiteralSubset=float(literal[ih].imag), channels=channels))
    return dict(N=order, seed=seed, originalCountCeiling=ceiling,
        prematurelyApplyingEventualCountCrop=False, selectedLabels=len(rows),
        counts=sorted({r['count'] for r in rows}),
        labelsByCount=dict(Counter(r['count'] for r in rows)),
        excludedMasks=dict(excluded), completeCofactorDivisorIncidences=incidences,
        sourceAmplitudeLogScale=scale, oneSharedRescalingPerPopulation=True,
        exactIntegerResiduesAndCutoffMembership=True,
        originalFullAllocationAndComplexPhaseRetained=True,
        seconds=time.monotonic()-started, cases=cases)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test', action='store_true')
    ap.add_argument('--orders', nargs='+', type=int, default=[256, 640])
    ap.add_argument('--seeds', nargs='+', type=int, default=[317, 919])
    ap.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    ap.add_argument('--moduli', nargs='+', type=int, default=[17, 31, 61, 127, 251, 503])
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-elliptic-audit/probe.json'))
    args = ap.parse_args()
    mp.mp.dps = 100
    tests = self_test()
    if args.self_test:
        print(json.dumps(tests, indent=2))
        return
    report = dict(schemaVersion=1, kind='literal-divisor-convolution-elliptic-channel-audit',
        sourceSha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        selfTest=tests, scope='complete constructed finite prime universes, not full native core',
        intervalArithmetic=False, primeCertificates=False,
        genericTraceProjectionControlsPrincipalChannel=False,
        nativeFloorCredit=False, cofinalRateCertified=False, cases=[])
    for order in args.orders:
        for seed in args.seeds:
            batch = experiment(order, seed, args.heights, args.moduli)
            report['cases'].append(batch)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2)+'\n')
            print(json.dumps(dict(N=order, seed=seed, labels=batch['selectedLabels'],
                incidences=batch['completeCofactorDivisorIncidences'],
                channels=len(args.heights)*len(args.moduli),
                seconds=batch['seconds'], nativeFloorCredit=False)), flush=True)


if __name__ == '__main__':
    main()
