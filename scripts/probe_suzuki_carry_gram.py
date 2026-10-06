#!/usr/bin/env python3
"""Optional lagged carry-Gram preflight; not a numerical certificate.

Retain the literal prime powers and complex phase. Replay periodic lags,
the joined quadratic, and scale-localized coefficient packets. Report
source sensitivity separately from the strength of the arithmetic budget.
"""

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from probe_suzuki_integer_carry import prime_power_bases
from probe_suzuki_carry_correlations import divisor_phase


def delta(N, d):
    return (2*(N+1)//d-2*((N+1)//d))-(2*N//d-2*(N//d))


def periodic_preflight():
    checks = 0
    for d in range(2, 129):
        N = np.arange(d, dtype=np.int64)
        raw = delta(N, d)
        spikes = (N == (d-1)//2).astype(int)-(N == d-1).astype(int)
        if not np.array_equal(raw, spikes):
            raise AssertionError('literal two-spike incidence mismatch')
        for h in range(2*d+1):
            corr = int(np.sum(raw*delta(N+h, d)))
            expected = 2*int(h % d == 0)-int(h % d == d//2)-int(h % d == d-d//2)
            if corr != expected:
                raise AssertionError('periodic lag formula mismatch')
            checks += 1
    return checks


def gcd_quadratic_replay(ds, lam):
    S = np.array([256, 257, 263, 287, 511])
    alpha = np.array([1+.25j, -.4+.8j, .3-.1j, -.7-.2j, .2+.6j])
    incidences = delta(S[:, None], ds[None, :])
    rows = []
    for y in [0.0, 60.0]:
        phase = np.exp(-1j*y*np.log(ds.astype(float)))
        gram = (incidences*(lam*phase)[None, :])@incidences.T
        joined = np.sum(lam*phase*np.abs(alpha@incidences)**2)
        quadratic = alpha@gram@alpha.conj()
        exact = 0j
        for i, N in enumerate(S):
            for j, M in enumerate(S):
                entry = 0j
                for a, ca in zip([2*N+1, 2*N+2, N+1], [1, 1, -2]):
                    for b, cb in zip([2*M+1, 2*M+2, M+1], [1, 1, -2]):
                        entry += ca*cb*divisor_phase(math.gcd(int(a), int(b)), y)
                exact += alpha[i]*alpha[j].conjugate()*entry
        err = max(abs(quadratic-joined), abs(exact-joined))
        if err > 2e-10:
            raise AssertionError('joined quadratic/gcd replay mismatch')
        rows.append({'height': y, 'real': float(joined.real), 'imag': float(joined.imag),
                     'identityResidualFloating': float(err),
                     'hermitianGramClaimed': y == 0})
    return rows


def continuous_packet(X, alpha, x):
    """Exact summation by parts, sampled at real denominators X*x."""
    N = np.arange(X, X+len(alpha), dtype=float)
    upper = 2*(X+len(alpha))/X
    result = alpha[-1]*(np.floor(upper/x) % 2)-alpha[0]*(np.floor(2/x) % 2)
    for n, coefficient in zip(N[1:], alpha[:-1]-alpha[1:]):
        if coefficient != 0:
            result += coefficient*(np.floor(2*(n/X)/x) % 2)
    return result


def source_transform(s):
    carry = (mp.power(2, s)-2)*mp.zeta(s)/s
    overlap = (mp.zeta(s, mp.mpf(3)/4)-mp.zeta(s))/s
    return (1+mp.power(2, s))*carry-2*overlap


def packet_preflight(X, ds, lam):
    N = np.arange(X, 2*X, dtype=np.int64)
    incidence = delta(N[:, None], ds[None, :])
    position = (N-X+.5)/X
    coefficients = {
        'flat': np.ones(X),
        'fejer_triangle_midpoint': 1-np.abs(2*position-1),
        'smooth_hann': np.sin(np.pi*position)**2,
        'fejer_exact_convolution': np.r_[np.convolve(np.ones(X), np.ones(X))/X, 0],
    }
    rows = []
    beta = .99995
    grid = np.linspace(-8, math.log(6), 8192, endpoint=False)
    step = (math.log(6)+8)/8192
    grid += step/2
    x = np.exp(grid)
    for name, alpha in coefficients.items():
        if name == 'fejer_exact_convolution':
            t = np.arange(X, dtype=np.int64)[:, None]
            average = (np.sum((2*(2*X+t)//ds[None, :]) % 2, axis=0)-
                       np.sum((2*(X+t)//ds[None, :]) % 2, axis=0))/X
            mass = average**2
            bound = ((X % ds)/X)**2
            if np.any(mass > bound+1e-13):
                raise AssertionError('exact Fejer localization bound failed')
        else:
            mass = np.abs(alpha@incidence)**2
        low_budgets = []
        if name == 'fejer_exact_convolution':
            for D in sorted({math.isqrt(X), X//8}):
                take = ds <= D
                budget = (math.log(4)+4)*D**3/X**2
                for y in [0.0, 60.0]:
                    # Join the entire phased sector before taking its norm.
                    raw = complex(np.sum(lam[take]*mass[take]*
                                         np.exp(-1j*y*np.log(ds[take].astype(float)))))
                    if abs(raw) > budget+1e-12:
                        raise AssertionError('proved low-denominator budget replay failed')
                    low_budgets.append({'D': D, 'height': y,
                                        'joinedReal': raw.real, 'joinedImag': raw.imag,
                                        'joinedNorm': abs(raw), 'provedBudget': budget,
                                        'arithmeticProof': 'SuzukiCarryFejer.norm_lowPacket_le'})
        zero_height_mass = float(np.sum(lam*mass))
        model_mass = continuous_packet(X, alpha, x)**2
        matched = float(np.sum(np.exp(beta*grid)*model_mass)*step)
        variation = float(abs(alpha[0])+abs(alpha[-1])+np.sum(np.abs(np.diff(alpha))))
        low_tail_bound = variation**2*math.exp(-8*beta)/beta
        if name == 'flat':
            matched_exact = str(mp.nstr(source_transform(mp.mpf('.99995')), 25))
        else:
            matched_exact = None
        height_rows = []
        for y in [0.0, 60.0]:
            raw = complex(np.sum(lam*mass*np.exp(-1j*y*np.log(ds.astype(float)))))
            height_rows.append({'height': y, 'real': raw.real, 'imag': raw.imag,
                                'absolute': abs(raw)})
        physical_upper = 2*(X+len(alpha))
        outside_mass = float(np.sum(lam[ds > physical_upper]*mass[ds > physical_upper]))
        if outside_mass != 0:
            raise AssertionError('physical upper support lost')
        rows.append({'N': X, 'coefficientPacket': name,
                     'literalZeroHeightMass': zero_height_mass,
                     'zeroHeightMassDividedByN': zero_height_mass/X,
                     'normPaymentToMatchedSourceRatio': zero_height_mass/(X**beta*matched),
                     'literalMassBelow_N_over_8': float(np.sum(lam[ds < X/8]*mass[ds < X/8])),
                     'physicalUpperSupport': physical_upper,
                     'literalMassOutsidePhysicalSupport': outside_mass,
                     'smallDenominatorBoundReplayed': name == 'fejer_exact_convolution',
                     'lowDenominatorBudgetReplay': low_budgets,
                     'matchedSourceCoefficientQuadrature': matched,
                     'matchedSourceCoefficientExactFlatFormula': matched_exact,
                     'unresolvedSmallDenominatorTailUpperBound': low_tail_bound,
                     'pointwiseSquaredKernelMin': float(np.min(mass)),
                     'pointwiseSquaredKernelMax': float(np.max(mass)),
                     'phasedStatistics': height_rows})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--maximum-n', type=int, default=4096)
    parser.add_argument('--output', type=Path,
                        default=Path('.lake/suzuki-carry-correlation/gram-probe.json'))
    args = parser.parse_args()
    if args.maximum_n < 1536:
        parser.error('maximum-n must be at least 1536')
    mp.mp.dps = 70
    bases = prime_power_bases(6*(args.maximum_n+1))
    ds = np.flatnonzero(bases)
    lam = np.log(bases[ds].astype(float))
    source_rows = []
    for k in [1, 2]:
        rho = mp.zetazero(k)
        source_rows.append({'control': 'known critical zero; floating, not an off-line zero',
                            'zero': str(rho),
                            'unweightedSquaredFlatSymbolAbsolute': mp.nstr(abs(source_transform(rho)), 25),
                            'heightMatchedSquaredFlatCoefficient': mp.nstr(source_transform(rho.real), 25)})
    report = {
        'scope': 'Optional floating replay; no outward rounding or zero-free certificate',
        'fullPrimePowersRetained': True,
        'phaseRetainedBeforeQuadraticJoin': True,
        'periodicLagIntegerChecks': periodic_preflight(),
        'quadraticGcdReplay': gcd_quadratic_replay(ds, lam),
        'packets': [row for X in sorted({256, 640, 1536, args.maximum_n})
                    for row in packet_preflight(X, ds, lam)],
        'sourceSensitivity': source_rows,
        'flatPacketLeadingDensityCoefficient': str(mp.pi),
        'strengthAudit': {
            'heightMatchingAloneChangesTheLinearMellinArgument': True,
            'squaredMatchedResponseStrictlyPositive': True,
            'lagGramIsHermitianAtNonzeroHeight': False,
            'gcdNormPaymentBeatsSourceScale': False,
            'uncenteredPacketsHaveLinearDensityMass': True,
            'centeredPhasedGlobalBoundProved': False,
            'independentLowDenominatorBudgetProved': True,
            'campaignSourceScaledLowDenominatorSavingProved': True,
            'campaignPowerSaving': 'H=n^20000, D=n^19998, norm/H^beta <= (log4+4)/n^5 for beta>=19999/20000',
            'highDenominatorPacketPaid': False,
        },
        'newSuzukiFloor': False,
        'newZeroFreeRegion': False,
        'rhProved': False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'output': str(args.output),
                      'periodicLagIntegerChecks': report['periodicLagIntegerChecks'],
                      'quadraticGcdReplay': report['quadraticGcdReplay'],
                      'sourceSensitivity': source_rows,
                      'lastPackets': report['packets'][-4:]}, indent=2))


if __name__ == '__main__':
    main()
