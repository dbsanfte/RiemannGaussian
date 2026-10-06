#!/usr/bin/env python3
"""Optional same-amplitude phase-code preflight; not a certificate.

Keep exact finite Fejer indices, every prime power and the full height
phase. The Mellin grid evaluates the literal continuous carry profile,
not a replacement limiting density. All quadrature errors remain open.
"""

import argparse
import json
import math
from pathlib import Path

import numpy as np
from probe_suzuki_integer_carry import prime_power_bases


def amplitudes(H, frequencies):
    N = np.arange(H, 3*H, dtype=np.int64)
    a = np.r_[np.arange(1, H+1), np.arange(H-1, -1, -1)]/H
    return N, a[None, :]*np.exp(1j*np.asarray(frequencies)[:, None]*N)


def continuous_mass(H, alpha, points):
    lo, hi = -16.0, math.log(6.0)
    step = (hi-lo)/points
    logs = lo+(np.arange(points)+.5)*step
    x = np.exp(logs)
    value = -alpha[:, 0, None]*(np.floor(2/x) % 2)[None, :]
    value += alpha[:, -1, None]*(np.floor(6/x) % 2)[None, :]
    differences = alpha[:, :-1]-alpha[:, 1:]
    for k in range(1, 2*H):
        carry = np.floor((2*(H+k)/H)/x) % 2
        value += differences[:, k-1, None]*carry[None, :]
    return logs, np.abs(value)**2, step


def prime_packets(H, alpha, ds):
    result = np.zeros((len(alpha), len(ds)), dtype=complex)
    diagonal = np.zeros(len(ds))
    active_counts = np.zeros(len(ds), dtype=int)
    for i, d in enumerate(ds):
        plus = np.arange((d-1)//2, 3*H, d, dtype=int)
        minus = np.arange(d-1, 3*H, d, dtype=int)
        plus, minus = plus[plus >= H], minus[minus >= H]
        result[:, i] = (np.sum(alpha[:, plus-H], axis=1)-
                        np.sum(alpha[:, minus-H], axis=1))
        active = np.r_[plus, minus]
        active = active[active < 3*H-1]
        diagonal[i] = np.sum(np.abs(alpha[0, active-H])**2)
        active_counts[i] = len(active)
    return result, diagonal, active_counts


def row(H, frequencies, points, height, beta, prepared=None):
    _, alpha = amplitudes(H, frequencies)
    logs, mass, step = prepared or continuous_mass(H, alpha, points)
    cp = np.sum(np.exp((1-1j*height)*logs)[None, :]*mass, axis=1)*step
    cb = np.sum(np.exp(beta*logs)[None, :]*mass, axis=1)*step
    lam = np.array([cp[1]-cp[2], cp[2]-cp[0], cp[0]-cp[1]])
    # Canonical lambda dot C(beta) is MINUS det(rows 1,p,beta).
    response = np.dot(lam, cb)
    determinant = np.linalg.det(np.array([np.ones(3), cp, cb]))
    bases = prime_power_bases(6*H)
    ds = np.flatnonzero(bases)
    packets, diagonal, active_counts = prime_packets(H, alpha, ds)
    actual_mass = np.abs(packets)**2
    kernel = lam@actual_mass
    offdiag = lam@(actual_mass-diagonal[None, :])
    single = active_counts <= 1
    coefficient_phase = np.exp(-1j*height*math.log(H))
    arithmetic = coefficient_phase*np.sum(
        np.log(bases[ds])*np.exp(-1j*height*np.log(ds))*kernel)/H**beta
    low = ds <= math.isqrt(H)
    low_arithmetic = coefficient_phase*np.sum(np.log(bases[ds[low]])*
                            np.exp(-1j*height*np.log(ds[low]))*kernel[low])/H**beta
    variation = (np.abs(alpha[:, 0])+np.abs(alpha[:, -1])+
                 np.sum(np.abs(np.diff(alpha, axis=1)), axis=1))
    return {
        'H': H, 'frequencies': list(frequencies), 'height': height, 'beta': beta,
        'normalizedPoleCoefficients': [[v.real, v.imag] for v in cp],
        'normalizedMatchedCoefficients': cb.real.tolist(),
        'nativeResponseNormDividedBy_H_power_1_plus_beta': float(abs(response)),
        'lambdaSumResidual': float(abs(np.sum(lam))),
        'poleResponseResidual': float(abs(np.dot(lam, cp))),
        'determinantOrientationResidual': float(abs(response+determinant)),
        'diagonalCancellationResidual': float(np.max(np.abs(kernel-offdiag))),
        'singleIncidenceKernelResidual': float(np.max(np.abs(kernel[single]), initial=0)),
        'nativeStatisticDividedBy_H_power_1_plus_beta': [arithmetic.real, arithmetic.imag],
        'nativeLowSectorDividedBy_H_power_1_plus_beta': [low_arithmetic.real, low_arithmetic.imag],
        'normalizedTailBoundsOnlyNotQuadratureErrors':
            (variation**2*math.exp(-16*beta)/beta).tolist(),
        'gridPoints': points, 'numericalCertificate': False,
    }


def algebraic_replay():
    H = 7
    N, alpha = amplitudes(H, [0, 1/H, 2/H])
    ds = np.arange(2, 6*H+1)
    packets, _, counts = prime_packets(H, alpha, ds)
    delta = ((2*(N[:, None]+1)//ds) % 2)-((2*N[:, None]//ds) % 2)
    direct = alpha@delta
    replay_error = float(np.max(np.abs(packets-direct)))
    c = np.array([1+2j, 3-1j, -.5+.25j])
    lam = np.array([c[1]-c[2], c[2]-c[0], c[0]-c[1]])
    mass = np.abs(packets)**2
    joined = lam@mass
    lag_joined = np.zeros(len(ds), dtype=complex)
    for i, n in enumerate(N):
        for j, m in enumerate(N):
            if n == m:
                continue
            b = np.sum(lam*np.exp(1j*np.array([0,1/H,2/H])*(n-m)))
            lag_joined += alpha[0, i]*alpha[0, j].conjugate()*b*delta[i]*delta[j]
            if np.any((ds > 2*abs(int(n-m))+1) & (delta[i]*delta[j] != 0)):
                raise AssertionError('literal lag support failed')
    lag_error = float(np.max(np.abs(joined-lag_joined)))
    outer_error = float(np.max(np.abs(joined[ds > 3*H]), initial=0))
    alias_error = 0.0
    for h in range(1, 17):
        _, a = amplitudes(h, [math.pi])
        v, _, _ = prime_packets(h, a, np.array([2]))
        alias_error = max(alias_error, abs(abs(v[0,0])**2-h**2))
    if max(replay_error, lag_error, outer_error, alias_error) > 2e-10:
        raise AssertionError('phase-code algebraic replay failed')
    return {'integerResidueVsDirectPacketResidual': replay_error,
            'lagExpansionResidual': lag_error, 'outerAbove3HResidual': outer_error,
            'piAliasMass_H_squared_Residual': float(alias_error),
            'singleIncidenceDenominatorsReplayed': int(np.sum(counts <= 1))}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--maximum-h', type=int, default=1024)
    p.add_argument('--grid-points', type=int, default=65536)
    p.add_argument('--slow-only', action='store_true')
    p.add_argument('--heights', type=float, nargs='+', default=[60.0])
    p.add_argument('--betas', type=float, nargs='+', default=[.99995])
    p.add_argument('--output', type=Path,
                   default=Path('.lake/suzuki-carry-phase-code/probe.json'))
    args = p.parse_args()
    if args.maximum_h < 64 or args.grid_points < 8192:
        p.error('maximum-h>=64 and grid-points>=8192 are required')
    rows = []
    for H in sorted({64, 256, args.maximum_h}):
        families = [
                ('slow_0_1_2', [0, 1/H, 2/H]),
                ('fixed_0_pi_half_pi', [0, math.pi/2, math.pi]),
                ('symmetric_control', [0, 1/H, -1/H])]
        if args.slow_only:
            families = families[:1]
        for name, frequencies in families:
            _, alpha = amplitudes(H, frequencies)
            prepared = continuous_mass(H, alpha, args.grid_points)
            for beta in args.betas:
                if beta <= 0:
                    p.error('every beta must be positive')
                for height in args.heights:
                    r = row(H, frequencies, args.grid_points, height, beta, prepared)
                    r['family'] = name
                    rows.append(r)
                    print(json.dumps({k:r[k] for k in ['H','family','height','beta',
                          'nativeResponseNormDividedBy_H_power_1_plus_beta',
                          'singleIncidenceKernelResidual']}), flush=True)
    report = {'scope': 'Optional floating preflight, exact finite indices',
              'algebraicReplay': algebraic_replay(),
              'allPrimePowersAndFullPhaseRetained': True,
              'height60SyntheticNotClaimedZero': True,
              'cofinalNondegeneracyProved': False,
              'quadratureErrorCertified': False, 'rows': rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
