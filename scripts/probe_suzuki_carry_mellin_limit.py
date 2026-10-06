#!/usr/bin/env python3
"""Continuum/scaled finite Fejer preflight, not an interval certificate.

Euler-polynomial sums evaluate the limiting moments without truncating
the dense small-x carry jumps. The modulated profile uses finite geometric
sums. Exact algebra is replayed on small examples before quadrature.
"""

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
from probe_suzuki_carry_phase_code import amplitudes
from probe_suzuki_carry_gram import continuous_packet


EULER = [[1], [-.5, 1], [0, -1, 1], [.25, 0, -1.5, 1],
         [0, 1, 0, -2, 1], [-.5, 0, 2.5, 0, -2.5, 1]]


def tent(v):
    return np.maximum(0, np.minimum(v-1, 3-v))


def scaled_alternating_power(n, K, q):
    """q^n sum_{k=1}^K (-1)^(k+1) k^n, finite Euler identity."""
    v = q*(K+1)
    polynomial = sum(c*q**(n-j)*v**j for j, c in enumerate(EULER[n]))
    return (q**n*sum(EULER[n])-(1-2*(K % 2))*polynomial)/2


def moments(x):
    q = x/2
    cutoffs = [np.floor(v/q).astype(np.int64) for v in [1, 2, 3]]
    result = []
    for n in range(5):
        a = [scaled_alternating_power(n, k, q) for k in cutoffs]
        b = [scaled_alternating_power(n+1, k, q) for k in cutoffs]
        result.append(2*b[1]-b[0]-b[2]+a[0]+3*a[2]-4*a[1])
    return np.array(result)


def continuum_profile(tau, x):
    q = x/2
    if tau == 0:
        return moments(x)[0].astype(complex)
    r = -np.exp(1j*tau*q)
    denominator = 1-r

    def sums(K):
        power = (1-2*(K % 2))*np.exp(1j*tau*q*K)
        a0 = -r*(1-power)/denominator
        qa1 = -r*(q*(1-power)-(q*K)*power*denominator)/denominator**2
        return a0, qa1

    with np.errstate(divide='ignore', invalid='ignore'):
        a, b, c = [sums(np.floor(v/q).astype(np.int64)) for v in [1, 2, 3]]
        value = 2*b[1]-a[1]-c[1]+a[0]+3*c[0]-4*b[0]
    for i in np.flatnonzero(np.abs(denominator) < 1e-6):
        k = np.arange(1, math.ceil(6/x[i])+1)
        v = k*x[i]/2
        value[i] = np.sum((-1.)**(k+1)*tent(v)*np.exp(1j*tau*v))
    return value


def replay():
    x = np.linspace(.017, 5.99, 211)
    m = moments(x)
    residual = 0.0
    for i, value in enumerate(x):
        k = np.arange(1, math.ceil(6/value)+1)
        v = k*value/2
        signs = (-1.)**(k+1)
        for n in range(5):
            residual = max(residual, abs(m[n, i]-np.sum(signs*tent(v)*v**n)))
    profile_error = 0.0
    rounded_error = 0.0
    for tau in [0, .1, 1, 2, 4]:
        p = continuum_profile(tau, x)
        for i, value in enumerate(x):
            k = np.arange(1, math.ceil(6/value)+1)
            v = k*value/2
            direct = np.sum((-1.)**(k+1)*tent(v)*np.exp(1j*tau*v))
            profile_error = max(profile_error, abs(p[i]-direct))
        for H in [2, 7, 16]:
            _, alpha = amplitudes(H, [tau/H])
            for i, value in enumerate(x):
                # Replay exact rational coincidences; floating ceil/floor
                # alone can move a discontinuity to the wrong grid cell.
                q = Fraction(str(float(value)))
                N = np.arange(H,3*H)
                before = np.array([(2*int(n)*q.denominator//(H*q.numerator)) % 2 for n in N])
                after = np.array([(2*(int(n)+1)*q.denominator//(H*q.numerator)) % 2 for n in N])
                finite = np.dot(alpha[0],after-before)*np.exp(1j*tau/H)
                k = range(1,math.ceil(6/q)+1)
                v = np.array([math.ceil(H*j*q/2)/H for j in k])
                direct = np.sum((-1.)**(np.arange(len(v))+2)*tent(v)*np.exp(1j*tau*v))
                rounded_error = max(rounded_error, abs(finite-direct))
            finite_grid = continuous_packet(H,alpha[0],x)*np.exp(1j*tau/H)
            bound = (1+abs(tau))*(6/x+1)/H
            if np.any(np.abs(finite_grid-p) > bound+2e-12):
                raise AssertionError('pointwise sampling bound failed')
    if max(residual, profile_error, rounded_error) > 2e-10:
        raise AssertionError('continuum profile regression failed')
    return {'momentVsDirectResidual': float(residual),
            'geometricProfileVsDirectResidual': float(profile_error),
            'literalFiniteVsRoundedJumpResidual': float(rounded_error)}


def main():
    a = argparse.ArgumentParser(description=__doc__)
    a.add_argument('--grid-points', type=int, default=524288)
    a.add_argument('--heights', type=float, nargs='+', default=[54.38832170192632, 60, 100])
    a.add_argument('--output', type=Path,
                   default=Path('.lake/suzuki-carry-mellin-limit/probe.json'))
    args = a.parse_args()
    lo, hi = -16.0, math.log(6)
    step = (hi-lo)/args.grid_points
    logs = lo+(np.arange(args.grid_points)+.5)*step
    x = np.exp(logs)
    m = moments(x)
    B = m[1]**2-m[0]*m[2]
    C = m[2]**2/4+m[0]*m[4]/12-m[1]*m[3]/3
    beta = .99995
    bb = complex(np.sum(np.exp(beta*logs)*B)*step)
    cb = complex(np.sum(np.exp(beta*logs)*C)*step)
    taus = [.05, .1, .2, .5, 1.0]
    mass = {t:np.abs(continuum_profile(t, x))**2 for t in sorted({0, *taus, *[2*t for t in taus]})}
    rows = []
    for y in args.heights:
        p = 1-1j*y
        bp = complex(np.sum(np.exp(p*logs)*B)*step)
        cp = complex(np.sum(np.exp(p*logs)*C)*step)
        coefficient = bp*cb-cp*bb
        determinants = []
        for tau in taus:
            fp = np.array([np.sum(np.exp(p*logs)*mass[t])*step for t in [0,tau,2*tau]])
            fb = np.array([np.sum(np.exp(beta*logs)*mass[t])*step for t in [0,tau,2*tau]])
            d = (fp[1]-fp[0])*(fb[2]-fb[0])-(fp[2]-fp[0])*(fb[1]-fb[0])
            determinants.append({'tau':tau,'determinant':[d.real,d.imag],
                                 'determinantOver_tau_power6':[d.real/tau**6,d.imag/tau**6],
                                 'leadingCoefficientTimes12':[12*coefficient.real,12*coefficient.imag]})
        rows.append({'height':y,'beta':beta,'B_p':[bp.real,bp.imag],'C_p':[cp.real,cp.imag],
                     'B_beta':[bb.real,bb.imag],'C_beta':[cb.real,cb.imag],
                     'coefficientWedge':[coefficient.real,coefficient.imag],
                     'determinants':determinants})
    report = {'scope':'Optional continuum/Taylor preflight, not a certificate',
              'gridPoints':args.grid_points,'algebraicReplay':replay(),
              'rows':rows,'allHeightNonvanishingProved':False,
              'uniformQuadratureErrorProof':False,'outwardRounded':False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    for r in rows:
        print(json.dumps({'height':r['height'],'coefficientWedge':r['coefficientWedge'],
                          'tau1Determinant':r['determinants'][-1]['determinant']}),flush=True)


if __name__ == '__main__':
    main()
