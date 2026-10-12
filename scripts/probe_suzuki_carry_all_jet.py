#!/usr/bin/env python3
"""Optional preflight of the all-jet spectral bypass.

The literal tent profile is evaluated independently of the proposed
regularized lag representation. Floating quadrature does not certify the
identity or a nonzero source. Nothing here runs in ordinary CI.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.integrate import simpson


def literal_profile(tau, x):
    step = x / 2
    q = -np.exp(1j * tau * step)
    rows = []
    for knot in (1, 2, 3):
        count = np.floor(knot / step)
        # Using parity separately avoids loss in pi*count at small x.
        power = np.where(count % 2 == 0, 1, -1) * np.exp(1j * tau * step * count)
        zero = -q * (1 - power) / (1 - q)
        first = -step * q * (1 - power - count * power * (1 - q)) / (1 - q)**2
        rows.append((zero, first))
    (z1, f1), (z2, f2), (z3, f3) = rows
    return 2*f2-f1-f3+z1+3*z3-4*z2


def overlap(v):
    return np.where(v <= 1, 2/3-v*v+v**3/2, (2-v)**3/6)


def quadrature_remainder(v, orders):
    step = v[:, None] / orders[None, :]
    small = v <= 1
    result = np.zeros(step.shape)
    knots = [np.ones_like(v), 2-v, np.full_like(v, 2), 3-v]
    linear = [v, -2*(1-v), -2*(1-v), v]
    quadratic = [-np.ones_like(v), np.full_like(v, 2), np.full_like(v, -2), np.ones_like(v)]
    # On 1<=v<=2 only the first and last knots occur.
    linear = [np.where(small, row, 2-v if i in (0, 3) else 0)
              for i, row in enumerate(linear)]
    quadratic = [np.where(small, row, 1 if i == 0 else -1 if i == 3 else 0)
                 for i, row in enumerate(quadratic)]
    for a, c, d in zip(knots, linear, quadratic):
        share = np.mod(a[:, None]/step, 1)
        b2 = share*share-share+1/6
        b3 = share*(share-1)*(share-.5)
        result -= step/2*c[:, None]*b2+step*step/3*d[:, None]*b3
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--height', type=float, default=54)
    parser.add_argument('--tau', type=float, default=.25)
    parser.add_argument('--lag-ceiling', type=int, default=4096)
    parser.add_argument('--log-grid', type=int, default=32769)
    parser.add_argument('--literal-grid', type=int, default=1000001)
    parser.add_argument('--output', type=Path,
                        default=Path('.lake/suzuki-carry-determinant/all-jet-preflight.json'))
    args = parser.parse_args()
    s = 1-1j*args.height
    ts = np.linspace(-14, np.log(6), args.literal_grid)
    xs = np.exp(ts)
    contrast = np.abs(literal_profile(args.tau, xs))**2-np.abs(literal_profile(0, xs))**2
    literal = simpson(np.exp(s*ts)*contrast, x=ts)
    logs = np.linspace(-14, np.log(2), args.log_grid)
    vs = np.exp(logs)
    hs = np.arange(1, args.lag_ceiling+1, dtype=float)
    weights = np.where(hs % 2 == 0, 1, -1)*np.exp(-s*np.log(hs))
    remainder = np.empty(vs.shape, dtype=complex)
    for start in range(0, len(vs), 256):
        sub = vs[start:start+256]
        remainder[start:start+len(sub)] = quadrature_remainder(sub, hs) @ weights
    mp.mp.dps = 50
    eta = complex((1-mp.power(2, 2-s))*mp.zeta(s-1))
    density = -eta*overlap(vs)/vs+remainder
    spectral = 2**(s+1)*simpson(np.exp(s*logs)*(np.cos(args.tau*vs)-1)*density, x=logs)
    # Direct finite-grid replay of the ordinary overlap sum.
    replays = []
    for v in (.017, .12, 2/3, .99, 1.2, 1.75):
        for h in (1, 2, 17, 103):
            grid = np.arange(int(np.floor(3*h/v))+1)*v/h
            tent = lambda t: np.maximum(0, np.minimum(t-1, 3-t))
            direct = np.sum(tent(grid)*tent(grid+v))
            predicted = h/v*overlap(np.array(v))+quadrature_remainder(np.array([v]), np.array([h]))[0, 0]
            replays.append(float(abs(direct-predicted)))
    report = {'scope': 'floating all-jet spectral preflight, not a Lean bridge',
              'height': args.height, 'tau': args.tau, 'lagCeiling': args.lag_ceiling,
              'literalContrast': [literal.real, literal.imag],
              'spectralContrast': [spectral.real, spectral.imag],
              'difference': float(abs(literal-spectral)),
              'ordinaryQuadratureReplayMaxError': max(replays),
              'smallLagBulkCoefficient': [eta.real, eta.imag],
              'literalSpectralIdentityProved': False, 'outwardRounded': False,
              'numericalCertificate': False, 'campaignDetectorClosed': False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
