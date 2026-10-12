#!/usr/bin/env python3
"""Optional phase/root preflight for the carry determinant.

This evaluates a finite boundary-series model with a nonuniform FFT. The
boundary identification is not yet a Lean theorem and floating output is
not a certificate. Candidates must be checked against the literal cell
series and rigorously enclosed before any exceptional/nonexceptional claim.
"""

import argparse
import json
from pathlib import Path

import finufft
import numpy as np
import sympy as sp
from scipy.optimize import brentq


def boundary_arrays(rows, ceiling):
    b, s = sp.symbols('b s')
    nodes, weights = [], []
    for row in rows:
        numbers = np.arange(row['residue'] or row['modulus'], ceiling + 1,
                            row['modulus'], dtype=np.float64)
        x = 2 * row['a'] / numbers
        columns = []
        for name, shifts in [('B', (2, 3, 4)), ('C', (4, 5, 6))]:
            expr = sp.cancel(sp.sympify(row[name]['MellinCoefficient_without_x_power_s']) *
                             sp.prod(s + j for j in shifts))
            polynomial = sp.Poly(expr, s)
            assert polynomial.degree() <= 1 or polynomial.is_zero
            for order in [1, 0]:
                values = sp.lambdify(b, polynomial.nth(order), 'numpy')(numbers)
                columns.append(x * np.broadcast_to(values, numbers.shape))
        nodes.append(np.log(x))
        weights.append(np.asarray(columns, dtype=np.complex128))
    return np.concatenate(nodes), np.concatenate(weights, axis=1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--boundary', type=Path,
                        default=Path('.lake/suzuki-carry-mellin-limit/jets.json'))
    parser.add_argument('--maximum-height', type=float, default=20000)
    parser.add_argument('--step', type=float, default=.02)
    parser.add_argument('--denominator-ceiling', type=int, default=200000)
    parser.add_argument('--refine-candidates', type=int, default=0,
                        help='Refine this many candidate crossings in the finite model.')
    parser.add_argument('--output', type=Path,
                        default=Path('.lake/suzuki-carry-determinant/phase-scan.json'))
    args = parser.parse_args()
    boundary = json.loads(args.boundary.read_text())
    nodes, weights = boundary_arrays(boundary['boundaryRows'], args.denominator_ceiling)
    size = 2 * 2 ** int(np.ceil(np.log2(args.maximum_height / args.step + 1)))
    transforms = finufft.nufft1d1(args.step * nodes, weights, size,
                                 eps=1e-11, isign=-1, nthreads=4)
    first = size // 2
    count = int(args.maximum_height / args.step) + 1
    heights = np.arange(count) * args.step
    s = 1 - 1j * heights
    ub, vb, uc, vc = transforms[:, first:first + count]
    B = (s * ub + vb) / ((s + 2) * (s + 3) * (s + 4))
    C = (s * uc + vc) / ((s + 4) * (s + 5) * (s + 6))
    ratio = C / B
    imaginary = ratio.imag
    indices = np.flatnonzero((imaginary[:-1] * imaginary[1:] < 0) & (heights[:-1] >= 54))
    candidates = []
    # The approximate beta interval is diagnostic only, not an enclosure.
    target = -.06674801714
    for index in indices:
        fraction = -imaginary[index] / (imaginary[index + 1] - imaginary[index])
        real = ratio[index].real + fraction * (ratio[index + 1].real - ratio[index].real)
        height = heights[index] + fraction * args.step
        candidates.append({'height': float(height), 'realRatio': float(real),
                           'distanceToTarget': float(abs(real - target)),
                           'bracket': [float(heights[index]), float(heights[index + 1])]})
    candidates.sort(key=lambda row: row['distanceToTarget'])
    refined = []
    if args.refine_candidates:
        def evaluate(height):
            parameter = 1 - 1j * height
            ub, vb, uc, vc = weights @ np.exp(-1j * height * nodes)
            bv = (parameter * ub + vb) / np.prod([parameter + j for j in (2, 3, 4)])
            cv = (parameter * uc + vc) / np.prod([parameter + j for j in (4, 5, 6)])
            return cv / bv

        for candidate in candidates[:args.refine_candidates]:
            lo, hi = candidate['bracket']
            root = brentq(lambda height: evaluate(height).imag, lo, hi, xtol=1e-10)
            value = evaluate(root)
            refined.append({'height': float(root), 'realRatio': float(value.real),
                            'imaginaryResidual': float(value.imag),
                            'distanceToTarget': float(abs(value.real - target)),
                            'bracket': [lo, hi]})
        refined.sort(key=lambda row: row['distanceToTarget'])
    report = {'scope': 'floating finite-boundary phase/root preflight',
              'maximumHeight': args.maximum_height, 'step': args.step,
              'denominatorCeiling': args.denominator_ceiling,
              'boundaryIdentificationProvedInLean': False,
              'numericalCertificate': False, 'outwardRounded': False,
              'imaginaryRatioCrossings': len(indices), 'closestCandidates': candidates[:40],
              'refinedCandidates': refined,
              'controlSamples': [{'height': float(heights[i]), 'B': [float(B[i].real), float(B[i].imag)],
                                 'C': [float(C[i].real), float(C[i].imag)]}
                                for i in [int(y / args.step) for y in [54, 100, 500, 1000]]
                                if i < count]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'crossings': len(indices), 'closest': candidates[:12],
                      'refined': refined[:12],
                      'certificate': False}), flush=True)


if __name__ == '__main__':
    main()
