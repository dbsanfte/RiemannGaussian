#!/usr/bin/env python3
"""Exact boundary bookkeeping before numerical Mellin-jet diagnostics.

The tent moment profiles are piecewise polynomials. Their knots are
2*a/b with a=1,2,3; the polynomial branches depend on b modulo 2*a.
This optional probe retains every coincident knot and derivative jump.
The Mellin/Hurwitz identification is exploratory, not a Lean theorem
or a numerical certificate. No actual-prime estimate is performed.
"""

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as S


DENOM, X, PARAM = S.symbols('b x s', positive=True)


def alternating_power(n, cutoff, parity):
    return (X/2)**n*(S.euler(n, 1)-parity*S.euler(n, cutoff+1))/2


def branch_moment(n, a, residue, right):
    values = []
    for j in [1, 2, 3]:
        remainder = (j*residue) % a
        cutoff = (j*DENOM-remainder)/a
        parity = (-1)**((j*residue)//a)
        if right and remainder == 0:
            cutoff -= 1
            parity = -parity
        values.append((alternating_power(n, cutoff, parity),
                       alternating_power(n+1, cutoff, parity)))
    aa, bb, cc = values
    return S.expand(2*bb[1]-aa[1]-cc[1]+aa[0]+3*cc[0]-4*bb[0])


def literal_moment(n, x):
    value = 0
    for k in range(1, int(S.ceiling(6/x))+1):
        v = k*x/2
        tent = max(0, min(v-1, 3-v))
        value += (-1)**(k+1)*tent*v**n
    return value


def boundary_rows():
    rows, replay_count = [], 0
    for a in [1, 2, 3]:
        for residue in range(2*a):
            if math.gcd(residue, a) != 1:
                continue
            sides = []
            for right in [False, True]:
                moments = [branch_moment(n, a, residue, right) for n in range(5)]
                for block in [1, 3, 7]:
                    b = residue+2*a*block
                    epsilon = S.Rational(1, 10000*b**3)
                    x = S.Rational(2*a, b)+(epsilon if right else -epsilon)
                    for n, polynomial in enumerate(moments):
                        residual = polynomial.subs({DENOM: b, X: x})-literal_moment(n, x)
                        if residual != 0:
                            raise AssertionError('exact rational branch replay failed')
                        replay_count += 1
                B = S.expand(moments[1]**2-moments[0]*moments[2])
                C = S.expand(moments[2]**2/4+moments[0]*moments[4]/12-
                             moments[1]*moments[3]/3)
                sides.append((B, C))
            row = {'a': a, 'residue': residue, 'modulus': 2*a}
            for index, name, degree in [(0, 'B', 4), (1, 'C', 6)]:
                difference = S.expand(sides[1][index]-sides[0][index])
                terms, jumps = [], []
                for order in range(degree+1):
                    jump = S.factor(S.diff(difference, X, order).subs(X, 2*a/DENOM))
                    if jump == 0:
                        continue
                    jumps.append([order, str(jump)])
                    terms.append((-1)**(order+1)*jump*(2*a/DENOM)**order/
                                 S.prod(PARAM+j for j in range(order+1)))
                row[name] = {'derivativeJumps': jumps,
                             'MellinCoefficient_without_x_power_s': str(S.factor(sum(terms)))}
            rows.append(row)
    return rows, replay_count


def model_coefficient(rows, parameter, name):
    result = mp.mpc(0)
    for row in rows:
        modulus, residue, a = row['modulus'], row['residue'], row['a']
        expr = S.sympify(row[name]['MellinCoefficient_without_x_power_s'],
                        locals={'s': PARAM, 'b': DENOM})
        polynomial = S.Poly(S.expand(expr*DENOM**5), DENOM)
        for (power,), coefficient in polynomial.terms():
            exponent = power-5
            c = S.lambdify(PARAM, coefficient, modules='mpmath')(parameter)
            result += c*mp.power(2*a, parameter)*mp.power(modulus, exponent-parameter)*\
                mp.zeta(parameter-exponent, mp.mpf(residue or modulus)/modulus)
    return result


def complex_json(value):
    return [mp.nstr(value.real, 35), mp.nstr(value.imag, 35)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--heights', nargs='+', default=['54.38832170192632', '60', '100'])
    parser.add_argument('--beta', default='0.99995')
    parser.add_argument('--output', type=Path,
                        default=Path('.lake/suzuki-carry-mellin-limit/jets.json'))
    args = parser.parse_args()
    mp.mp.dps = 60
    rows, replay_count = boundary_rows()
    beta = mp.mpf(args.beta)
    bb, cb = [model_coefficient(rows, beta, name) for name in ['B', 'C']]
    samples = []
    for text in args.heights:
        p = 1-mp.j*mp.mpf(text)
        bp, cp = [model_coefficient(rows, p, name) for name in ['B', 'C']]
        sample = {'height': text, 'B_p': complex_json(bp), 'C_p': complex_json(cp),
                  'B_beta': complex_json(bb), 'C_beta': complex_json(cb),
                  'coefficientWedge': complex_json(bp*cb-cp*bb)}
        samples.append(sample)
        print(json.dumps(sample), flush=True)
    report = {'scope': 'optional symbolic boundary/Mellin diagnostic',
              'boundaryRows': rows, 'exactRationalMomentBranchReplays': replay_count,
              'beta': args.beta, 'samples': samples,
              'MellinBoundaryFormulaProvedInLean': False,
              'actualContinuumFourthOrderExpansionProvedInLean': False,
              'allHeightNonvanishingProved': False, 'outwardRounded': False,
              'numericalCertificate': False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
