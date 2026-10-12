#!/usr/bin/env python3
"""High-precision root/jet diagnostic for the exploratory boundary model.

Arb encloses each evaluation of the boundary/Hurwitz expression. Its
identification with the literal Mellin integral is NOT a Lean theorem, so
these enclosures are not a certificate of an actual carry exception.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy as sp
from flint import acb, arb, ctx, dirichlet_char
import numpy as np


class BoundaryModel:
    def __init__(self, rows):
        self.b, self.s = sp.symbols('b s')
        self.X, self.Y = sp.symbols('X Y')
        self.terms = {}
        for name in ['B', 'C']:
            terms = []
            for row in rows:
                expr = sp.sympify(row[name]['MellinCoefficient_without_x_power_s'])
                polynomial = sp.Poly(sp.expand(expr * self.b**5), self.b)
                for (power,), coefficient in polynomial.terms():
                    terms.append((row['a'], row['modulus'],
                                  row['residue'] or row['modulus'],
                                  power - 5, coefficient))
            self.terms[name] = terms
        self.grouped = {}
        for name, terms in self.terms.items():
            grouped = {}
            for a, modulus, residue, exponent, coefficient in terms:
                shift = -exponent
                assert shift >= 0
                two = sp.Rational(2)**(-shift) / self.X
                three = sp.Rational(3)**(-shift) / self.Y
                if modulus == 2:
                    components = {'zeta': two if residue == 2 else 1-two}
                elif modulus == 4:
                    components = {'zeta': (1-two)/2,
                                  'L4': sp.Rational(1 if residue == 1 else -1, 2)}
                else:
                    assert modulus == 6
                    if residue in [1, 5]:
                        components = {'zeta': (1-two)*(1-three)/2,
                                      'L3': (1+two)*(1 if residue == 1 else -1)/2}
                    else:
                        components = {'zeta': two*(1-three)/2,
                                      'L3': two*(1 if residue == 2 else -1)/2}
                scale = {1: self.X, 2: self.X**2, 3: self.X*self.Y}[a]
                for kind, value in components.items():
                    key = kind, shift
                    grouped[key] = grouped.get(key, 0) + scale*coefficient*value
            self.grouped[name] = {key: sp.factor(value) for key, value in grouped.items()
                                  if sp.cancel(value) != 0}
            assert ('zeta', 0) not in self.grouped[name], 'Uncancelled zeta pole in model'

    def eval_rational(self, expr, parameter, extra=None):
        if extra is not None and expr in extra:
            return extra[expr]
        if expr == self.s:
            return parameter
        if expr.is_Rational:
            return acb(arb(int(expr.p)) / int(expr.q))
        if expr.is_Add:
            return sum(self.eval_rational(term, parameter, extra) for term in expr.args)
        if expr.is_Mul:
            result = acb(1)
            for term in expr.args:
                result *= self.eval_rational(term, parameter, extra)
            return result
        if expr.is_Pow and expr.args[1].is_Integer:
            return self.eval_rational(expr.args[0], parameter, extra)**int(expr.args[1])
        raise ValueError(f'Unexpected coefficient expression: {expr}')

    def coefficients(self, parameter):
        cached = {}
        result = {}
        for name, terms in self.terms.items():
            value = acb(0)
            for a, modulus, residue, exponent, coefficient in terms:
                key = (modulus, residue, exponent)
                if key not in cached:
                    cached[key] = (parameter - exponent).zeta(arb(residue) / modulus)
                value += self.eval_rational(coefficient, parameter) * \
                    acb(2*a)**parameter * acb(modulus)**(exponent-parameter) * cached[key]
            result[name] = value
        return result

    def grouped_coefficients(self, parameter):
        extra = {self.X: acb(2)**parameter, self.Y: acb(3)**parameter}
        cache, result = {}, {}
        for name, terms in self.grouped.items():
            value = acb(0)
            for (kind, shift), coefficient in terms.items():
                key = kind, shift
                if key not in cache:
                    argument = parameter+shift
                    cache[key] = argument.zeta() if kind == 'zeta' else \
                        argument.dirichlet_l(dirichlet_char(3, 2) if kind == 'L3' else
                                             dirichlet_char(4, 3))
                value += self.eval_rational(coefficient, parameter, extra)*cache[key]
            result[name] = value
        return result


def literal_cell_prefix(parameter, count):
    """Evaluate the proved polynomial-cell formula, independently of jumps.

    Long-double arithmetic is diagnostic, not outward rounding. Factoring
    out the common oscillatory phase avoids subtracting two large phases.
    """
    m, x = sp.symbols('m x')

    def prefix(j, d, residue):
        cutoff = (12 // d) * m + residue // d
        return (x / 2)**j * (sp.euler(j, 1) - (-1)**(residue // d) *
                             sp.euler(j, cutoff + 1)) / 2

    values = {'B': np.clongdouble(0), 'C': np.clongdouble(0)}
    parameter = np.clongdouble(parameter)
    for residue in range(12):
        first = residue if residue else 12
        n = np.arange(first, count + 1, 12, dtype=np.longdouble)
        quotient = (n - residue) / 12
        upper = np.longdouble(12) / n
        phase = np.exp(parameter * np.log(upper))
        log_ratio = -np.log1p(1 / n)
        moments = []
        for j in range(5):
            moments.append(sp.expand(2 * prefix(j+1, 3, residue) - prefix(j+1, 6, residue) -
                                      prefix(j+1, 2, residue) + prefix(j, 6, residue) +
                                      3 * prefix(j, 2, residue) - 4 * prefix(j, 3, residue)))
        polynomials = {'B': moments[1]**2 - moments[0]*moments[2],
                       'C': moments[2]**2/4 + moments[0]*moments[4]/12 -
                            moments[1]*moments[3]/3}
        for name, polynomial in polynomials.items():
            cell = np.zeros(n.shape, dtype=np.clongdouble)
            for (degree,), expression in sp.Poly(sp.expand(polynomial), x).terms():
                coefficients = sp.Poly(expression, m).all_coeffs()
                evaluated = np.zeros(n.shape, dtype=np.longdouble)
                for coefficient in coefficients:
                    evaluated = evaluated * quotient + \
                        np.longdouble(int(coefficient.p)) / np.longdouble(int(coefficient.q))
                cell += evaluated * upper**degree * \
                    (-np.expm1((parameter+degree) * log_ratio)) / (parameter+degree)
            values[name] += np.sum(phase * cell, dtype=np.clongdouble)
    return values


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--boundary', type=Path,
                        default=Path('.lake/suzuki-carry-mellin-limit/jets.json'))
    parser.add_argument('--height', default='202268.98326694674')
    parser.add_argument('--beta', default='0.9999785')
    parser.add_argument('--precision', type=int, default=256)
    parser.add_argument('--literal-cells', type=int, default=0,
                        help='Also cross-check this finite literal cell prefix (not a certificate).')
    parser.add_argument('--output', type=Path,
                        default=Path('.lake/suzuki-carry-determinant/refined-root.json'))
    args = parser.parse_args()
    ctx.prec = args.precision
    mp.mp.dps = 60
    model = BoundaryModel(json.loads(args.boundary.read_text())['boundaryRows'])

    def convert(value):
        return mp.mpc(mp.mpf(value.real.mid().str(70, radius=False)),
                      mp.mpf(value.imag.mid().str(70, radius=False)))

    def ratio(beta, height=mp.mpf(0)):
        parameter = acb(arb(mp.nstr(beta, 70)), arb(mp.nstr(-height, 70)))
        coefficients = model.grouped_coefficients(parameter)
        return convert(coefficients['C'] / coefficients['B'])

    height = mp.findroot(lambda y: ratio(1, y).imag,
                         mp.mpf(args.height), tol=mp.mpf('1e-50'))
    target = ratio(1, height).real
    beta = mp.findroot(lambda b: ratio(b).real - target,
                       mp.mpf(args.beta), tol=mp.mpf('1e-50'))
    pvalues = model.grouped_coefficients(acb(1, arb(mp.nstr(-height, 70))))
    bvalues = model.grouped_coefficients(acb(arb(mp.nstr(beta, 70))))
    wedge = pvalues['B'] * bvalues['C'] - pvalues['C'] * bvalues['B']
    report = {'scope': 'Arb-enclosed exploratory boundary model, not the literal cell certificate',
              'height': mp.nstr(height, 60), 'beta': mp.nstr(beta, 60),
              'ratio': mp.nstr(target, 60), 'pointWedge': str(wedge),
              'B_p': str(pvalues['B']), 'C_p': str(pvalues['C']),
              'B_beta': str(bvalues['B']), 'C_beta': str(bvalues['C']),
              'boundaryIdentificationProvedInLean': False,
              'actualExceptionalPointProved': False, 'numericalCertificate': False}
    # A sign-change/IVT audit of the MODEL, not an equality between the
    # model and the actual Lean Mellin coefficient. No Newton residual is
    # used as a root-existence proof.
    ylo, yhi = arb('202268.983266946747349770'), arb('202268.983266946747349772')
    blo, bhi = arb('0.99997855'), arb('0.99997856')
    ybox = arb('202268.983266946747349771', '0.000000000000000001')
    if abs(height-mp.mpf('202268.98326694675')) < mp.mpf('1e-8'):
        def enclosed_ratio(parameter):
            values = model.grouped_coefficients(parameter)
            assert not values['B'].contains(0), 'Model ratio denominator not separated'
            return values['C']/values['B']
        rlo, rhi = enclosed_ratio(acb(1,-ylo)), enclosed_ratio(acb(1,-yhi))
        rbox = enclosed_ratio(acb(1,-ybox))
        rblo, rbhi = enclosed_ratio(acb(blo)), enclosed_ratio(acb(bhi))
        subdivisions = 1000
        for index in range(subdivisions):
            center = blo+(2*index+1)*(bhi-blo)/(2*subdivisions)
            interval = center+arb(0, (bhi-blo)/(2*subdivisions))
            enclosed_ratio(acb(interval))
        opposite = (rlo.imag > 0 and rhi.imag < 0) or (rlo.imag < 0 and rhi.imag > 0)
        beta_bracket = (rblo.real > rbox.real and rbhi.real < rbox.real) or \
                       (rblo.real < rbox.real and rbhi.real > rbox.real)
        assert opposite and beta_bracket, 'The model interval/IVT gate was not enclosed'
        report['modelIntervalIVT'] = {'heightBracket': [str(ylo), str(yhi)],
            'betaBracket': [str(blo), str(bhi)],
            'heightEndpointImaginaryRatios': [str(rlo.imag), str(rhi.imag)],
            'heightIntervalRealRatio': str(rbox.real),
            'betaEndpointRealRatios': [str(rblo.real), str(rbhi.real)],
            'ratioDenominatorsSeparated': True, 'enclosedModelSignChanges': True,
            'betaIntervalSubdivisions': subdivisions,
            'actualMellinIdentificationProved': False,
            'LeanNumericalCertificate': False}
    if args.literal_cells:
        parameter = np.clongdouble(1) - np.clongdouble(1j) * np.longdouble(mp.nstr(height, 65))
        literal = literal_cell_prefix(parameter, args.literal_cells)
        report['literalPrefixCheck'] = {'cells': args.literal_cells,
            'B': str(literal['B']), 'C': str(literal['C']),
            'outwardRounded': False, 'numericalCertificate': False,
            'note': 'Independent polynomial-cell prefix; no jump/Hurwitz identification assumed.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
