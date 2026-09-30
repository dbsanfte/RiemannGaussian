#!/usr/bin/env python3
"""Optional floating-point probe of the exact selected-mode Gamma inversion.

This is exploration, not a certificate or a zero hypothesis. The Fourier
check uses the literal two-prime ordered quotient coefficient, including
its proper-power denominator. Height scans do not assert zeta zeros.
No complete cofactor, radial freezing, or phase norm replaces the response.
"""
import argparse
import itertools
import json
from pathlib import Path

import mpmath as mp


def hinge_average(j, u, x):
    if x <= 0:
        return mp.mpf(0)
    return (x * mp.gammainc(j, 0, u * x) / mp.factorial(j - 1)
            - j / u * mp.gammainc(j + 1, 0, u * x) / mp.factorial(j))


def gamma_tent(j, u, p, q, length):
    a, b = mp.log(p), mp.log(q)
    return (hinge_average(j, u, length) - hinge_average(j, u, length - a)
            - hinge_average(j, u, length - b) + hinge_average(j, u, length - a - b))


def weight(n, j, h, p, q, height):
    s = mp.mpf(3) / 2 + mp.j * height
    k = n + 1 - j - h
    # (-d/ds)^k [q^-s/(1-q^-s)] / k!, exactly.
    odds_moment = mp.log(q)**k / mp.factorial(k) * mp.polylog(-k, mp.exp(-s * mp.log(q)))
    return mp.log(p)**h / mp.factorial(h) * mp.exp(-s * mp.log(p)) * odds_moment


def fourier_tent(j, u, p, q, length):
    def integrand(x):
        if not x:
            return -2 * mp.log(p) * mp.log(q) / j
        character = (1-mp.exp(-mp.j*x*mp.log(p))) * (1-mp.exp(-mp.j*x*mp.log(q)))
        term = mp.exp(mp.j*x*length) * (u/(u+mp.j*x))**j * character / j
        return 2*mp.re(term)/x**2
    return -mp.quad(integrand, [0, mp.mpf('0.05'), mp.mpf('0.1'),
                               mp.mpf('0.2'), mp.mpf('0.5'), 1, 2, 4, 8, mp.inf])/(2*mp.pi)


def finite_cofactor_scan(n, j, h, u, length, primes, height):
    """Exact finite subset formula, numerically evaluated before norms."""
    k = n+1-j-h
    s = mp.mpf(3)/2 + mp.j*height
    moments = {p: [mp.log(p)**a/mp.factorial(a)*mp.polylog(-a, mp.exp(-s*mp.log(p)))
                   for a in range(k+1)] for p in primes}
    rows = {a: mp.mpc(0) for a in range(2, len(primes)+1)}
    kernel_ranges = {a: [] for a in rows}
    for i, r in enumerate(primes):
        for size in range(1, len(primes)-i):
            for middle in itertools.combinations(primes[i+1:], size):
                coefs = [mp.mpc(1)] + [mp.mpc(0)]*k
                for p in middle:
                    coefs = [sum(coefs[b]*moments[p][a-b] for b in range(a+1))
                             for a in range(k+1)]
                support = (r,)+middle
                averaged = mp.mpf(0)
                for count in range(len(support)+1):
                    for subset in itertools.combinations(support, count):
                        averaged += (-1)**count*hinge_average(j, u, length-sum(mp.log(p) for p in subset))
                coefficient = mp.log(r)**h/mp.factorial(h)*mp.exp(-s*mp.log(r))*coefs[k]
                rows[len(support)] += coefficient*averaged/j
                kernel_ranges[len(support)].append(averaged)
    return {'primes': list(primes), 'height': str(height),
            'counts': [{'cofactor_count': a, 'real': str(mp.re(value)), 'imag': str(mp.im(value)),
                        'gamma_riesz_min': str(min(kernel_ranges[a])),
                        'gamma_riesz_max': str(max(kernel_ranges[a]))} for a, value in rows.items()],
            'total_real': str(mp.re(sum(rows.values()))),
            'total_imag': str(mp.im(sum(rows.values())))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    mp.mp.dps = 65
    n, j, h, p, q = 100, 55, 1, 17, 23
    u = mp.mpf(10001)/20000
    length = 2*mp.log(mp.floor(u**(-n)/(n+1))+2)
    physical = gamma_tent(j, u, p, q, length)/j
    spectral = fourier_tent(j, u, p, q, length)
    scan = []
    for y in ['0', '54.1', '55', '56', '60', '80', '100']:
        coefficient = weight(n, j, h, p, q, mp.mpf(y))
        response = coefficient*physical
        scan.append({'height': y, 'weight_real_fraction': str(mp.re(coefficient)/abs(coefficient)),
                     'response_real': str(mp.re(response)), 'response_imag': str(mp.im(response))})
    result = {'status': 'uncertified numerical exploration; no zero hypothesis',
              'orders': {'N': n, 'j': j, 'h': h, 'middle': n+1-j-h},
              'primes': [p, q], 'u': str(u), 'literal_length': str(length),
              'gamma_tent_over_j': str(physical), 'fourier_response': str(spectral),
              'absolute_inversion_residual': str(abs(physical-spectral)),
              'height_scan': scan,
              'finite_all_count_scan': [finite_cofactor_scan(n, j, h, u, length,
                                        (17, 23, 29, 31, 37), mp.mpf(y)) for y in ['0', '60', '100']],
              'scope': 'Fixed rectangle atom of the ordered quotient, not the whole source carrier.'}
    content = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(content)
    print(content)


if __name__ == '__main__':
    main()
