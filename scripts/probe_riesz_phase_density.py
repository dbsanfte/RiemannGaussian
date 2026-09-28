#!/usr/bin/env python3
"""Optional audit of a resonant density error, never a literal prime-sum test.

The error is a*exp(-(u-1/2)*T)*cos(y*T). Its observation keeps the exact
factorial, phase and radial endpoints. The nonoscillating gamma mass is
evaluated with SciPy; the oscillating part uses the finite integer-gamma
formula at high precision. Numerical values are diagnostics, not certificates.
"""

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp
from scipy.special import gammainc


def normalized_upper_laplace(n, u, rate, endpoint):
    """u^(n+1) integral_endpoint^infinity T^n/n! exp(-rate*T) dT.

    Reverse the exact degree-n polynomial so successive terms have small
    modulus. The unused finite tail has a geometric majorant; report it.
    This floating-point bound is not a directed-rounding certificate.
    """
    z = rate*endpoint
    ratio = mp.mpf(n)/abs(z)
    assert ratio < 1
    term = mp.mpc(1)
    series = term
    omitted = mp.mpf(0)
    for j in range(1, n+1):
        term *= (n-j+1)/z
        series += term
        omitted = abs(term)*ratio/(1-ratio) if j < n else mp.mpf(0)
        if omitted < mp.mpf('1e-65'):
            break
    prefactor = mp.exp((n+1)*mp.log(u)+n*mp.log(endpoint)-mp.loggamma(n+1)-z)/rate
    return prefactor*series, abs(prefactor)*omitted


def row(n, u, y):
    lower = mp.mpf(39)*n/20
    upper = mp.mpf(203)*n/100
    mass = gammainc(n+1, float(u*upper))-gammainc(n+1, float(u*lower))
    left, left_err = normalized_upper_laplace(n, u, u+2j*y, lower)
    right, right_err = normalized_upper_laplace(n, u, u+2j*y, upper)
    alias = left-right
    error_per_amplitude = (mp.mpf(mass)+alias)/2
    return {
        'N': n,
        'gamma_mass_in_core': float(mass),
        'doubled_frequency_alias_re': float(alias.real),
        'doubled_frequency_alias_im': float(alias.imag),
        'finite_series_omitted_bound_diagnostic': float(left_err+right_err),
        'negative_amplitude_minus_one_fifth': {
            'normalized_re': float(-error_per_amplitude.real/5),
            'normalized_im': float(-error_per_amplitude.imag/5),
            'proved_limit': '-1/10',
        },
        'positive_amplitude_four': {
            'normalized_re': float(4*error_per_amplitude.real),
            'normalized_im': float(4*error_per_amplitude.imag),
            'proved_limit': '2',
        },
        'lean_exterior_bound_per_abs_amplitude': float(10000*(n+2)/(u*u*n*n)),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    mp.mp.dps = 85
    u, y = mp.mpf(10001)/20000, mp.mpf(54)
    rows = [row(n, u, y) for n in (256, 640, 1536, 4096, 8192, 32768, 131072, 1048576)]
    payload = {
        'scope': 'uncertified smooth-density error model; no actual primes or Riesz masks',
        'radius': '10001/20000',
        'height': 54,
        'radial_window': '39N/20 < T <= 203N/100',
        'error': 'a exp(-(u-1/2)T) cos(yT)',
        'rows': rows,
        'limitations': [
            'The exact error and its core-window limit are proved in Lean independently.',
            'No prime factors, incidence weights, allocation or sieve coefficients are modeled.',
            'Values are for the signed error, not for the entire positive density.',
            'This is not a proof or counterexample to either arithmetic endgame inequality.',
            'SciPy gamma values and mpmath truncation estimates are not certified intervals.',
        ],
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    print(json.dumps(payload, indent=2))
    if args.output:
        args.output.write_text(json.dumps(payload, indent=2)+'\n')


if __name__ == '__main__':
    main()
