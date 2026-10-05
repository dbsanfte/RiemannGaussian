#!/usr/bin/env python3
"""Optional analytic countermodel preflight; never an actual-prime certificate.

The exact component transform is proved in ZetaPrimeMomentChebyshev.
This records the source rate and the scale at which a fixed power ripple
fits a published subexponential PNT envelope. No arithmetic hypothesis is
inferred from this probe and it is not registered in ordinary CI.
"""
import argparse
import json
from pathlib import Path

import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    mp.mp.dps = 90
    u = mp.mpf(10001) / 20000
    y = mp.mpf(54)
    s = mp.mpc(mp.mpf(3) / 2, y)
    rho = s - u
    c = s - 1
    rows = []
    for order in (1, 16, 256, 640, 1536, 4096, 65536):
        # Exact Laplace transform of -exp((rho-1)*t)/rho.
        ek = -mp.power(u, -order-1) / rho
        ep = -mp.power(u, -order) / rho
        source = mp.power(u, order+1) * (s*ek-ep)
        rows.append({'order': order, 'componentSourceRe': mp.nstr(source.real, 35),
                     'componentSourceIm': mp.nstr(source.imag, 8),
                     'smoothSourceLogNorm': mp.nstr((order+1)*mp.log(abs(u/c)), 25),
                     'selectedLogSaddle': mp.nstr(order/u, 25)})
    scales = []
    delta = u-mp.mpf(1)/2
    for t in (1000000, 100000000, 1000000000, 10000000000):
        # Relative density ripple envelope 2 exp(-delta*t), compared with
        # Johnston--Yang 9.39 t^1.515 exp(-.8274 sqrt(t)).  This is a strength
        # comparison only; no equality of this model with actual psi is claimed.
        log_ratio = (mp.log(2) - delta*t - mp.log(mp.mpf('9.39'))
                     - mp.mpf('1.515')*mp.log(t) + mp.mpf('.8274')*mp.sqrt(t))
        scales.append({'logX': t, 'logRippleToPntEnvelope': mp.nstr(log_ratio, 25),
                       'rippleFitsEnvelope': log_ratio < 0})
    regions = []
    for label, cap, width in (
        ('existing discharged signed-pole', 2000,
         lambda h: mp.mpf(792)/(7625*h-2000)),
        ('BTY2026 Theorem 1: external analytic proof not imported', 3900,
         lambda h: 1/(mp.mpf('4.896')*h)),
        ('Yang2024 Littlewood: external analytic proof not imported', 8200,
         lambda h: mp.log(h)/(mp.mpf('21.233')*h)),
    ):
        regions.append({'input': label, 'illustrativeLogHeight': cap,
                        'width': mp.nstr(width(cap), 25),
                        'radiusMargin': mp.nstr(width(cap)-mp.mpf(51)/1000000, 25),
                        'numericalOnly': True})
    result = {'schema': 'prime-moment-error-frontier-probe-v1',
              'actualPrimeCertificate': False, 'cofinalArithmeticBound': False,
              'precisionDecimalDigits': mp.mp.dps, 'u': '10001/20000', 'y': 54,
              'component': '-exp((rho-1)t)/rho', 'momentRows': rows,
              'pntEnvelopeStrengthRows': scales, 'regionWidthPreflight': regions}
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    else:
        print(output, end='')


if __name__ == '__main__':
    main()
