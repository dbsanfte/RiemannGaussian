#!/usr/bin/env python3
"""Optional actual-prime regressions for the proved compensation box.

Primality witnesses are exact Proth certificates. Logarithms, phases and
factorial probabilities are numerical, not interval certificates. Chosen
examples do not estimate population density or the complete signed sum.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np

from probe_riesz_label_anatomy import check_certificate, length, proth_near_log, riesz
from probe_riesz_joint_masked import rectangle_values


def run(N, y):
    h = 1/(10*(mp.mpf(abs(y))+1))
    period = 2*mp.pi/abs(y)
    shift = mp.pi/abs(y)-2*N
    v = shift-mp.floor(shift/period)*period
    slopes = [mp.mpf(1)/25, mp.mpf(1)/10, mp.mpf(11)/50,
              mp.mpf(27)/50, mp.mpf(11)/10]
    primes, witnesses = [], []
    for i, slope in enumerate(slopes):
        start = slope*N+(v if i == 4 else 0)
        p, cert = proth_near_log(start+h/2)
        check_certificate(p, cert)
        assert start < mp.log(p) < start+h
        primes.append(p)
        witnesses.append(cert)
    logs = list(map(mp.log, primes))
    T, L = mp.fsum(logs), length(N)
    response = riesz(logs, L)
    coefficient = -T*response/L
    predicted = -T*logs[0]/L
    error = abs(coefficient-predicted)
    cosine = mp.cos(y*T)
    weight = float(rectangle_values(N, np.array([float(logs[-1]/T)]),
                                   np.array([float(logs[0]/T)]))[0])
    assert error < mp.mpf('1e-150')
    assert cosine < -mp.mpf('.5') and coefficient < -mp.mpf(2)/35*N
    assert h+v < mp.mpf(N)/1000 and weight > .5
    assert mp.mpf('1.37')*N < L < mp.mpf('1.4')*N
    assert all(p > N*N and x < L for p, x in zip(primes, logs))
    assert mp.mpf('1.95')*N < T <= mp.mpf('2.03')*N
    U = mp.mpf(10001)/20000
    log_atom = ((N+1)*mp.log(U)-mp.mpf('1.5')*T+N*mp.log(T)
                -mp.loggamma(N+1)+mp.log(coefficient*cosine)+mp.log(weight))
    return dict(N=N, y=y, log_width=mp.nstr(h, 30), shift=mp.nstr(v, 30),
                total_log_over_N=mp.nstr(T/N, 30), length_over_N=mp.nstr(L/N, 30),
                prime_log_slopes=[mp.nstr(x/N, 30) for x in logs],
                proth_certificates=witnesses, product_bit_length=math.prod(primes).bit_length(),
                coefficient=mp.nstr(coefficient, 30), cosine=mp.nstr(cosine, 30),
                rectangle_weight=weight, identity_error=mp.nstr(error, 10),
                log_source_normalized_single_atom=mp.nstr(log_atom, 30))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[1024, 2048])
    parser.add_argument('--heights', nargs='+', type=int, default=[54, 100])
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    mp.mp.dps = 600
    assert all(y != 0 for y in args.heights)
    paths = [Path(__file__), Path(__file__).with_name('probe_riesz_label_anatomy.py'),
             Path(__file__).with_name('probe_riesz_joint_masked.py')]
    report = dict(scope='Chosen actual-prime identity regressions, not a density or net-floor certificate',
                  theorem='RiemannGaussian.ZetaRieszCompensationSupply.eventually_retained_positive_supply',
                  arithmetic='Primality certificates checked exactly; transcendental and binomial values are uncertified numerical checks',
                  exclusions='Does not estimate other labels, counts, the joined signed target, or its complementary carrier',
                  hashes={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}, rows=[])
    for N in args.orders:
        for y in args.heights:
            report['rows'].append(run(N, y))
            print(f'checked N={N}, y={y}', flush=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
