#!/usr/bin/env python3
"""Optional floating source-mode scan at the literal prime-density saddle.

Tests theta=2*delta, alongside exact selected-pole phase matching.
For huge N the weighted factorial sums are approximated by exact smooth
integrals with an explicit first-derivative Riemann error formula. This
formula and the floating evaluations are NOT interval-certified or Lean
assumptions. No actual primes, zeros or native carrier are evaluated here.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp


def response(n: int, u: mp.mpf) -> dict:
    eta = mp.mpf(3)/100
    d = eta/mp.sqrt(n+1)
    theta = 2*d
    psi = theta-mp.atan(d/u)
    r = u/mp.sqrt(u*u+d*d)
    K = 13*n//32
    # Exact moving floor for moderate orders; huge-order replacement has
    # the recorded bound 0<L_N-L0_N<4*(N+1)*u**N.
    log_K = -n*mp.log(u)-mp.log(n+1)
    if n <= 65536:
        U = mp.mpf(10001)/20000
        if u == mp.mpf(1)/2:
            integer = 2**n//(n+1)
        elif u == U:
            integer = 20000**n//(10001**n*(n+1))
        else:
            integer = 40000**n//(20001**n*(n+1))
        L = 2*mp.log(integer+2)
        floor_error_log10 = None
    else:
        L = 2*log_K
        floor_error_log10 = (mp.log(4)-log_K)/mp.log(10)
    F = (n+1)/(u*L)

    def integral(omega, a, b):
        if abs(omega) < mp.mpf('1e-30'):
            return mp.log((1-a)/(1-b))
        c = 2*omega
        return (mp.cos(omega)*(mp.ci(c*(1-a))-mp.ci(c*(1-b)))
                +mp.sin(omega)*(mp.si(c*(1-a))-mp.si(c*(1-b))))

    trace = mp.sin(n*psi)/(n*mp.sin(psi)) if psi else mp.mpf(1)
    w1, w2 = (n+1)*psi, (n+2)*psi
    a, b = mp.mpf(K)/(n+1), mp.mpf(n-K)/(n+1)
    v = mp.mpf(n+1-K)/(n+2)
    central = integral(w1, a, b)
    successor = integral(w2, 0, v)
    value = r**(n+1)*(trace+central-r*F*successor)
    # Right-endpoint rule error: width*sup|g'|/(2*order).
    ec = (b-a)/(2*(n+1))*(2*abs(w1)/(1-b)+1/(1-b)**2)
    ep = v/(2*(n+2))*(2*abs(w2)/(1-v)+1/(1-v)**2)
    error = r**(n+1)*(ec+r*abs(F)*ep)
    exact = None
    if n <= 65536:
        central_sum = mp.fsum(mp.cos((2*k-n-1)*psi)/(n+1-k)
            for k in range(K+1, n-K+1))
        successor_sum = mp.fsum(mp.cos((2*k-n-2)*psi)/(n+2-k)
            for k in range(1, n+2-K))
        exact = r**(n+1)*(trace+central_sum-r*F*successor_sum)
        assert abs(exact-value) < error
    return dict(theta=theta, delta=d, angular_mismatch=psi,
        accumulated_mismatch=w1, source_model_response=value,
        finite_sum_riemann_error_formula=error, moderate_order_direct_sum=exact,
        log10_floor_length_error_upper=floor_error_log10)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/riesz-physical-saddle-probe.json'))
    args = parser.parse_args()
    rows = []
    for num, den in [(1, 2), (20001, 40000), (10001, 20000)]:
        for n in [640, 4096, 65536, 10**10, 10**12, 10**14, 10**16]:
            with mp.workdps(75):
                a = response(n, mp.mpf(num)/den)
            # Only repeat the closed integral at higher precision. The
            # moderate exact sums are independently bounded controls.
            with mp.workdps(110):
                b = response(n, mp.mpf(num)/den)
                error = abs(a['source_model_response']-b['source_model_response'])
                assert error < mp.mpf('1e-40')
                row = dict(u=[num, den], N=n, **{
                    k: mp.nstr(value, 35) if value is not None else None
                    for k, value in b.items()}, precision_crosscheck_absolute_error=mp.nstr(error, 10))
            rows.append(row)
    output = dict(schema='riesz-physical-saddle-floating-v1',
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        precisions_decimal=[75, 110], eta=[3, 100], angle='2*delta',
        interval_certified=False, prime_samples=False, actual_zeros=False,
        native_carrier_bound=False, proof_dependency=False, ordinary_ci=False,
        row_count=len(rows), rows=rows)
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(dict(rows=len(rows), last=rows[-1]), indent=2))


if __name__ == '__main__':
    main()
