#!/usr/bin/env python3
"""Independent checks of the optional Riesz binomial-tail evaluator.

Small cases use exact rational probabilities, not the tail recurrence.
Large cases compare against Arb's separate incomplete-beta implementation.
This validates numerical evaluation only, never continuum quadrature or a
prime-sum bound. Requires the optional requirements-riesz-balls.txt environment.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

from flint import arb, ctx, fmpq, fmpz
from riesz_binomial_balls import binomial_tail


def run():
    ctx.prec = 384
    exact_count = 0
    for n in (0, 1, 2, 17, 64):
        for p in (fmpq(0), fmpq(1, 37), fmpq(17, 37), fmpq(36, 37), fmpq(1)):
            for j in (-1, 0, 1, n//2, n, n+1):
                truth = sum((fmpq(fmpz.bin_uiui(n, k))*p**k*(1-p)**(n-k)
                             for k in range(max(j, 0), n+1)), fmpq(0))
                assert binomial_tail(arb(p), n, j).contains(truth), (n, p, j)
                exact_count += 1
    large = []
    for n in (65536, 64882, 62916):
        for j in (34407, 37684):
            for value in ('0.51', '0.525', '0.54', '0.55', '0.575', '0.59'):
                q = arb(value)
                start = time.monotonic()
                got = binomial_tail(q, n, j)
                new_time = time.monotonic()-start
                start = time.monotonic()
                with ctx.workprec(224):
                    reference = q.beta_lower(j, n-j+1, regularized=True)
                old_time = time.monotonic()-start
                assert reference.is_finite() and reference.rad() < arb('1e-55')
                assert got.overlaps(reference) and got.rad() < arb('1e-55')
                large.append(dict(n=n, j=j, q=value, overlap=True,
                                  tail_radius=str(got.rad()),
                                  recurrence_seconds=new_time, beta_seconds=old_time))
    # A ball straddling the mean tests the tail-selection branch itself.
    n, j = 65536, 34407
    q = arb(arb(j)/n, arb(2)**(-220))
    got = binomial_tail(q, n, j)
    with ctx.workprec(224):
        ref = q.beta_lower(j, n-j+1, regularized=True)
    assert got.overlaps(ref) and got.rad() < arb('1e-50')
    return dict(exact_rational_cases=exact_count, large_cases=large,
                mean_straddling_ball=True,
                scope='Finite binomial probabilities only; no carrier or continuum bound',
                source_sha256={name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                               for name in (Path(__file__).name, 'riesz_binomial_balls.py')})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = run()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
