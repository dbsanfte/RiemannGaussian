#!/usr/bin/env python3
"""Optional checks for the correlated owner-order quadrature.

Exact rational moment checks and independent beta/hypergeometric Fourier
references test the interpolation error budget. The large-order check is
for a pure Fourier moment, NOT the varying Riesz response, a masked packet,
or a prime sum. Keep outside normal CI and certificate verification.
"""
import argparse
from fractions import Fraction
import hashlib
import importlib.metadata
import json
import math
from pathlib import Path
import time

from flint import acb, arb, ctx, fmpq
from riesz_owner_gauss import hermite_fourier_bound, owner_rule, raw_moments


def display(value):
    with ctx.workprec(192):
        return str(value+0)


def rational_checks():
    checks = 0
    for M, lo, hi in [(1, 1, 1), (7, 2, 5), (13, 7, 9), (20, 4, 18)]:
        for k, value in enumerate(raw_moments(M, lo, hi, 13)):
            exact = sum((Fraction(math.comb(M, j)*math.comb(M-j, b)*(-1)**b,
                                  j+k+b)
                         for j in range(lo, hi+1) for b in range(M-j+1)), Fraction(0))
            truth = fmpq(exact.numerator, exact.denominator)
            # Avoid coercing truth into a rounded ball before containment.
            mid, rad = value.mid().fmpq(), value.rad().fmpq()
            assert mid-rad <= truth <= mid+rad, (M, lo, hi, k)
            checks += 1
    return checks


def independent_checks():
    """1F1 integrates each beta component independently of its moments."""
    rows = []
    ctx.prec = 2048
    M, lo, hi, q = 20, 8, 13, 12
    rule, _ = owner_rule(M, lo, hi, q)
    for frequency in (1, 10, 100):
        exact = sum(acb(0, frequency).hypgeom_1f1(j, M+1)/j
                    for j in range(lo, hi+1))
        approximate = sum(w*acb(0, frequency*x).exp() for x, w in rule)
        error = abs(approximate-exact)
        budget, defects = hermite_fourier_bound(M, lo, hi, rule, arb(frequency))
        assert error.upper() < budget.lower()
        rows.append(dict(trials=M, owner_orders=[lo, hi], nodes=q,
                         frequency=frequency, reference=display(exact),
                         observed_error=display(error), error_bound=display(budget),
                         interpolation_jet_defects=display(defects)))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=262144)
    parser.add_argument('--nodes', type=int, nargs='+', default=[128, 192])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.order < 10000 or min(args.nodes) < 2:
        parser.error('require order>=10000 and at least two nodes')
    started = time.monotonic()
    names = [Path(__file__).name, 'riesz_owner_gauss.py']
    hashes = lambda: {n: hashlib.sha256(Path(__file__).with_name(n).read_bytes()).hexdigest()
                      for n in names}
    frozen = hashes()
    ctx.prec = 512
    check_count = rational_checks()
    regression = independent_checks()
    n = args.order
    h = n//25-1
    M, lo, hi = n-h, (21*n+39)//40, 23*n//40
    rows = []
    for q in args.nodes:
        ctx.prec = max(4096, 32*q)
        rule, audit = owner_rule(M, lo, hi, q)
        # p=(1-r)*x: this is conservative for every 0<=r<=1.
        frequency = arb(3)/250*(arb(203)*n/100)
        bound, defects = hermite_fourier_bound(M, lo, hi, rule, frequency)
        row = dict(nodes=q, frequency=display(frequency), error_bound=display(bound),
                   interpolation_jet_defects=display(defects),
                   centered_moment_checks=audit['moment_checks'],
                   maximum_centered_moment_defect=display(
                       arb(audit['maximum_centered_moment_defect'])),
                   scope='Pure Fourier moment over the full positive conditional owner measure')
        rows.append(row)
        print(json.dumps(row), flush=True)
    assert hashes() == frozen, 'Source changed during the audit'
    out = dict(N=n, trials=M, owner_orders=[lo, hi], rational_moment_checks=check_count,
               independent_hypergeometric_checks=regression, rows=rows,
               source_sha256=frozen, seconds=time.monotonic()-started,
               versions={p: importlib.metadata.version(p) for p in
                         ('python-flint', 'numpy', 'scipy')},
               scope='External numerical interpolation audit only. Both Hermite-jet defects '
                     'and the pure-phase remainder are included. No full varying-amplitude '
                     'or physical-mask quadrature bound, arithmetic transfer or Lean theorem.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2)+'\n')


if __name__ == '__main__':
    main()
