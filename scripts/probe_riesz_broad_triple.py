#!/usr/bin/env python3
"""Optional broad-triple capacity diagnostic, never a proof dependency.

Integrate the exact continuous triple coefficient over its share band.
This is not a discrete-prime, phase, allocation, or source-scale estimate.
The accompanying Lean bound uses literal prime windows and exact sixfold
incidence instead. Central five-prime inputs remain untrusted until their
separate optional verification and arithmetic transfer have completed.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

from scipy.integrate import quad


def model(low, high, lam):
    def inner(x):
        a, b = max(low, 1-x-high), min(high, 1-x-low)
        if a >= b:
            return 0.0
        def density(y):
            z = 1-x-y
            riesz = 1-2*lam+sum(max(lam-1+p, 0) for p in (x, y, z))
            return -riesz/(6*lam*x*y*z)
        return quad(density, a, b, epsabs=1e-12, epsrel=1e-10)[0]
    seams = sorted({low, high, 1-low-high, 1-2*low, 1-2*high})
    cuts = [x for x in seams if low <= x <= high]
    return sum(quad(inner, a, b, epsabs=1e-12, epsrel=1e-10)[0]
               for a, b in zip(cuts, cuts[1:]))


def main():
    rows = []
    for lam in (0.69, 0.693, 0.694):
        for low, high in ((997/3000, 1003/3000), (31/100, 7/20)):
            rows.append(dict(cutoff_ratio=lam, share_low=low, share_high=high,
                             model_coefficient_per_total_log=model(low, high, lam)))
    mass = Q(13, 100)**2*Q(67, 20)/6
    coefficient = Q(51, 100)*mass
    assert mass <= Q(19, 2000) and coefficient <= Q(1, 200)
    # Exact scalar arithmetic, not verification of the five-prime premise.
    credit = Q(12965, 100000)
    debit = Q(121003, 1000000)+Q(1, 200)
    lo, hi = Q(99, 100)*credit, Q(501, 500)*Q(1001, 1000)*debit
    margin = lo-hi-Q(8, 10000)*(lo+hi)
    assert margin > Q(1, 1000)
    payload = dict(
        scope="uncertified continuum diagnostic; the Lean literal bound is independent",
        rows=rows,
        rational_mass_budget=str(mass), rational_coefficient_budget=str(coefficient),
        conditional_central_credit=str(credit), conditional_period_margin=str(margin),
        limitations=[
            "Quadrature errors are not certified; these rows are not arithmetic prime-sum bounds.",
            "No radial, original-phase, allocation, or source-scale transport is inferred.",
            "The proposed central credit is not proved by this script or its rational comparisons.",
            "The broad band does not include all triple shapes or any other prime-count class."],
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    out = Path(__file__).resolve().parents[1]/"docs/riesz-broad-triple-probe.json"
    out.write_text(json.dumps(payload, indent=2)+"\n")
    print(json.dumps(payload, indent=2))


if __name__ == '__main__':
    main()
