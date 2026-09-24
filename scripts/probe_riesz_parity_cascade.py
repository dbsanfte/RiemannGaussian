#!/usr/bin/env python3
"""Optional continuous-density diagnostic across prime counts.

This is NOT a prime count, Lean proof, or arithmetic error estimate.
It retains fixed outer log-share bounds, integrates every ordered middle
simplex, and enumerates the complete truncated hinge. Its purpose is to
check whether the surplus of the selected five-prime packet is balanced
by other signs/classes, before proposing any additional formal machinery.
"""
import argparse
import itertools
import json
import math
from pathlib import Path

import numpy as np
from scipy.stats import qmc

from probe_riesz_parity_packet import PLO, PHI, RLO, RHI, triple_integral


def middle_box(power, seed, middle_count, lam):
    z = qmc.Sobol(middle_count+1, scramble=True, seed=seed).random_base2(power)
    p = PLO+(PHI-PLO)*z[:, 0]
    r = RLO+(RHI-RLO)*z[:, 1]
    remaining = 1-p-r-middle_count*r
    cuts = np.sort(z[:, 2:], axis=1)
    gaps = np.diff(np.column_stack((np.zeros(len(p)), cuts, np.ones(len(p)))), axis=1)
    middle = np.sort(r[:, None]+np.maximum(remaining, 0)[:, None]*gaps, axis=1)[:, ::-1]
    cofactor = np.column_stack((middle, r))
    assert np.all(1-p <= lam)
    d = lam-p
    hinge = np.zeros(len(p))
    # Vectorwise additions avoid a BLAS call for every individual subset.
    for subset in itertools.product((0, 1), repeat=middle_count+1):
        subtotal = np.zeros(len(p))
        for i, included in enumerate(subset):
            if included:
                subtotal += cofactor[:, i]
        hinge += (-1)**sum(subset)*np.maximum(0, d-subtotal)
    volume = (PHI-PLO)*(RHI-RLO)*np.maximum(remaining, 0)**(middle_count-1)
    volume /= math.factorial(middle_count-1)*math.factorial(middle_count)
    density = hinge*volume/(lam*p*np.prod(cofactor, axis=1))
    return {"prime_count": middle_count+2, "signed": float(np.mean(density)),
            "positive": float(np.mean(np.maximum(density, 0))),
            "negative_magnitude": float(np.mean(np.maximum(-density, 0)))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--power", type=int, default=17)
    parser.add_argument("--seeds", type=int, default=3)
    parser.add_argument("--max-primes", type=int, default=11)
    parser.add_argument("--odd-only", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    u = 10001/20000
    lam = -2*u*math.log(u)
    rows = []
    for count in range(3, args.max_primes+1, 2 if args.odd_only else 1):
        trials = [middle_box(args.power, seed, count-2, lam) for seed in range(args.seeds)]
        values = [x["signed"] for x in trials]
        row = {"prime_count": count, "signed_mean": float(np.mean(values)),
               "seed_spread": max(values)-min(values), "trials": trials}
        rows.append(row)
        print(json.dumps(row), flush=True)
    exact_triple, _ = triple_integral(lam)
    result = {"status": "continuous prime-density model; not certified or actual prime counts",
              "radius": u, "lambda": lam, "sample_power": args.power, "odd_only": args.odd_only,
              "triple_quadrature_crosscheck": exact_triple, "classes": rows,
              "partial_signed_sum": sum(x["signed_mean"] for x in rows),
              "warning": "No bound for omitted prime counts, other log-share boxes, or actual arithmetic error."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")


if __name__ == "__main__":
    main()
