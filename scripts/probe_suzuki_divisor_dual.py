#!/usr/bin/env python3
"""Screen finite Suzuki divisor certificates; floating-point exploration only.

Copyright (c) 2026 David Sanftenberg. Released under Apache 2.0.

Requires numpy, scipy, and mpmath. Every divisor constraint is checked at
each sampled cutoff. This is not an all-cutoff proof or an exact certificate.
The Lean interface is SuzukiLegendreDivisorDual.lean. Crucially, the trial
form MINIMIZES to the potential. We evaluate the actual mass center, or
subtract the exact convexity cost when using log(N).

Unrestricted finite weights can make every constraint an equality by
descending substitution. That diagnostic recovers the original arithmetic
value; it does not prove a lower bound. The search targets much smaller
piecewise-constant families, including dyadic interval refinements.
"""

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.optimize import linprog
from scipy.special import gammaln


def mangoldt_sieve(n):
    values = np.zeros(n + 1)
    composite = np.zeros(n + 1, dtype=bool)
    for p in range(2, n + 1):
        if composite[p]:
            continue
        composite[p * 2 :: p] = True
        power = p
        while power <= n:
            values[power] = math.log(p)
            power *= p
    return values[1:]


def interval_edges(n, family, size):
    # Isolate 1: its log is zero and its weight can enforce the d=1 constraint.
    edges = {0, 1, n}
    if family == "uniform":
        edges.update(n * j // size for j in range(1, size))
    elif family == "dyadic":
        high = n
        while high > 1:
            low = high // 2
            edges.update(low + (high - low) * j // size for j in range(size + 1))
            high = low
    elif family == "quotient":
        edges.update(n // q for q in range(1, size + 2))
        high = n // (size + 1)
        while high > 1:
            high //= 2
            edges.add(high)
    else:
        raise ValueError(family)
    return np.array(sorted(edges), dtype=np.int64)


def probe(n, family, size, center, lam, slope, intercept, shape="constant"):
    d = np.arange(1, n + 1)
    root_n = math.sqrt(n)
    log_d = np.log(d)
    mass = math.fsum(lam / np.sqrt(d)) - slope
    moment = math.fsum(lam * log_d / np.sqrt(d))
    optimum_r = 2 * math.log(mass / 2)
    r = optimum_r if center == "mass" else math.log(n)
    displacement = (r - optimum_r) / 2
    convex_cost = 2 * mass * (math.expm1(displacement) - displacement)
    potential = moment - 2 * mass * (math.log(mass / 2) - 1) + intercept
    target = (log_d - r) / np.sqrt(d)
    edges = interval_edges(n, family, size)
    multiples = edges[1:] // d[:, None] - edges[:-1] // d[:, None]
    if shape == "constant":
        # w(m) = coefficient[j] / sqrt(N) on (edges[j], edges[j+1]].
        matrix = multiples / root_n
        objective = (gammaln(edges[1:] + 1) - gammaln(edges[:-1] + 1)) / root_n
        repair_kernel = np.sum(matrix, axis=1)
        repair_columns = slice(None)
    elif shape == "log_affine":
        # w(m) = (a[j] + b[j]*log(m/N))/sqrt(m) on each interval.
        # Complete quotient cells have exactly this shape in the equality solution.
        prefixes = [np.r_[0, np.cumsum(log_d**power / np.sqrt(d))] for power in range(3)]
        lower = edges[:-1] // d[:, None]
        upper = edges[1:] // d[:, None]
        first = (prefixes[0][upper] - prefixes[0][lower]) / np.sqrt(d[:, None])
        second = (prefixes[1][upper] - prefixes[1][lower]) / np.sqrt(d[:, None])
        second += np.log(d / n)[:, None] * first
        matrix = np.c_[first, second]
        first_objective = prefixes[1][edges[1:]] - prefixes[1][edges[:-1]]
        second_objective = prefixes[2][edges[1:]] - prefixes[2][edges[:-1]]
        second_objective -= math.log(n) * first_objective
        objective = np.r_[first_objective, second_objective]
        repair_kernel = np.sum(first, axis=1)
        repair_columns = slice(0, len(edges) - 1)
    else:
        raise ValueError(shape)
    result = linprog(-objective, A_ub=matrix, b_ub=target,
                     bounds=(None, None), method="highs")
    if not result.success:
        return {"N": n, "family": family, "size": size, "error": result.message}
    coefficients = result.x.copy()
    violation = matrix @ coefficients - target
    repair = max(0.0, float(np.max(violation / repair_kernel))) + 1e-12
    coefficients[repair_columns] -= repair
    kernel = matrix @ coefficients
    slack = target - kernel
    linear_value = float(objective @ coefficients)
    certificate = (intercept + 4 * math.exp(r / 2) + slope * r
                   + linear_value - convex_cost)
    arithmetic_loss = float(lam @ slack)
    return {
        "N": n, "family": family, "size": size, "shape": shape, "center": center,
        "variables": len(coefficients), "r_minus_log_N": r - math.log(n),
        "actual_potential": potential, "certificate": certificate,
        "certificate_div_sqrt_N": certificate / root_n,
        "weighted_slack": arithmetic_loss, "convex_cost": convex_cost,
        "minimum_kernel_slack": float(np.min(slack)),
        "finite_identity_residual": potential - certificate - arithmetic_loss,
        "positive_basis_repair": repair,
        "interval_edges": edges.tolist(),
        "scaled_coefficients": coefficients.tolist(),
    }


def equality_diagnostic(n, lam, slope, intercept):
    """Full finite equality solution, used only to audit orientation and loss."""
    d = np.arange(1, n + 1)
    mass = math.fsum(lam / np.sqrt(d)) - slope
    r = 2 * math.log(mass / 2)
    target = (np.log(d) - r) / np.sqrt(d)
    weights = np.zeros(n + 1)
    for k in range(n, 0, -1):
        weights[k] = target[k - 1] - math.fsum(weights[2 * k :: k])
    kernel = np.array([math.fsum(weights[k::k]) for k in range(1, n + 1)])
    potential = (math.fsum(lam * np.log(d) / np.sqrt(d))
                 - 2 * mass * (math.log(mass / 2) - 1) + intercept)
    dual = intercept + 4 * math.exp(r / 2) + slope * r + math.fsum(weights[1:] * np.log(d))
    return {"N": n, "max_kernel_error": float(np.max(np.abs(kernel - target))),
            "potential_minus_dual": potential - dual,
            "purpose": "finite equality diagnostic, not an independent arithmetic bound"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoffs", type=int, nargs="+", default=[128, 512, 2048, 8192])
    parser.add_argument("--center", choices=["mass", "endpoint"], default="mass")
    parser.add_argument("--models", nargs="+", default=[
        "uniform:8:constant", "uniform:32:constant", "dyadic:1:constant",
        "dyadic:4:constant", "dyadic:16:constant", "dyadic:4:log_affine",
        "dyadic:16:log_affine", "quotient:8:log_affine", "quotient:32:log_affine"],
        help="family:size:shape, e.g. dyadic:16:log_affine")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if min(args.cutoffs) < 2:
        parser.error("cutoffs must be at least 2")
    models = []
    for model in args.models:
        try:
            family, size, shape = model.split(":")
            size = int(size)
            if family not in ["uniform", "dyadic", "quotient"] or size < 1:
                raise ValueError(model)
            if shape not in ["constant", "log_affine"]:
                raise ValueError(model)
        except ValueError:
            parser.error(f"invalid model: {model}")
        models.append((family, size, shape))
    mp.mp.dps = 50
    slope = float((mp.digamma(mp.mpf(1) / 4) - mp.log(mp.pi)) / 2)
    intercept = float(mp.zeta(2, mp.mpf(1) / 4) / 4 - 8)
    all_lam = mangoldt_sieve(max(args.cutoffs))
    rows = []
    for n in args.cutoffs:
        for family, size, shape in models:
            row = probe(n, family, size, args.center, all_lam[:n], slope, intercept, shape)
            rows.append(row)
            print(json.dumps({k: v for k, v in row.items()
                              if k not in ["interval_edges", "scaled_coefficients"]}), flush=True)
    report = {
        "status": "floating-point exploration, no all-cutoff theorem",
        "slope": slope, "intercept": intercept,
        "equality_diagnostic": equality_diagnostic(min(512, max(args.cutoffs)),
            all_lam[:min(512, max(args.cutoffs))], slope, intercept),
        "rows": rows,
    }
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
