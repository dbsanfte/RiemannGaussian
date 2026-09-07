#!/usr/bin/env python3
"""Explore the complete finite eta translate budget; output is not a proof.

For r_j in (0,1], a_j=-log(r_j), and real coefficients c_j, this computes
exact interval formulas in floating point and compares exact coefficient laws with numerical minimization of
  1 + c^T G_N c - 2 b^T c + (sum |c_j|)^2/(2N+1),
where b_j=max(0,log(2r_j)). The mathematical identification with the
complete continuous residual is in EtaTranslatedFiniteResidual.lean;
EtaRationalTranslateGram.lean provides an exact rational checking interface.

Requirements: numpy and scipy (tested with 2.2.6 and 1.15.3).
Example:
  python scripts/search_eta_translate_coefficients.py --dimensions 4 16 64 \
      --solvers canonical free --output /tmp/eta-coefficients.json
The moebius_log candidate implements EtaMoebiusTrialPenalty.lean on
d=2^k physical grids, with arithmetic cutoff M=k+1 and a balanced
logarithmic taper. Use --solvers canonical moebius_log to compare it
with the minimizer. The default eta cutoff agrees with the Lean schedule
for d>=4; use --cutoff 4 or 16 for its d=1 or d=2 stages.

The output includes coefficients, the residual, the full tail allowance,
and numerical optimization diagnostics. It certifies no zeta zero region.
"""
import argparse
import json
import time
from pathlib import Path

import numpy as np
import scipy
from scipy.optimize import minimize


def intervals(scale, cutoff):
    """Actual finite colour intervals in x=exp(-t), clipped at 1/(2N+1)."""
    indices = np.arange(cutoff, dtype=float)
    lower = np.maximum(1.0 / (2 * cutoff + 1), scale / (2 * indices + 2))
    upper = np.minimum(1.0, scale / (2 * indices + 1))
    keep = upper > lower
    return lower[keep][::-1], upper[keep][::-1]


def primitive(points, lower, upper):
    """Mass of the disjoint interval union to the left of each point."""
    if len(lower) == 0:
        return np.zeros_like(points)
    masses = np.r_[0.0, np.cumsum(upper - lower)]
    completed = np.searchsorted(upper, points, side="right")
    next_index = np.minimum(completed, len(lower) - 1)
    partial = np.where(completed < len(lower), np.maximum(0.0, points - lower[next_index]), 0.0)
    return masses[completed] + partial


def finite_gram(scales, cutoff):
    """Every pairwise overlap, integrated without sampling a time grid."""
    bands = [intervals(float(scale), cutoff) for scale in scales]
    dimension = len(scales)
    gram = np.empty((dimension, dimension))
    for j, (lower_j, upper_j) in enumerate(bands):
        gram[j, j] = (upper_j - lower_j).sum()
        for k in range(j):
            lower_k, upper_k = bands[k]
            entry = (primitive(upper_j, lower_k, upper_k) - primitive(lower_j, lower_k, upper_k)).sum()
            gram[j, k] = gram[k, j] = entry
    return gram


def moebius_log_coefficients(dimension):
    """Numerical evaluation of the exact balanced logarithmic candidate law."""
    if dimension < 1 or dimension & (dimension - 1):
        raise ValueError("The logarithmic candidate requires a power-of-two dimension.")
    stage = dimension.bit_length() - 1
    arithmetic_cutoff = stage + 1
    mu = np.ones(arithmetic_cutoff + 1, dtype=np.int64)
    mu[0] = 0
    prime = np.ones(arithmetic_cutoff + 1, dtype=bool)
    for p in range(2, arithmetic_cutoff + 1):
        if prime[p]:
            mu[p::p] *= -1
            mu[p * p::p * p] = 0
            prime[p * p::p] = False
    n = np.arange(1, arithmetic_cutoff + 1)
    weights = (1 - np.log(n) / np.log(arithmetic_cutoff)
               if arithmetic_cutoff > 1 else np.zeros(1))
    harmonic = np.r_[0.0, np.cumsum(mu[1:] * weights / n)]
    denominators = np.arange(1, dimension + 2)
    x = dimension / denominators
    prefix_indices = np.minimum(arithmetic_cutoff, dimension // denominators)
    values = np.where(x >= 1, x * (harmonic[prefix_indices] - harmonic[-1]), 0.0)
    return values[:-1] - values[1:]


def search(scales, cutoff, label, solver="free"):
    scales = np.asarray(scales, dtype=float)
    if cutoff < 1 or len(scales) < 1 or np.any(scales <= 0) or np.any(scales > 1):
        raise ValueError("Require N>=1 and a nonempty family of scales in (0,1].")
    started = time.monotonic()
    gram = finite_gram(scales, cutoff)
    pairing = np.maximum(0.0, np.log(2 * scales))
    tail_factor = 1.0 / (2 * cutoff + 1)
    dimension = len(scales)

    if solver == "moebius_log":
        if label != "uniform_scale" or not np.array_equal(scales, np.arange(1, dimension + 1) / dimension):
            raise ValueError("The logarithmic candidate requires the uniform physical scale grid.")
        coefficients = moebius_log_coefficients(dimension)
        stage = dimension.bit_length() - 1
        diagonal = (dimension + 1) * tail_factor
        regularized = gram + diagonal * np.eye(dimension)
        canonical = np.linalg.solve(regularized, pairing)
        residual = float(1 + coefficients @ (gram @ coefficients) - 2 * pairing @ coefficients)
        coefficient_norm = float(np.abs(coefficients).sum())
        tail = float(tail_factor * coefficient_norm ** 2)
        penalty = float(diagonal * (coefficients @ coefficients))
        score = residual + penalty
        deficit = float(1 - pairing @ canonical)
        difference = coefficients - canonical
        gap = float(difference @ (regularized @ difference))
        return {
            "grid": label, "solver": solver, "dimension": dimension, "cutoff": cutoff,
            "stage": stage, "arithmetic_cutoff": stage + 1,
            "matches_lean_cutoff": cutoff == 4 * dimension ** 2,
            "budget": residual + tail, "finite_residual": residual,
            "tail_allowance": tail, "coefficient_l1": coefficient_norm,
            "coefficient_sum": float(coefficients.sum()), "regularization": diagonal,
            "coefficient_square_allowance": penalty, "ridge_objective": score,
            "proved_stage_allowance": ((stage + 1) ** 2 / dimension
                                       if cutoff == 4 * dimension ** 2 else None),
            "canonical_deficit": deficit, "canonical_objective_gap": gap,
            "comparison_identity_error": abs(score - deficit - gap),
            "ridge_gradient_max": float(np.max(np.abs(2 * (regularized @ coefficients - pairing)))),
            "active_coefficients": int((abs(coefficients) > 1e-7).sum()),
            "seconds": time.monotonic() - started,
            "scales": scales.tolist(), "coefficients": coefficients.tolist(),
        }

    def objective(split):
        # c=u-v, u,v>=0. The penalty makes shared positive mass costly.
        coefficients = split[:dimension] - split[dimension:]
        gradient = gram @ coefficients - pairing
        tail_gradient = tail_factor * split.sum()
        value = 1 + coefficients @ (gram @ coefficients) - 2 * pairing @ coefficients
        value += tail_factor * split.sum() ** 2
        return value, np.r_[2 * (gradient + tail_gradient), 2 * (-gradient + tail_gradient)]

    if solver == "canonical":
        diagonal = (dimension + 1) * tail_factor
        regularized = gram + diagonal * np.eye(dimension)
        coefficients = np.linalg.solve(regularized, pairing)
        residual = float(1 + coefficients @ (gram @ coefficients) - 2 * pairing @ coefficients)
        coefficient_norm = float(np.abs(coefficients).sum())
        tail = float(tail_factor * coefficient_norm ** 2)
        deficit = float(1 - pairing @ coefficients)
        square_allowance = float(diagonal * (coefficients @ coefficients))
        return {
            "grid": label, "solver": solver, "dimension": dimension, "cutoff": cutoff,
            "budget": residual + tail, "finite_residual": residual,
            "tail_allowance": tail, "coefficient_l1": coefficient_norm,
            "coefficient_sum": float(coefficients.sum()), "regularization": diagonal,
            "resolvent_deficit": deficit, "coefficient_square_allowance": square_allowance,
            "resolvent_identity_error": abs(residual + square_allowance - deficit),
            "normal_equation_error": float(np.max(np.abs(regularized @ coefficients - pairing))),
            "active_coefficients": int((abs(coefficients) > 1e-7).sum()),
            "gram_condition": float(np.linalg.cond(gram)), "seconds": time.monotonic() - started,
            "scales": scales.tolist(), "coefficients": coefficients.tolist(),
        }

    initial = np.zeros(2 * dimension)
    initial[np.argmax(scales)] = 1
    result = minimize(objective, initial, method="L-BFGS-B", jac=True,
                      bounds=[(0, None)] * (2 * dimension),
                      options={"maxiter": 20000, "ftol": 1e-14, "gtol": 1e-10, "maxls": 50})
    coefficients = result.x[:dimension] - result.x[dimension:]
    residual = 1 + coefficients @ (gram @ coefficients) - 2 * pairing @ coefficients
    coefficient_norm = np.abs(coefficients).sum()
    tail = tail_factor * coefficient_norm ** 2
    _, gradient = objective(result.x)
    projected_gradient = np.where(result.x > 1e-10, gradient, np.minimum(gradient, 0.0))
    return {
        "grid": label, "solver": solver, "dimension": dimension, "cutoff": cutoff,
        "budget": float(residual + tail), "finite_residual": float(residual),
        "tail_allowance": float(tail), "coefficient_l1": float(coefficient_norm),
        "coefficient_sum": float(coefficients.sum()), "optimizer_success": bool(result.success),
        "optimizer_message": str(result.message), "iterations": int(result.nit),
        "projected_gradient_max": float(np.max(np.abs(projected_gradient))),
        "active_coefficients": int((abs(coefficients) > 1e-7).sum()),
        "gram_condition": float(np.linalg.cond(gram)), "seconds": time.monotonic() - started,
        "scales": scales.tolist(), "coefficients": coefficients.tolist(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--dimensions", type=int, nargs="+", default=[4, 16, 64])
    parser.add_argument("--cutoff", type=int, help="Use this common N; default is max(64,4*d*d).")
    parser.add_argument("--grids", nargs="+", choices=["uniform_scale", "uniform_log", "reciprocal"],
                        default=["uniform_scale"])
    parser.add_argument("--solvers", nargs="+", choices=["canonical", "free", "moebius_log"],
                        default=["canonical", "free"],
                        help="Canonical uses the Lean Gram inverse; moebius_log uses the balanced arithmetic law.")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if any(d < 1 for d in args.dimensions) or (args.cutoff is not None and args.cutoff < 1):
        parser.error("Dimensions and cutoff must be positive.")
    if "moebius_log" in args.solvers:
        if args.grids != ["uniform_scale"] or any(d & (d - 1) for d in args.dimensions):
            parser.error("moebius_log requires uniform_scale and power-of-two dimensions.")
    report = {"status": "exploratory floating-point output; no Lean proof or certified zero bound",
              "numpy_version": np.__version__, "scipy_version": scipy.__version__, "results": []}
    for dimension in args.dimensions:
        cutoff = args.cutoff if args.cutoff is not None else max(64, 4 * dimension * dimension)
        grids = {"uniform_scale": np.arange(1, dimension + 1) / dimension,
                 "uniform_log": np.exp(-np.linspace(0, np.log(dimension), dimension)),
                 "reciprocal": 1 / np.arange(1, dimension + 1)}
        labels = args.grids[:1] if dimension == 1 else args.grids
        for label in labels:
            for solver in args.solvers:
                result = search(grids[label], cutoff, label, solver)
                report["results"].append(result)
                print(json.dumps({k: v for k, v in result.items() if k not in ["scales", "coefficients"]}), flush=True)
                args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
