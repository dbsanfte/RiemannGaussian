#!/usr/bin/env python3
"""Infer Dirichlet coefficients from actual numerical zeta measurements.

Run with the existing project environment:
  ../.venv/bin/python zeta_data.py --pass discovery
  ../.venv/bin/python zeta_data.py --pass validation

No arithmetic coefficient identities, factorisation routines, prime tables,
Mobius values, or divisor counts are supplied to the reconstruction. The basis
n**(-s), the function transforms, sample region, and finite fitting cutoff are
explicit choices. Coefficients are estimates; cross-cutoff agreement is an
empirical error check, not an enclosure for the omitted infinite tail.
"""

from __future__ import annotations

import argparse
import json
import random
import time
from pathlib import Path

import mpmath as mp
import numpy as np


TRANSFORMS = ["z", "inverse", "square", "argument_double", "product_double",
              "ratio_double", "inverse_ratio_double", "log_derivative",
              "shift_ratio", "shift_product", "log", "square_root"]


def observations(s):
    z = mp.zeta(s)
    z2 = mp.zeta(2 * s)
    shifted = mp.zeta(s - 1)
    derivative = mp.zeta(s, derivative=1)
    return dict(zip(TRANSFORMS, [z, 1 / z, z * z, z2, z * z2, z2 / z,
                               z / z2, -derivative / z, shifted / z,
                               z * shifted, mp.log(z), mp.sqrt(z)]))


def encoded(entry, digits):
    return [mp.nstr(mp.re(entry), digits), mp.nstr(mp.im(entry), digits)]


def reconstruct(config):
    started = time.monotonic()
    mp.mp.dps = config["digits"]
    sigma, fit_size, sample_size = config["sigma"], config["fit_size"], config["sample_size"]
    rng = random.Random(config["seed"])
    heights = [str(round(rng.uniform(-config["height"], config["height"]), 8))
               for _ in range(sample_size)]
    logs = [mp.log(n) for n in range(1, fit_size + 1)]
    design = mp.matrix(sample_size, fit_size)
    measured = mp.matrix(sample_size, len(TRANSFORMS))
    samples = []
    for row, height in enumerate(heights):
        s = mp.mpc(sigma, height)
        values = observations(s)
        for column, log_n in enumerate(logs):
            # Fit b_n = a_n n**(-sigma). Removing the real damping from the
            # matrix avoids unnecessary conditioning from column magnitudes.
            design[row, column] = mp.exp(-mp.j * mp.mpf(height) * log_n)
        for column, name in enumerate(TRANSFORMS):
            measured[row, column] = values[name]
        samples.append({"s": [str(sigma), height],
                        "values": {name: encoded(entry, config["digits"])
                                   for name, entry in values.items()}})
        if (row + 1) % 32 == 0:
            print(f"Observed {row + 1}/{sample_size} zeta sample points", flush=True)
    print("Solving the coefficient reconstruction at arbitrary precision", flush=True)
    gram = design.H * design
    rhs = design.H * measured
    coefficients_scaled = (gram ** -1) * rhs
    coefficients = {
        name: [coefficients_scaled[row, column] * mp.exp(sigma * logs[row])
               for row in range(fit_size)] for column, name in enumerate(TRANSFORMS)}
    retained = config["retained"]
    retained_coefficients = {name: [encoded(entry, config["digits"])
                                   for entry in values[:retained]]
                             for name, values in coefficients.items()}
    fit_residual = design * coefficients_scaled - measured
    approximate_design = np.array([[complex(design[row, column])
                                    for column in range(fit_size)]
                                   for row in range(sample_size)])
    return {"config": config, "elapsed_seconds": time.monotonic() - started,
            "design_condition_number_double_diagnostic": float(np.linalg.cond(approximate_design)),
            "max_sample_absolute_fit_residual": mp.nstr(max(abs(entry) for entry in fit_residual), 12),
            "samples": samples, "coefficients": retained_coefficients,
            "max_retained_imaginary_coefficient": {
                name: mp.nstr(max(abs(mp.im(entry)) for entry in values[:retained]), 12)
                for name, values in coefficients.items()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pass", dest="which", choices=["discovery", "validation"], required=True)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "zeta-results")
    args = parser.parse_args()
    configs = {
        "discovery": {"sigma": 28, "fit_size": 40, "sample_size": 120,
                      "retained": 16, "digits": 120, "height": 1200, "seed": 2026100601},
        "validation": {"sigma": 50, "fit_size": 64, "sample_size": 192,
                       "retained": 32, "digits": 170, "height": 2200, "seed": 2026100602},
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    result = reconstruct(configs[args.which])
    destination = args.output_dir / f"coefficients_{args.which}.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Saved {destination}", flush=True)
    for name, maximum in result["max_retained_imaginary_coefficient"].items():
        print(f"  {name}: imaginary-coefficient diagnostic {maximum}", flush=True)
    print(f"Elapsed: {result['elapsed_seconds']:.1f} seconds", flush=True)


if __name__ == "__main__":
    main()
