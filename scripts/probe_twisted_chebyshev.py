#!/usr/bin/env python3
"""Optional fixed-height scale detector; not a certificate or a CI task.

Separates literal integer von Mangoldt data from a positive continuous
coherent control. Checks components before variance/correlation analysis.
Large-order statements below concern the CONTROL, not actual primes.
"""

import argparse
import cmath
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.special import logsumexp


def mangoldt(limit):
    prime = np.ones(limit + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if prime[p]:
            prime[p * p :: p] = False
    values = np.zeros(limit + 1)
    for p in np.flatnonzero(prime):
        p = int(p)
        power = p
        while power <= limit:
            values[power] = math.log(p)
            if power > limit // p:
                break
            power *= p
    return values


def pack(z):
    return {"re": float(z.real), "im": float(z.imag), "abs": float(abs(z))}


def main_integral(a, b, y):
    c = 1 - 1j * y
    return (cmath.exp(c * math.log(b)) - cmath.exp(c * math.log(a))) / c


def literal_blocks(values, y, beta):
    logs = np.log(np.maximum(np.arange(len(values)), 1))
    prefix = np.cumsum(values * np.exp(-1j * y * logs))
    rows = []
    for T in np.arange(math.log(1024), math.log(len(values) - 1) - 1, .25):
        lower, upper = math.exp(T), math.exp(T + 1)
        raw = prefix[math.floor(upper)] - prefix[math.floor(lower)]
        raw -= main_integral(lower, upper, y)
        rows.append({"T": float(T), "lower": math.floor(lower),
                     "upper": math.floor(upper), "raw": pack(raw),
                     "power_normalized": pack(raw * math.exp(-beta * T))})
    ys = np.array([complex(r["power_normalized"]["re"],
                           r["power_normalized"]["im"]) for r in rows])
    return {"height": y, "rows": rows,
            "sample_mean": pack(ys.mean()),
            "sample_variance": float(np.mean(np.abs(ys - ys.mean()) ** 2)),
            "warning": "Finite low-height calibration; no all-scale or high-order inference."}


def lower_gamma_chernoff(shape, endpoint):
    """Log of a valid elementary Gamma lower-tail upper bound."""
    if endpoint >= shape:
        return 0.
    return shape - endpoint + shape * math.log(endpoint / shape)


def coherent_control(u, y):
    beta = 1.5 - u
    # d psi_model / dx = 1 - 2*x**(beta-1)*cos(y*log(x))
    # only above exp(B); below that use density one.
    B = math.ceil(1 / (Fraction(str(u)) - Fraction(1, 2)))
    constant = -math.expm1(beta) / beta
    conjugate = -(cmath.exp(beta - 2j * y) - 1) / (beta - 2j * y)
    # Uniform sample over an EXACT full log-period, retaining both pieces.
    Ts = B + 10 + np.arange(8192) / 8192 * math.pi / abs(y)
    oscillation = conjugate * np.exp(-2j * y * Ts)
    blocks = constant + oscillation
    mean = blocks.mean()
    variance = np.mean(np.abs(blocks - mean) ** 2)
    orders = []
    for k in [256, 640, 4096, 8192, 16384, 32768, 65536, 131072]:
        shape = k + 1
        # Complete continuous factorial moment:
        # (u/(1/2+iy))**shape - 1 - (u/(u+2iy))**shape.
        # Cutting the perturbation below B costs <= 2*P(Gamma(shape,u)<=B).
        logs = [shape * math.log(u / abs(.5 + 1j * y)),
                shape * math.log(u / abs(u + 2j * y)),
                math.log(2) + lower_gamma_chernoff(shape, u * B)]
        orders.append({"order": k, "control_error_bound_log": float(logsumexp(logs)),
                       "limit": {"re": -1., "im": 0.}})
    rates = []
    for frequency in [.0001, .001, .01, .1, 1., 2 * abs(y)]:
        exponent = .5 * math.log1p((frequency / u) ** 2)
        rates.append({"off_frequency": frequency,
                      "factorial_decay_exponent": exponent,
                      "orders_for_e_minus_10": math.ceil(10 / exponent)})
    return {"is_literal_prime_data": False, "radius": u, "beta": beta,
            "height": y, "positive_density_start_log": B,
            "minimum_density_relative_factor": 1 - 2 * math.exp(-(u - .5) * B),
            "matched_normalized_block": pack(constant),
            "conjugate_normalized_block_amplitude": pack(conjugate),
            "period_mean": pack(mean), "period_variance": float(variance),
            "exact_period_variance": abs(conjugate) ** 2,
            "mean_error": abs(mean - constant),
            "variance_error": abs(variance - abs(conjugate) ** 2),
            "coherent_factorial_orders": orders, "frequency_filter_rates": rates,
            "verdict": "Positive block variance and exact phase coupling coexist with source -1."}


def sensitivity(u):
    epsilon = u - .5
    rows = []
    for T in [10_000, 20_000, 100_000, 1_000_000]:
        rows.append({"log_scale": T, "coherent_relative_amplitude": 2 * math.exp(-epsilon * T),
                     "ripple_log": math.log(2) - epsilon * T,
                     "sqrt_log_envelope_log": -math.sqrt(T),
                     "log_power_10_envelope_log": -10 * math.log(T)})
    return {"epsilon": epsilon, "rows": rows,
            "warning": "Fixed sample comparisons are not eventual envelope proofs; use the Lean audit."}


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=1 << 22)
    parser.add_argument("--height", type=float, nargs="+", default=[60., 100.])
    parser.add_argument("--radius", type=float, default=10001 / 20000)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.limit < 8192 or not (.5 < args.radius < 1) or any(y == 0 for y in args.height):
        parser.error("need limit>=8192, 1/2<radius<1 and nonzero heights")
    values = mangoldt(args.limit)
    # Independent exact small integer prime-power regression.
    assert np.allclose(values[1:17], [0, math.log(2), math.log(3), math.log(2),
        math.log(5), 0, math.log(7), math.log(2), math.log(3), 0, math.log(11),
        0, math.log(13), 0, 0, math.log(2)])
    controls = [coherent_control(args.radius, y) for y in args.height]
    assert all(c["minimum_density_relative_factor"] > 0 for c in controls)
    assert all(c["variance_error"] < 1e-9 and c["mean_error"] < 1e-8 for c in controls)
    result = {"certificate": False, "literal_limit": args.limit,
              "literal_vonMangoldt": [literal_blocks(values, y, 1.5 - args.radius) for y in args.height],
              "positive_continuous_controls": controls,
              "sensitivity": sensitivity(args.radius),
              "conclusions": [
                  "Raw/block variance is not a non-coherence criterion.",
                  "The matched source is a subleading density ripple, not bulk phase alignment.",
                  "Off-frequency scale variation can vanish under the factorial transform.",
                  "Literal finite samples do not prove or refute an all-height arithmetic estimate."]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"literal_limit": args.limit, "controls": [
        {"height": c["height"], "variance": c["period_variance"],
         "mean": c["period_mean"], "high_order_error_log": c["coherent_factorial_orders"][-1]["control_error_bound_log"]}
        for c in controls]}, indent=2))


if __name__ == "__main__":
    run()
