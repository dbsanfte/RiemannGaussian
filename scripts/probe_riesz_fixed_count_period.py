#!/usr/bin/env python3
"""Optional smooth-model diagnostic for fixed-count signed prime periods.

This uses logarithmic prime-density integrals, not actual prime counts or a
certificate. The Lean theorems independently prove the literal prime bounds.
The moving length uses the exact rational damped cutoff; every factorial
allocation order in unpaidOrders and each Riesz subset sign is retained.
"""
import json
import math
from itertools import combinations

import numpy as np
from scipy.stats import binom


def unpaid_orders(n):
    return np.array([
        k for k in range(n + 2)
        if n + 1 < 8 * k < 7 * (n + 1)
        and 32 * k <= 15 * n + 64
        and not 13 * n // 32 + 1 <= k <= (15 * n + 64) // 32
        and not 4 * n <= 5 * (n + 1 - k)
    ])


def riesz(cut, logs):
    ans = np.zeros_like(cut)
    for k in range(len(logs) + 1):
        for subset in combinations(logs, k):
            ans += (-1) ** k * np.maximum(cut - sum(subset), 0)
    return ans


def row(n, count, cofactor_share=0.52, y=54.0):
    # This is exactly floor(u^(-N)/(N+1)) for u=10001/20000.
    cutoff = pow(20000, n) // (pow(10001, n) * (n + 1))
    length = 2 * math.log(cutoff + 2)
    v = (2 * math.ceil((2 * n * y - math.pi) / (2 * math.pi)) + 1) * math.pi / y
    cofactor = v * (cofactor_share * np.arange(1, count + 1) / sum(range(1, count + 1)))
    nodes, weights = np.polynomial.legendre.leggauss(768)
    total = v + math.pi / y * nodes
    prime_log = total - sum(cofactor)
    reflected = riesz(total - length, cofactor)
    correction = riesz(np.full_like(total, sum(cofactor) - length), cofactor)
    coef = (-1) ** (count + 2) * total / length * (reflected - correction)
    orders = unpaid_orders(n)
    allocated = np.zeros_like(total)
    for logp in [prime_log, *[np.full_like(total, b) for b in cofactor]]:
        in_physical = (2 * math.log(n) < logp) & (logp < length)
        part = binom.cdf(orders[-1], n + 1, 1 - logp / total)
        part -= binom.cdf(orders[0] - 1, n + 1, 1 - logp / total)
        allocated += in_physical * part
    # Divide out the common saddle value to avoid enormous exponentials.
    radial = np.exp(-(total-v)/2 + n*np.log(total/v))
    integrand = (1 - allocated) * coef * radial / prime_log
    phase = -np.cos(math.pi * nodes)  # the selected centre has cos(y*v)=-1
    signed = math.pi/y * np.dot(weights, integrand * phase)
    absolute = math.pi/y * np.dot(weights, abs(integrand * phase))
    return {
        "N": n, "total_prime_count": count+1,
        "cofactor_share": cofactor_share,
        "unsaturated_cutoff_over_v": float((sum(cofactor)-length)/v),
        "retained_cutoff_correction_over_v": float(correction[0]/v),
        "signed_response_over_radial_base": float(signed),
        "absolute_response_over_radial_base": float(absolute),
        "signed_to_absolute_ratio": float(signed/absolute),
        "max_allocated_fraction": float(max(allocated)),
        "cofactor_min_share": float(min(cofactor)/v),
    }


if __name__ == "__main__":
    print(json.dumps({
        "kind": "exploratory smooth model; not a prime theorem or certificate",
        "rows": [row(n, k, share) for share in (0.52, 0.696)
                 for k in (6, 7, 8, 9) for n in (256, 1024, 4096, 16384)]
    }, indent=2))
