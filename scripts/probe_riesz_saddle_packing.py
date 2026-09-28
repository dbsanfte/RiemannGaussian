#!/usr/bin/env python3
"""Geometry diagnostics only: no prime counts or arithmetic certificate.

Evaluate the exact proposed period count and stable factorial radial ratio.
The length column uses the asymptotic 2*log(u**(-N)/(N+1)); the exact length
is within [2*log(1+1/A),2*log(1+2/A)] above it, A=u**(-N)/(N+1).
"""
import json
import math


def diagnostic(n: int, height: float = 54.0) -> dict:
    u = 10001 / 20000
    root = math.sqrt(n)
    periods = 1 + math.floor(abs(height) * root / (4 * math.pi))
    width = (periods - 1) * 2 * math.pi / abs(height)
    length = -2 * (n * math.log(u) + math.log1p(n))
    ratio = math.exp(-width / 2 + n * math.log1p(width / (2 * n)))
    cutoff_lo = length / (2 * n + root + 1)
    cutoff_hi = length / (2 * n - 1)
    return {
        "N": n,
        "periods": periods,
        "center_span": width,
        "last_over_first_radial": ratio,
        "approx_cutoff_bin": [cutoff_lo, cutoff_hi],
        "approx_bin_fits": 693 / 1000 <= cutoff_lo and cutoff_hi <= 1733 / 2500,
        "net_credit_multiplier": periods * math.sqrt(n + 1) / 16 - 1 / 8,
        "proved_coarse_multiplier": n / 16,
    }


if __name__ == "__main__":
    print(json.dumps({
        "status": "floating geometry diagnostic, not a certified starting order or prime estimate",
        "height": 54,
        "u": "10001/20000",
        "rows": [diagnostic(n) for n in [10000, 1000000, 100000000, 10000000000]],
    }, indent=2))
