#!/usr/bin/env python3
"""Optional floating audit of the exact owner tail times the radial kernel.

The finite mesh and floating binomial tails are diagnostic, not a floor,
a proof of a uniform rate, or a certified interval calculation. The Lean
module ZetaRieszJointOwnerEnvelope proves the displayed rational saving.
This probe is deliberately outside ordinary builds and CI.
"""

import argparse
import json
import math

import numpy as np
from scipy.special import gammaln
from scipy.stats import binom


def joint_exponent(radius, owner_slope, tilt):
    return (math.log(2 * radius) + (19 / 32) * math.log(tilt)
            - owner_slope * (1 - 1 / tilt) / 2)


def probe_order(n, radius):
    owner = np.linspace(243 / 200, 507 / 400, 41)[:, None]
    total = np.linspace(39 / 20, 203 / 100, 81)[None, :]
    share = 1 - owner / total
    eligible = (owner <= (13 / 20) * total)
    # Literal integer endpoints, without a limiting share indicator.
    lo, hi = n // 5 + 2, 13 * n // 32
    log_tail = np.logaddexp(binom.logcdf(lo - 1, n + 1, share),
                            binom.logsf(hi, n + 1, share))
    t = n * total
    log_response = ((n + 1) * math.log(radius) + log_tail - t / 2
                    + (n + 1) * np.log(t) - gammaln(n + 1))
    log_response = np.where(eligible, log_response, -np.inf)
    i, j = np.unravel_index(np.argmax(log_response), log_response.shape)
    actual = float(log_response[i, j])
    bound = math.log(6 * (n + 1)) - n / 20000
    return {
        "N": n, "unpaidOrders": [lo, hi],
        "meshMaximumSourceNormalizedLogAmplitude": actual,
        "meshOwnerSlope": float(owner[i, 0]),
        "meshTotalSlope": float(total[0, j]),
        "provedLogEnvelope": bound,
        "meshBelowEnvelope": actual <= bound,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", nargs="+", type=int,
                        default=[320, 640, 1536, 4096, 8192, 32768, 131072])
    args = parser.parse_args()
    if any(n < 320 for n in args.orders):
        parser.error("the checked integer tail identity is used only at N>=320")
    radius = 10001 / 20000
    slopes = [1.2, 1.205, 1.21, 1.215, 1.22, 1.225, 1.2675]
    audit = {
        "schemaVersion": 1,
        "scope": "floating scalar-kernel exploration; not a literal prime-sum or floor certificate",
        "radius": radius,
        "chosenOwnerSlope": 243 / 200,
        "chosenTilt": 41 / 40,
        "chosenExponent": joint_exponent(radius, 243 / 200, 41 / 40),
        "provedExponentCeiling": -1 / 20000,
        "optimalTiltDiagnostics": [
            {"ownerSlope": a, "tilt": a / (19 / 16),
             "exponent": joint_exponent(radius, a, a / (19 / 16))}
            for a in slopes
        ],
        "finiteMesh": [probe_order(n, radius) for n in args.orders],
        "wholeFloorProved": False,
        "zeroExclusionProved": False,
    }
    print(json.dumps(audit, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
