#!/usr/bin/env python3
"""Optional smooth-period diagnostic for the signed floor mechanism.

Uses the full radial factorial amplitude relative to its central value.
No primes are replaced in a certified arithmetic sum by this probe.
It is not a prime-count estimate, packet bound, or RH certificate. Outside CI.
"""

import json
import math

from scipy.integrate import quad


def row(order, radial_ratio, height=54):
    centre = radial_ratio * order
    half = math.pi / height

    def amplitude(offset):
        return math.exp(-offset / 2 + (order + 1) * math.log1p(offset / centre))

    def curvature(offset):
        total = centre + offset
        return amplitude(offset) * (
            ((order + 1) / total - 0.5) ** 2 - (order + 1) / total**2
        )

    direct = quad(
        lambda offset: amplitude(offset) * math.cos(height * offset),
        -half, half, epsabs=1e-14,
    )[0]
    retained = -quad(
        lambda offset: curvature(offset) * (1 + math.cos(height * offset)) / height**2,
        -half, half, epsabs=1e-14,
    )[0]
    # The true amplitude maximum includes its saddle if that lies in the period.
    candidates = [-half, half]
    saddle_offset = 2 * (order + 1) - centre
    if -half <= saddle_offset <= half:
        candidates.append(saddle_offset)
    max_amplitude = max(amplitude(x) for x in candidates)
    adverse_bound = (
        2 * half * (order + 1) / (centre - half) ** 2
        * max_amplitude / height**2
    )
    assert abs(direct - retained) < 1e-12
    assert direct <= adverse_bound + 1e-12
    return {
        "order": order,
        "radial_ratio": radial_ratio,
        "height": height,
        "signed_period_per_central_amplitude": direct,
        "curvature_identity_value": retained,
        "adverse_upper_bound": adverse_bound,
        "convex_drift_is_favorable": retained < 0,
        "identity_discrepancy": abs(direct - retained),
    }


def main():
    print(json.dumps({
        "scope": __doc__.strip(),
        "limitations": [
            "smooth factorial-period diagnostic only",
            "height 54 is not asserted to be a zeta zero",
            "no source-normalized or whole-carrier floor is inferred",
        ],
        "rows": [row(n, r) for n in (640, 4096, 65536, 1000000)
                 for r in (1.95, 2.0, 2.03)],
    }, indent=2))


if __name__ == "__main__":
    main()
