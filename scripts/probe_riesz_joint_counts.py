#!/usr/bin/env python3
"""Optional scalar rate diagnostic; not a prime-sum or Lean certificate."""

import json
import math
from fractions import Fraction
from pathlib import Path


def main():
    radius = Fraction(10001, 20000)
    kernel_tilt = Fraction(131071, 262144)
    euler_slack = Fraction(100001, 100000)
    count_saving = Fraction(7001, 7000)
    final_rate = Fraction(49999, 50000)
    exact_rate = radius / kernel_tilt * euler_slack / count_saving
    rows = [
        {
            "j": j,
            "log_count_saving_per_moment": (j - 6) * math.log(2) / (4096 * (j + 4)),
            "chosen_log_count_saving": math.log(float(count_saving)),
        }
        for j in (64, 128, 256, 1024, 4096)
    ]
    result = {
        "status": "uncertified scalar diagnostic; not a prime-sum estimate",
        "lean_source": "RiemannGaussian/ZetaRieszJointCountFloor.lean",
        "parameters": {
            "radius_ceiling": str(radius),
            "kernel_tilt": str(kernel_tilt),
            "euler_slack": str(euler_slack),
            "count_saving": str(count_saving),
            "certified_rate": str(final_rate),
            "count_reduction_factor": 512,
        },
        "rational_rate_check": {
            "rate": str(exact_rate),
            "upper_bound": str(final_rate),
            "passes_in_python": exact_rate <= final_rate,
            "floating_rate": float(exact_rate),
        },
        "finite_scalar_threshold": 64,
        "arithmetic_threshold": "eventual; not numerically evaluated",
        "rows": rows,
        "asymptotic_scalar_rates": {
            "source_log_growth": math.log(float(2 * radius)),
            "count_log_saving_factor_512": math.log(2) / 4096,
            "count_log_saving_factor_1024": math.log(2) / 8192,
            "note": "1024 fails this envelope, not a mathematical optimality claim",
        },
        "limitations": [
            "Euler mass is absorbed only eventually; j=64 is not a full bound threshold.",
            "Every fixed prime-count class remains eventually.",
            "No signed low-count floor or new zero exclusion follows.",
        ],
    }
    out = Path(__file__).resolve().parents[1] / "docs/riesz-joint-count-probe.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Wrote {out.relative_to(out.parent.parent)}")


if __name__ == "__main__":
    main()
