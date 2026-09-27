#!/usr/bin/env python3
"""Optional diagnostic for joint radial/allocation exponents.

This probes only the envelope proved in ZetaRieszJointRadialFloor.
Floating evaluations are not certificates or signed-prime estimates.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path


U = 10001 / 20000
GAP = 131071 / 262144
ORDER = 13 / 32


def radial_rate(t):
    return math.log(U * t) + 1 - GAP * t


def row(kind, share, tilt, saving, endpoints):
    allocation = math.log(tilt * (1 - share) + share) - ORDER * math.log(tilt)
    return {
        'part': kind,
        'prime_share': share,
        'tilt': tilt,
        'allocation_log_rate': allocation,
        'proved_allocation_saving': saving,
        'radial_endpoints': endpoints,
        'samples': [
            {
                'total_log_over_order': t,
                'radial_log_rate': radial_rate(t),
                'joint_log_rate_with_actual_tilt': radial_rate(t) + allocation,
                'joint_log_rate_with_proved_saving': radial_rate(t) - saving,
            }
            for t in [endpoints[0], 2.0, endpoints[1]]
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    payload = {
        'scope': 'uncertified scalar diagnostics; exact bounds checked separately in Lean',
        'radius_ceiling': U,
        'summable_kernel_gap': GAP,
        'proved_joint_saving': 1 / 400000,
        'rows': [
            row('residual above share', 3 / 5, 41 / 40, 1 / 12500,
                [248 / 125, 252 / 125]),
            row('assigned part below share', 59 / 100, 197 / 200, 1 / 35000,
                [987 / 500, 507 / 250]),
        ],
        'limitations': [
            'No directed rounding; numeric output is not a proof',
            'The central saddle still has positive envelope exponent',
            'The assigned-part estimate does not bound the raw signed contribution',
            'The full core has no independent cofinal floor from this probe',
            'The theorem bounds have an unevaluated finite majorant constant',
        ],
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(payload, indent=2) + '\n')


if __name__ == '__main__':
    main()
