#!/usr/bin/env python3
"""Evaluate constants in the proved seven-prime head bound, outside CI.

This is a floating-point scalar diagnostic, not a prime-sum certificate.
The requested radial-scale budgets are not certified supply constants.
"""
import argparse
import json
import math
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1]
                        / 'docs/riesz-seven-head-probe.json')
    args = parser.parse_args()
    moment = lambda a: 6 * math.log(4) / (1 - 2 ** (-a))
    constant = 640 * math.log(4) * math.exp(4) * moment(.5) * moment(.1) ** 5
    rows = []
    for budget in (1, 1 / 128, 1e-6):
        theta = min(1 / 128, (budget / (4 * constant)) ** 2)
        rows.append({'radial_scale_budget': budget, 'theta_diagnostic': theta,
                     'four_B_sqrt_theta': 4 * constant * math.sqrt(theta)})
    result = {
        'scope': 'floating-point diagnostic of proved scalar formulas',
        'prime_sum_certificate': False,
        'exponential_head_constant': constant,
        'rows': rows,
        'limitations': [
            'The supply constant depends on height and has not been numerically evaluated.',
            'No eventual starting order or literal prime population is certified here.',
            'The seven-prime head is paid relatively; separate source-scale decay is not claimed.',
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
