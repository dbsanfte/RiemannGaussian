#!/usr/bin/env python3
"""Standalone scientific figure for the verified two-base size experiment."""

from fractions import Fraction as Q
from math import comb, factorial, log, pi
from pathlib import Path
import json
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


BASE = Path(__file__).resolve().parent
OUT = BASE / 'joint-results'


def midpoint(value):
    return float(re.match(r'\[?([-+0-9.eE]+)', value).group(1))


def main():
    source = json.loads((OUT / 'joint_size_search.json').read_text())
    analytic = json.loads((OUT / 'joint_size_analytic.json').read_text())
    audit = json.loads((OUT / 'joint_size_analytic_verification.json').read_text())
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                         'axes.spines.top': False, 'axes.spines.right': False})
    blue, green, orange = '#28699a', '#2d8474', '#cf7930'
    fig, axes = plt.subplots(2, 2, figsize=(14, 10.5), layout='constrained')
    fig.suptitle('Joint size products: verified arithmetic, a barrier before the critical strip', fontsize=16)

    ax = axes[0, 0]
    tb, tc = 2 * pi / log(2), 2 * pi / log(3)
    for limit, y, color in ((8, 2, green), (32, 1, blue)):
        frequencies = sorted(m * tb + n * tc for m in range(-limit, limit + 1)
                             for n in range(-limit, limit + 1) if abs(m * tb + n * tc) <= 40)
        ax.scatter(frequencies, np.full(len(frequencies), y), marker='|', s=70, linewidths=.8, color=color)
    dependent = [k * pi / log(2) for k in range(-9, 10) if abs(k * pi / log(2)) <= 40]
    ax.scatter(dependent, np.zeros(len(dependent)), marker='|', s=100, color=orange)
    ax.set(title='A. Independent bases produce a dense frequency group', xlabel='t on the boundary s = 1 + it',
           yticks=(0, 1, 2), yticklabels=('2,4: discrete group', '2,3: |m,n| ≤ 32', '2,3: |m,n| ≤ 8'),
           xlim=(-41, 41), ylim=(-.55, 2.8))
    ax.text(.5, .96, 'Finite frequency windows illustrate the universal proof',
            transform=ax.transAxes, ha='center', va='top', fontsize=9)
    ax.text(.5, .06, 'Every finite q ≥ 2: nonzero coefficients at a dense set\n'
            '⇒ no continuation across Re(s)=1 for independent bases',
            transform=ax.transAxes, ha='center', va='bottom', fontsize=9)

    ax = axes[0, 1]
    q = np.arange(2, 17)
    independent = [1 / factorial(int(v)) ** 2 for v in q]
    dependent = [comb(2 + int(v) - 1, int(v)) / (2 ** int(v) * factorial(int(v))) for v in q]
    ax.semilogy(q, independent, '-', color=blue, label='Independent: 1/(q!)²')
    ax.semilogy(q, dependent, '-', color=orange, label='c=b²: (q+1)/(2^q q!)')
    geometry = [v for v in source['correlated_angle_volume_grammar']['observations'] if v['power_relation_k'] == 2]
    for prefix, color in (('independent', blue), ('dependent', orange)):
        lower = np.array([float(Q(v[f'{prefix}_lower'])) for v in geometry])
        upper = np.array([float(Q(v[f'{prefix}_upper'])) for v in geometry])
        centre = (lower + upper) / 2
        ax.errorbar([v['q'] for v in geometry], centre, yerr=[centre - lower, upper - centre],
                    fmt='o', capsize=3, markersize=4, color=color)
    ax.set(title='B. Dependence changes the real-pole coefficient', xlabel='Finite root order q',
           ylabel='Abelian coefficient / simplex volume', xticks=(2, 4, 8, 12, 16))
    ax.grid(axis='y', alpha=.15)
    ax.legend(frameon=False, fontsize=9)
    ax.text(.06, .25, 'q=2: 1/4 versus 3/8\n405 volume programs → one correlated law',
            transform=ax.transAxes, ha='left', fontsize=9)

    ax = axes[1, 0]
    records = analytic['actual_root_torus_moment_controls']['independent_records']
    powers = (32, 64, 128)
    maxima = [max(midpoint(y['angular_Fourier_modulus_upper_ball'])
                  for v in records if v['root_order'] == 4 and v['epsilon_power_of_two'] == -k
                  for y in v['moments']) for k in powers]
    # The worst modes share the base-2 coordinate; coincident three-pair
    # curves would obscure that equality. Plot their common upper envelope.
    ax.semilogy(powers, maxima, 'o-', color=blue, label='Worst bound across 3 independent pairs')
    controls = analytic['actual_root_torus_moment_controls']['dependent_records']
    dependent_mass = [midpoint(v['moment_modulus_lower_ball']) for v in controls if v['bases'] == [2, 4]]
    ax.semilogy((32, 64, 128), dependent_mass, 's--', color='#727b83', label='2,4: mode (1,−2) stays at mass ≈1')
    ax.set(title='C. Actual zeta-root moments distinguish the bases', xlabel='−log2(epsilon), Re(s)=1+epsilon',
           ylabel='Maximum bound over 24 nonconstant modes (q=4)', xticks=(32, 64, 128))
    ax.grid(axis='y', alpha=.15)
    ax.legend(frameon=False, fontsize=8.5, loc='lower left')
    ax.text(.97, .76, '18 independent cases + 6 dependence controls\n'
            'Independent audit checks 48 modes per case', transform=ax.transAxes, ha='right', fontsize=9)

    ax = axes[1, 1]
    positions = np.arange(6)
    for data, shift, color, label in ((analytic, -.08, blue, 'Fejer / arithmetic N=512'),
                                      (audit, .08, green, 'Ordinary Fourier / arithmetic N=768')):
        points = data['actual_zeta_ball_checks']
        ratios = [midpoint(v['difference_upper_ball']) / midpoint(v['proved_infinite_error_ball']) for v in points]
        bad = [midpoint(v['perturbed_difference_lower_ball']) / midpoint(v['proved_infinite_error_ball']) for v in points]
        ax.semilogy(positions + shift, ratios, 'o', color=color, label=label)
        ax.semilogy(positions + shift, bad, 'x', color=color, markersize=7)
    ax.axhline(1, color='#67717a', linewidth=1.1, linestyle='--')
    labels = [f'{v["bases"][0]},{v["bases"][1]}\n{v["s"][0]} {float(v["s"][1]):+.2f}i'
              for v in analytic['actual_zeta_ball_checks']]
    ax.set(title='D. Fresh zeta comparisons pass proved infinite tails', ylabel='Difference / permitted error bound',
           xticks=positions, xticklabels=labels, xlabel='Bases and complex test point')
    ax.tick_params(axis='x', labelsize=8)
    ax.grid(axis='y', alpha=.15)
    ax.legend(frameon=False, fontsize=9, loc='center right')
    ax.text(.02, .95, '○ Correct coefficients: below 1\n× Perturbed coefficient: above 1',
            transform=ax.transAxes, va='top', fontsize=9)

    fig.savefig(OUT / 'joint_size.png', dpi=190)
    fig.savefig(OUT / 'joint_size.pdf')
    print('Saved joint-results/joint_size.png and joint-results/joint_size.pdf')


if __name__ == '__main__':
    main()
