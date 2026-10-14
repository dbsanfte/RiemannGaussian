#!/usr/bin/env python3
"""Export the decoder's exact norm loss and certified zero obstructions."""

from fractions import Fraction as Q
from pathlib import Path
import json
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

BASE = Path(__file__).resolve().parent
OUT = BASE / 'decode-results'


def number(value):
    return float(re.search(r'[-+]?\d+(?:\.\d+)?(?:e[-+]?\d+)?', value).group())


def main():
    source = json.loads((OUT / 'decode_search.json').read_text())
    native = json.loads((OUT / 'decode_analytic.json').read_text())
    independent = json.loads((OUT / 'decode_analytic_verification.json').read_text())
    plt.rcParams.update({'font.size': 10, 'axes.titlesize': 12, 'axes.spines.top': False, 'axes.spines.right': False})
    blue, green, orange, red = '#2067a6', '#297d4f', '#bc6d17', '#b33c36'
    fig, axes = plt.subplots(2, 2, figsize=(12, 8.3), constrained_layout=True)

    ax = axes[0, 0]
    for tau, color in ((Q(1, 2), red), (Q(3, 2), orange), (Q(2), green)):
        rows = [r for r in source['norm_loss_profiles']['records'] if Q(r['target_sigma']) == tau]
        prime = [r['prime_pair'][1] for r in rows]
        ratio = [float(Q(r['norm_ratio_squared'])) ** .5 for r in rows]
        ax.plot(prime, ratio, 'o-', color=color, label=f'Target weight tau = {tau}')
    ax.set(title='A. Exact basis norm ratios; source sigma = 1/2', xlabel='Second prime q in input pair (2, q)',
           ylabel='Decoded / encoded weighted norm', xscale='log', yscale='log')
    ax.legend(frameon=False, loc='upper left', fontsize=9)
    ax.text(.04, .06, 'Bounded iff tau >= 4 sigma\nfor r = 3; proved for all inputs', transform=ax.transAxes, fontsize=9)

    ax = axes[0, 1]
    r = np.arange(2, 9)
    encoded, bounded = 2 / (r + 2), 2 * (r + 1) / (r + 2)
    ax.plot(r, encoded, 'o-', color=blue, label='Encoded correction: sigma above curve')
    ax.plot(r, bounded, 's-', color=red, label='Bounded decoding: tau above curve')
    ax.axhline(.5, color='#555555', ls='--', label='Critical line')
    ax.axhline(1, color='#777777', ls=':', label='Decoded coefficients: exact abscissa 1')
    ax.scatter([3, 3], [.4, 1.6], marker='*', color=orange, s=130, zorder=3)
    ax.set(title='B. Increasing index power does not remove norm loss', xlabel='Grafting power r',
           ylabel='Real-part weight boundary', xticks=r, ylim=(.05, 2.25))
    ax.legend(frameon=True, edgecolor='white', facecolor='white', fontsize=8, loc='upper left')

    ax = axes[1, 0]
    x = np.array([0, 1])
    source_jumps = [number(r['decoded_log_monodromy_jump_lower_ball']) for r in native['restored_actual_zero_obstruction_controls']['records']]
    independent_jumps = [number(r['independent_decoded_monodromy_jump_lower_ball']) for r in independent['restored_actual_zero_obstruction_controls']['records']]
    ax.bar(x - .16, source_jumps, .3, color=blue, label='Native basepoint bound')
    ax.bar(x + .16, independent_jumps, .3, color=green, label='Independent Cauchy bound')
    for xx, yy in list(zip(x - .16, source_jumps)) + list(zip(x + .16, independent_jumps)):
        ax.text(xx, yy + 2, f'{yy:.1f}', ha='center', fontsize=9)
    ax.set(title='C. Decoding restores a logarithmic zero obstruction', xlabel='Imaginary part of certified zeta zero',
           ylabel=r'Proved lower bound on $|\Delta T_3|$', xticks=x, xticklabels=['14.13473', '21.02204'], ylim=(0, 190))
    ax.legend(frameon=False, loc='upper left', fontsize=9)
    ax.text(.04, .05, 'Encoded Gamma_3 is holomorphic across both disks.\nThese jumps belong to the decoded logarithmic series.',
            transform=ax.transAxes, fontsize=8, bbox={'facecolor': 'white', 'edgecolor': 'none', 'alpha': .9})

    ax = axes[1, 1]
    for data, offset, marker in ((native['actual_zeta_ball_checks'], -.06, 'o'),
                                (independent['actual_zeta_ball_checks'], .06, 's')):
        good, wrong = [], []
        for row in data:
            tail = number(row['proved_decoded_tail_ball'] if offset < 0 else row['independent_decoded_tail_ball'])
            good.append(number(row['difference_upper_ball']) / tail)
            wrong.append(number(row['perturbed_difference_lower_ball'] if offset < 0 else row['smaller_perturbed_difference_lower_ball']) / tail)
        position = np.arange(1, 7) + offset
        ax.scatter(position, good, marker=marker, color=green, label='Correct coefficients' if offset < 0 else None)
        ax.scatter(position, wrong, marker=marker, color=red, label='Perturbed coefficients' if offset < 0 else None)
    ax.axhline(1, color='#555555', ls='--')
    ax.set(title='D. Six fresh decoded-series zeta comparisons', xlabel='Case; circles native, squares independent',
           ylabel='Distance / proved coefficient tail', yscale='log', xticks=range(1, 7))
    ax.legend(frameon=True, facecolor='white', edgecolor='white', loc='upper left', fontsize=9)
    for ax in axes.flat:
        ax.grid(alpha=.15)
    fig.suptitle('Prime-sum decoder: arithmetic recovery has an analytic cost', fontsize=16)
    fig.savefig(OUT / 'decode_overview.png', dpi=170)
    fig.savefig(OUT / 'decode_overview.pdf')
    plt.close(fig)
    print('Saved decode-results/decode_overview.png and .pdf')


if __name__ == '__main__':
    main()
