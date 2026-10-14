#!/usr/bin/env python3
"""Standalone scientific overview of the full prime-pair decoder audits."""

from fractions import Fraction
from pathlib import Path
import json

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

BASE = Path(__file__).resolve().parent
DEST = BASE / 'prime-pair-results'


def number(ball):
    return float(ball.split()[0].lstrip('['))


def main():
    source = json.loads((DEST / 'prime_pair_search.json').read_text())
    exact = json.loads((DEST / 'prime_pair_verification.json').read_text())
    analytic = json.loads((DEST / 'prime_pair_analytic.json').read_text())
    checked = json.loads((DEST / 'prime_pair_analytic_verification.json').read_text())
    assert all(x['all_passed'] for x in (source, exact, analytic, checked))
    plt.rcParams.update({'font.size': 10, 'axes.titlesize': 12, 'axes.labelsize': 10})
    fig, axes = plt.subplots(2, 2, figsize=(13.2, 9.2), constrained_layout=True)
    fig.suptitle('Prime-pair decoding: two familiar products, different analytic costs', fontsize=17)

    ax = axes[0, 0]
    counts = np.array([int(Fraction(v)) for v in source['zeta_profile']['ordered_prime_sum_counts']])
    indices = np.arange(4, 257)
    for parity, color, label in ((0, '#2166ac', 'Even sums'), (1, '#b35806', 'Odd sums')):
        ns = indices[indices % 2 == parity]
        ax.plot(ns, counts[ns], '.', color=color, markersize=4, label=label)
    ax.set(title='A. Ordered prime-sum counts recovered from the graft', xlabel='Sum n = p + q', ylabel='Ordered representations')
    ax.legend(loc='upper left')
    ax.text(.04, .80, 'Diagonal pairs retained.\nKnown convolution calibration.', transform=ax.transAxes, fontsize=9,
            va='top',
            bbox={'facecolor': 'white', 'edgecolor': 'none', 'alpha': .9})

    ax = axes[0, 1]
    rows = source['hilbert_row_norm_profiles']['records']
    for tau, color in (('2', '#b2182b'), ('5/2', '#b35806'), ('3', '#1b7837')):
        selected = [row for row in rows if row['target_tau'] == tau]
        ax.plot([row['sum_cutoff'] for row in selected],
                [float(Fraction(row['prefix_operator_norm_squared'])) ** .5 for row in selected],
                'o-', color=color, label=f'Target tau = {tau}')
    ax.set_xscale('log', base=2)
    ax.set_yscale('log')
    ax.set(title='B. Additive Hilbert norms, r = 3 and sigma = 1/2', xlabel='Decoded sum cutoff', ylabel='Finite prefix operator norm')
    ax.legend(loc='upper left')
    ax.text(.04, .115, 'Bounded iff tau >= 3, proved for the infinite operator.\nFinite maxima do not certify the infinite exact norm.',
            transform=ax.transAxes, fontsize=9, bbox={'facecolor': 'white', 'edgecolor': 'none', 'alpha': .9})

    ax = axes[1, 0]
    rs = np.arange(2, 9)
    ax.plot(rs, 2 / (rs + 2), 'o-', color='#2166ac', label='Encoded prime-only abscissa')
    ax.plot(rs, 2 * (rs + 1) / (rs + 2), 's-', color='#762a83', label='Bounded product target')
    ax.axhline(2, color='#b35806', label='Bounded additive target')
    ax.axhline(2.5, color='#b2182b', linestyle=':', label='Bounded additive Hilbert target')
    ax.axhline(.5, color='#666666', linestyle='--', label='Critical line')
    ax.set_ylim(.1, 3.9)
    ax.set(title='C. Increasing the encoding power leaves domain loss', xlabel='Encoding power r', ylabel='Real-part / target-weight boundary')
    ax.legend(loc='upper left', fontsize=9)
    ax.text(.04, .23, 'Source at sigma = 2/(r+2), including endpoint.\nTarget curves are generic decoder bounds.', transform=ax.transAxes, fontsize=9)

    ax = axes[1, 1]
    native = analytic['full_prime_product_zero_obstruction_controls']['records']
    independent = checked['full_prime_product_zero_obstruction_controls']['records']
    x = np.arange(2)
    a = [number(row['multiplicative_prime_square_monodromy_jump_lower_ball']) for row in native]
    b = [number(row['independent_prime_square_jump_lower_ball']) for row in independent]
    bars1 = ax.bar(x - .17, a, .32, color='#2166ac', label='Native modulus bounds')
    bars2 = ax.bar(x + .17, b, .32, color='#1b7837', label='Independent Cauchy bounds')
    ax.bar_label(bars1, fmt='%.1f', padding=3)
    ax.bar_label(bars2, fmt='%.1f', padding=3)
    ax.set_xticks(x, [f'{float(row["disk_centre"][1]):.5f}' for row in native])
    ax.set_ylim(0, max(a + b) * 1.3)
    ax.set(title='D. Product decoding restores zero-related branching', xlabel='Imaginary part of certified zeta zero', ylabel='Lower bound on the jump of P(s)^2')
    ax.legend(loc='upper left')
    ax.text(.035, .045, 'Product output only. Additive continuation at these\nzeros is not established by this experiment.',
            transform=ax.transAxes, fontsize=9, bbox={'facecolor': 'white', 'edgecolor': 'none', 'alpha': .9})
    for ax in axes.flat:
        ax.grid(alpha=.14)
        ax.spines[['top', 'right']].set_visible(False)
    for suffix in ('png', 'pdf'):
        fig.savefig(DEST / f'prime_pair_overview.{suffix}', dpi=180)
    print('Saved prime-pair-results/prime_pair_overview.png and .pdf', flush=True)


if __name__ == '__main__':
    main()
