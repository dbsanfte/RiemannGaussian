#!/usr/bin/env python3
"""Export the proved cancellation, domain edges, and numerical certificates."""

from fractions import Fraction
from pathlib import Path
import json

import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

BASE = Path(__file__).resolve().parent
DEST = BASE / 'visible-results'


def ball_value(s):
    return float(flint.arb(s).mid())


def main():
    exact = json.loads((DEST / 'visible_search.json').read_text())
    native = json.loads((DEST / 'visible_analytic.json').read_text())
    checked = json.loads((DEST / 'visible_analytic_verification.json').read_text())
    assert exact['all_passed'] and native['all_passed'] and checked['all_passed']
    plt.rcParams.update({'font.size': 10, 'axes.spines.top': False, 'axes.spines.right': False,
                         'axes.grid': True, 'grid.alpha': 0.18})
    fig, axes = plt.subplots(2, 2, figsize=(13.2, 9.2), layout='constrained')
    fig.suptitle('Residue-visible arithmetic decoder: cancellation and the remaining zeta barrier\n'
                 'Written universal proofs, exact fibre checks, and independent Arb bounds', fontsize=15)

    ax = axes[0, 0]
    colors = ('#2468a2', '#a15e1d', '#597c35')
    for shift, r, color in zip((-0.23, 0, 0.23), (3, 5, 7), colors):
        profile = next(row for row in exact['local_cancellation_grammar']['profiles'] if row['r'] == r)
        ys = [float(Fraction(v)) for v in profile['coefficients'][:19]]
        xs = np.arange(len(ys)) + shift
        ax.vlines(xs, 0, ys, color=color, linewidth=1.8, alpha=0.75)
        ax.scatter(xs, ys, color=color, s=20, label=f'r = {r}', zorder=3)
    ax.axhline(0, color='#3d3d3d', linewidth=0.7)
    ax.set(xlim=(1.3, 18.7), ylim=(-1.15, 0.9), xlabel='Local degree k', ylabel=r'Correction coefficient $c_{r,k}$',
           title='Same-prime terms cancel every degree below r')
    ax.set_xticks((2, 3, 5, 7, 10, 14, 18))
    ax.legend(loc='lower right', frameon=False)
    ax.text(0.02, 0.94, r'$c_{r,r}=-2H_{r-1}/r,\quad |c_{r,k}|\leq 1$',
            transform=ax.transAxes, va='top', fontsize=11)

    ax = axes[0, 1]
    rs = np.arange(3, 14)
    ax.plot(rs, 1 / rs, 'o-', color='#2468a2', label='Holomorphic remainder edge: 1/r')
    ax.plot(rs, 2 / (rs + 2), 's-', color='#597c35', label='Full encoded endpoint: 2/(r+2)')
    ax.plot(rs, 2 * (rs + 1) / (rs + 2), '^-', color='#ad482d', label='Bounded decoded target: 2(r+1)/(r+2)')
    ax.axhline(0.5, color='#444444', linestyle='--', label='Critical line: 1/2')
    ax.set(xlabel='Encoding parameter r', ylabel='Real-part / coefficient-weight boundary',
           title='Better cancellation leaves the decoder norm loss')
    ax.set_xticks((3, 5, 7, 9, 11, 13))
    ax.legend(loc='center right', frameon=False, fontsize=9)

    ax = axes[1, 0]
    rows = checked['deep_correction_ball_checks']['records']
    xs = np.arange(len(rows))
    distance = [ball_value(row['independent_difference_upper_ball']) for row in rows]
    tail = [ball_value(row['independent_prime_infinite_tail_ball']) for row in rows]
    wrong = [ball_value(row['changed_difference_lower_ball']) for row in rows]
    ax.semilogy(xs, distance, 'o', color='#2468a2', markersize=7, label='Valid difference upper')
    ax.semilogy(xs, tail, 's', color='#666666', markersize=7, label='Infinite-tail bound')
    ax.semilogy(xs, wrong, 'x', color='#ad482d', markersize=9, markeredgewidth=2,
                label='Coefficient error lower')
    for x, lo, hi in zip(xs, distance, wrong):
        ax.vlines(x, lo, hi, color='#999999', linewidth=0.7, alpha=0.7)
    labels = [f"{row['s'][0]}\n{row['s'][1]}i" for row in rows]
    ax.set_xticks(xs, labels)
    ax.set(xlabel='Fresh subcritical correction arguments', ylabel='Bound magnitude (log scale)',
           title='Independent remainder checks below Re(s) = 1/2')
    ax.set_ylim(min(distance) * 0.7, max(wrong) * 12)
    ax.legend(loc='upper center', ncol=3, frameon=False, fontsize=8.3, columnspacing=0.8)
    ax.text(0.02, 0.90, 'Remainder only; full ordinary series converges for Re(s) > 1.',
            transform=ax.transAxes, va='top', fontsize=9)

    ax = axes[1, 1]
    heights = list(dict.fromkeys(row['disk_centre'][1] for row in native['restored_actual_zero_obstruction_controls']['records']))
    for color, marker, height in zip(('#2468a2', '#a15e1d'), ('o', 's'), heights):
        rows = [row for row in native['restored_actual_zero_obstruction_controls']['records'] if row['disk_centre'][1] == height]
        rr = [row['r'] for row in rows]
        anomaly = [ball_value(row['monodromy_difference_upper_ball']) for row in rows]
        major = [ball_value(row['height_independent_monodromy_difference_bound_ball']) for row in rows]
        ax.semilogy(rr, anomaly, marker + '-', color=color, label=f'Zero height {float(height):.5f}: native bound')
        ax.semilogy(rr, major, '--', color=color, alpha=0.7, label=f'Height {float(height):.5f}: uniform Euler bound')
    ax.set_xticks((3, 4, 5, 7))
    ax.set(xlabel='Encoding parameter r', ylabel='Monodromy difference from (LOG zeta)²',
           title='The zero obstruction survives the parameter limit')
    ax.legend(loc='upper right', frameon=False, fontsize=8.7)
    ax.text(0.03, 0.06, 'All eight zero-jump lower bounds are positive.\nNo global RH continuation estimate is proved.',
            transform=ax.transAxes, va='bottom', fontsize=9)

    for suffix in ('png', 'pdf'):
        fig.savefig(DEST / f'visible_overview.{suffix}', dpi=180)
    plt.close(fig)
    print('Saved visible-results/visible_overview.png and .pdf')


if __name__ == '__main__':
    main()
