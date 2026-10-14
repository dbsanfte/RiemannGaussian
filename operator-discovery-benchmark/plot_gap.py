#!/usr/bin/env python3
"""Export exploratory energies beside proved edges and certified root checks."""

from fractions import Fraction
from pathlib import Path
import json

import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

BASE = Path(__file__).resolve().parent
DEST = BASE / 'gap-results'


def ball_value(s):
    return float(flint.arb(s).mid())


def main():
    probe = json.loads((DEST / 'gap_endpoint_probe.json').read_text())
    native = json.loads((DEST / 'gap_analytic.json').read_text())
    checked = json.loads((DEST / 'gap_analytic_verification.json').read_text())
    assert all(data['all_passed'] for data in (probe, native, checked))
    plt.rcParams.update({'font.size': 10, 'axes.spines.top': False,
                         'axes.spines.right': False, 'axes.grid': True,
                         'grid.alpha': 0.18})
    fig, axes = plt.subplots(2, 2, figsize=(13.2, 9.2), layout='constrained')
    fig.suptitle('Gap coupling: a known prime-pair kernel and the arithmetic 1/2 boundary\n'
                 'Exploratory FFT, unconditional endpoint proofs, and independent Arb checks', fontsize=15)

    ax = axes[0, 0]
    for r, color, marker in ((2, '#ad482d', 's'), (3, '#2468a2', 'o')):
        rows = [row for row in probe['endpoint_energy_profiles'] if row['r'] == r and row['sigma'] == 0.5]
        ax.plot([row['input_cutoff'] for row in rows],
                [row['finite_prefix_energy'] for row in rows], marker + '-', color=color,
                label=f'r = {r}: ' + ('divergent endpoint (proved)' if r == 2 else 'convergent endpoint (proved)'))
    ax.set_xscale('log', base=2)
    ax.set_xticks((256, 4096, 65536, 524288), ('256', '4096', '65536', '524288'))
    ax.set(xlabel='Prime-power input cutoff N', ylabel=r'Finite $\Gamma^-_r(1/2)$ prefix',
           title='Finite curves alone cannot establish an infinite limit')
    ax.legend(loc='upper left', frameon=False, fontsize=9)
    ax.text(0.03, 0.32, 'Double precision exploration only.\nEndpoint classification comes from a separate proof.',
            transform=ax.transAxes, fontsize=9)

    ax = axes[0, 1]
    rs = np.arange(1, 8)
    edges = np.maximum(2 / (rs + 2), 0.5)
    ax.plot(rs, edges, '-', color='#777777', linewidth=1.4)
    good = rs != 2
    ax.scatter(rs[good], edges[good], color='#597c35', s=62, zorder=3,
               label='Absolutely convergent at endpoint')
    ax.scatter([2], [0.5], facecolor='white', edgecolor='#ad482d', linewidth=2, s=95,
               zorder=4, label='Divergent at endpoint: r = 2')
    ax.axhline(0.5, color='#444444', linestyle='--', linewidth=1, label='Critical line')
    ax.set(xlim=(0.7, 7.3), ylim=(0.38, 0.79), xlabel='Gap exponent r',
           ylabel='Exact absolute convergence abscissa',
           title=r'Proved edge: $\max(2/(r+2),\,1/2)$')
    ax.set_xticks(rs)
    ax.legend(loc='upper right', frameon=False, fontsize=9)
    ax.text(0.05, 0.07, 'Near prime pairs force the 1/2 boundary for every r.\n'
            'r = 3 is the first continuous critical endpoint.', transform=ax.transAxes, fontsize=9)

    ax = axes[1, 0]
    rows = checked['actual_zeta_ball_checks']
    xs = np.arange(len(rows))
    distance = [ball_value(row['independent_difference_upper_ball']) for row in rows]
    tail = [ball_value(row['changed_integer_Toeplitz_tail_ball']) for row in rows]
    wrong = [ball_value(row['changed_difference_lower_ball']) for row in rows]
    ax.semilogy(xs, distance, 'o', color='#2468a2', markersize=7, label='Valid difference upper')
    ax.semilogy(xs, tail, 's', color='#666666', markersize=7, label='Infinite-tail bound')
    ax.semilogy(xs, wrong, 'x', color='#ad482d', markersize=9, markeredgewidth=2,
                label='Coefficient error lower')
    ax.set_xticks(xs, [f"{row['s'][0]}\n{row['s'][1]}i" for row in rows])
    ax.set(xlabel='Fresh full scalar arguments', ylabel='Bound magnitude (log scale)',
           title='Independent direct sums against native-zeta anchors')
    ax.set_ylim(min(distance) * 0.6, max(wrong) * 25)
    ax.legend(loc='upper center', ncol=3, frameon=False, fontsize=8, columnspacing=0.8)
    ax.text(0.03, 0.90, 'All six also reject the conjugated Hermitian correlation.',
            transform=ax.transAxes, fontsize=9)

    ax = axes[1, 1]
    heights = list(dict.fromkeys(row['disk_centre'][1] for row in native['one_sided_actual_zero_controls']['records']))
    for height, color in zip(heights, ('#2468a2', '#a15e1d')):
        rows = [row for row in native['one_sided_actual_zero_controls']['records'] if row['disk_centre'][1] == height]
        audit = [row for row in checked['one_sided_actual_zero_controls']['records'] if row['disk_centre'][1] == height]
        eps = [float(Fraction(row['epsilon'])) for row in rows]
        ax.plot(eps, [ball_value(row['native_zeta_modulus_over_epsilon_ball']) for row in rows],
                'o-', color=color, label=f'Native zeta, height {float(height):.5f}')
        ax.plot(eps, [ball_value(row['zeta_modulus_over_epsilon_upper_ball']) for row in audit],
                '^--', color=color, alpha=0.65, label=f'Cauchy upper, height {float(height):.5f}')
    ax.set_xscale('log')
    ax.set(xlabel=r'Right-side offset $\epsilon$ from the certified zero center',
           ylabel=r'$|\zeta(\rho_c+\epsilon)|/\epsilon$', ylim=(0.67, 1.45),
           title='Two reused simple-zero disks; right-side controls only')
    ax.legend(loc='upper left', frameon=False, fontsize=8.5)
    ax.text(0.03, 0.04, 'Nonzero correction limit follows from the endpoint proof.\n'
            'No whole crossing-disk holomorphy or RH estimate is proved.',
            transform=ax.transAxes, fontsize=9)

    for suffix in ('png', 'pdf'):
        fig.savefig(DEST / f'gap_overview.{suffix}', dpi=180)
    plt.close(fig)
    print('Saved gap-results/gap_overview.png and .pdf')


if __name__ == '__main__':
    main()
