#!/usr/bin/env python3
"""Scientific exports for the ordinary-root-sensitive difference experiment."""

from pathlib import Path
import json
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


BASE = Path(__file__).resolve().parent
OUT = BASE / 'difference-results'


def midpoint(x):
    return float(re.match(r'\[?([-+0-9.eE]+)', x).group(1))


def main():
    search = json.loads((OUT / 'difference_search.json').read_text())
    analytic = json.loads((OUT / 'difference_analytic.json').read_text())
    audit = json.loads((OUT / 'difference_analytic_verification.json').read_text())
    assert search['all_passed'] and analytic['all_passed'] and audit['all_passed']
    blue, green, orange, red = '#28699a', '#2d8474', '#cf7930', '#ae474b'
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                         'axes.spines.top': False, 'axes.spines.right': False})
    fig, axes = plt.subplots(2, 2, figsize=(14, 10), layout='constrained')
    fig.suptitle('Quadratic index differences: proved cancellation and ordinary zeta roots retained', fontsize=15)

    ax = axes[0, 0]
    degrees = np.linspace(2, 16, 160)
    for m, color in ((1, blue), (2, green), (3, orange)):
        ax.plot(degrees, m * (degrees - 1), color=color, label=f'm={m}: universal law')
        points = {2 ** row['iterations']: row['first_nonzero_Taylor_degree'] for row in search['exact_kernel_profiles']
                  if row['difference_order'] == m}
        ax.scatter(list(points), list(points.values()), color=color, s=30, zorder=3)
    ax.set_xscale('log', base=2)
    ax.set(title='A. Learned and proved order r=m(2ᵏ−1)',
           xlabel='Image degree d=2ᵏ', ylabel='First generic nonzero Taylor degree r',
           xticks=(2, 4, 8, 16), xlim=(1.8, 17), ylim=(0, 49))
    ax.set_xticklabels(('2', '4', '8', '16'))
    ax.text(.04, .87, 'Dots: exact fresh Taylor profiles\nLines: universal theorem', transform=ax.transAxes)
    ax.legend(frameon=False, fontsize=9, loc='lower right')
    ax.grid(alpha=.15)

    ax = axes[0, 1]
    iterations = np.arange(1, 5)
    for m, color in ((1, blue), (2, green), (3, orange), (6, red)):
        boundaries = -m + (m + 1) / 2.0 ** iterations
        ax.plot(iterations, boundaries, 'o-', color=color, markersize=4, label=f'm={m}')
    ax.axhline(.5, color='#777777', ls=':', lw=1)
    ax.text(3.95, .60, 'Critical line Re(s)=1/2', ha='right', fontsize=9)
    ax.scatter([2, 1], [-1.25, -2.5], facecolors='none', edgecolors='black', s=90, zorder=4)
    ax.annotate('Selected quartic: −5/4', xy=(2, -1.25), xytext=(2.15, -.85), fontsize=9,
                arrowprops={'arrowstyle': '-', 'lw': .8})
    ax.annotate('Trivial-zero control: −5/2', xy=(1, -2.5), xytext=(2.10, -3.4), fontsize=9,
                arrowprops={'arrowstyle': '-', 'lw': .8})
    ax.set(title='B. Zero-free correction above each proved boundary',
           xlabel='Number of index iterations k', ylabel='η=−m+(m+1)/2ᵏ',
           xticks=iterations, ylim=(-6, .9))
    ax.legend(frameon=False, ncol=2, fontsize=9, loc='lower left')
    ax.grid(alpha=.15)

    ax = axes[1, 0]
    samples = np.arange(1, 7)
    source_rows, independent_rows = analytic['actual_zeta_ball_checks'], audit['actual_zeta_ball_checks']
    source_error = [midpoint(v['difference_upper_ball']) / midpoint(v['proved_full_coefficient_tail_ball']) for v in source_rows]
    independent_error = [midpoint(v['difference_upper_ball']) / midpoint(v['independent_coefficient_tail_ball']) for v in independent_rows]
    source_bad = [midpoint(v['perturbed_difference_lower_ball']) / midpoint(v['proved_full_coefficient_tail_ball']) for v in source_rows]
    independent_bad = [midpoint(v['smaller_perturbation_lower_ball']) / midpoint(v['independent_coefficient_tail_ball']) for v in independent_rows]
    ax.semilogy(samples, source_error, 'o-', color=blue, markersize=4, label='Native shifted-log-ζ reference')
    ax.semilogy(samples, independent_error, 's-', color=green, markersize=4, label='Independent grouped reference')
    ax.semilogy(samples, source_bad, 'o--', color=orange, markersize=4, label='Source coefficient perturbation')
    ax.semilogy(samples, independent_bad, 's--', color=red, markersize=4, label='Smaller independent perturbation')
    ax.axhline(1, color='#555555', lw=1, label='Certificate threshold')
    ax.set(title='C. Six fresh scalar ζ comparisons pass; perturbations fail',
           xlabel='Fresh complex comparison case', ylabel='Distance bound / proved coefficient tail',
           xticks=samples, ylim=(.0009, 1e6))
    ax.legend(frameon=False, fontsize=9, loc='upper left')
    ax.grid(alpha=.15)

    ax = axes[1, 1]
    a = analytic['existing_actual_zero_new_operator_controls']['records'] + [analytic['actual_trivial_zero_control']]
    b = audit['existing_actual_zero_new_operator_controls']['records'] + [audit['actual_trivial_zero_control']]
    first = [midpoint(next(x for x in row['records'] if x['beta'] == '1/2')['root_monodromy_jump_lower_ball']) for row in a]
    second = [midpoint(next(x for x in row['records'] if x['beta'] == '1/2')['independent_monodromy_lower_ball']) for row in b]
    positions = np.arange(3)
    ax.bar(positions - .17, first, width=.32, color=blue, label='Source disk certificate')
    ax.bar(positions + .17, second, width=.32, color=green, label='Independent disk certificate')
    ax.set(title='D. Ordinary-root phase retained at actual zeros (β=1/2)',
           xlabel='Certified ζ-zero disk',
           ylabel=r'Lower bound for $|(e^{2\pi i\beta}-1)C_\beta|$',
           xticks=positions, xticklabels=['1/2+14.134725…i', '1/2+21.022040…i', '−2 (trivial)'], ylim=(0, 2.6))
    ax.text(.03, .92, 'β=1/4 also passes; β=1 has the correct zero phase.\nAt −2 the correction equals exactly 1.', transform=ax.transAxes, fontsize=9)
    ax.legend(frameon=False, fontsize=9, loc='upper left', bbox_to_anchor=(0, .78))
    ax.grid(axis='y', alpha=.15)

    fig.supxlabel('Negative correction domains are grouped analytic continuations. Historical originality unresolved; no new RH estimate.', fontsize=10)
    for suffix in ('png', 'pdf'):
        filename = OUT / f'difference_overview.{suffix}'
        fig.savefig(filename, dpi=190)
        print(filename)
    plt.close(fig)


if __name__ == '__main__':
    main()
