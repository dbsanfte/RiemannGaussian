#!/usr/bin/env python3
"""Standalone scientific figure for the signed cancellation experiment."""

from collections import Counter
from math import factorial, pi
from pathlib import Path
import json
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


BASE = Path(__file__).resolve().parent
OUT = BASE / 'cancellation-results'


def midpoint(value):
    return float(re.match(r'\[?([-+0-9.eE]+)', value).group(1))


def aq(q, mode):
    if not mode:
        return 1 / factorial(q)
    z = 1 / (2j * pi * mode)
    return -sum(z ** r / factorial(q - r) for r in range(1, q))


def main():
    source = json.loads((OUT / 'cancellation_search.json').read_text())
    analytic = json.loads((OUT / 'cancellation_analytic.json').read_text())
    audit = json.loads((OUT / 'cancellation_analytic_verification.json').read_text())
    blue, green, orange = '#28699a', '#2d8474', '#cf7930'
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                         'axes.spines.top': False, 'axes.spines.right': False})
    fig, axes = plt.subplots(2, 2, figsize=(14, 10.2), layout='constrained')
    fig.suptitle('Signed size-root search: exact cancellation, verified zero sensitivity, known reduction', fontsize=15)

    ax = axes[0, 0]
    orders = np.arange(2, 9)
    trained = Counter(v['q'] for v in source['frequency_grammar']['records'] if v['training_passed'])
    survived = Counter(v['q'] for v in source['frequency_grammar']['survivors'])
    ax.bar(orders - .17, [trained[q] for q in orders], width=.32, color=blue, label='Single-mode training fits')
    ax.bar(orders + .17, [survived[q] for q in orders], width=.32, color=green, label='Fresh axis / unequal-mode survivors')
    for q in orders:
        ax.text(q - .17, trained[q] + .5, str(trained[q]), ha='center', fontsize=9)
        ax.text(q + .17, survived[q] + .5, str(survived[q]), ha='center', fontsize=9, color=green)
    ax.set(title='A. One survivor among 1,904 signed programs', xlabel='Root order q', ylabel='Exact frequency-polynomial fits',
           xticks=orders, ylim=(0, 39))
    ax.legend(frameon=False, fontsize=9, loc='upper right')
    ax.text(.96, .64, 'Only q=2 and equal weights\n(FF, FC, CF, CC) = (1,1,1,1)',
            transform=ax.transAxes, ha='right', fontsize=10)

    ax = axes[0, 1]
    modes = np.arange(1, 17)
    for q, color in ((3, blue), (4, orange), (6, green)):
        values = [4 * aq(q, int(m)).real * aq(q, 1).real for m in modes]
        ax.loglog(modes, values, 'o-', color=color, markersize=3, label=f'q={q}: nonzero')
    ax.set(title='B. Equal weights cease to cancel at higher root order', xlabel='Mixed Fourier mode (m,1)',
           ylabel='Proved Abelian coefficient of the four-lift sum', xticks=(1, 2, 4, 8, 16))
    ax.set_xticklabels(('1', '2', '4', '8', '16'))
    ax.grid(alpha=.15)
    ax.legend(frameon=False, fontsize=9, loc='lower left')
    ax.text(.98, .93, 'q=2: exactly zero at every nonconstant mode\n'
            'q≥3: every nonzero rational constant combination\n'
            'has a natural boundary for independent bases', transform=ax.transAxes, ha='right', va='top', fontsize=9)

    ax = axes[1, 0]
    positions = np.arange(6)
    for dataset, offset, color, label in ((analytic, -.11, blue, 'Source N=4096'),
                                          (audit, .11, green, 'Independent N=6144')):
        points = dataset['actual_zeta_ball_checks']
        full = [midpoint(v['comparisons'][0]['difference_upper_ball']) / midpoint(v['comparisons'][0]['proved_infinite_error_ball']) for v in points]
        normalized = [midpoint(v['comparisons'][1]['difference_upper_ball']) / midpoint(v['comparisons'][1]['proved_infinite_error_ball']) for v in points]
        bad = [min(midpoint(x['perturbed_difference_lower_ball']) / midpoint(x['proved_infinite_error_ball']) for x in v['comparisons']) for v in points]
        ax.semilogy(positions + offset, full, 'o', color=color, label=label)
        ax.semilogy(positions + offset, normalized, 's', color=color, markerfacecolor='white')
        ax.semilogy(positions + offset, bad, 'x', color=color, markersize=7)
    ax.axhline(1, color='#69737b', linestyle='--', linewidth=1.1)
    labels = [f'{v["bases"][0]},{v["bases"][1]}\nβ={v["beta"]}\nσ={v["s"][0]}' for v in analytic['actual_zeta_ball_checks']]
    ax.set(title='C. Fresh zeta points pass two independently bounded formulas', ylabel='Difference / proved infinite error bound',
           xlabel='Base pair, root parameter, real part of the test point', xticks=positions, xticklabels=labels)
    ax.tick_params(axis='x', labelsize=9)
    ax.grid(axis='y', alpha=.15)
    ax.legend(frameon=False, loc='center right', fontsize=9)
    ax.text(.025, .91, '○ Full sum   □ Corrected root\n× Perturbed coefficients (must exceed 1)',
            transform=ax.transAxes, va='top', fontsize=9)

    ax = axes[1, 1]
    zeros = analytic['fresh_actual_critical_line_zero_control']['correction_records']
    independent = audit['fresh_actual_zero_control']['correction_records']
    positions = np.arange(len(zeros))
    native = [midpoint(v['correction_rectangle_real_lower_ball']) for v in zeros]
    uniform = [midpoint(v['global_moment_real_part_lower_ball']) for v in zeros]
    repeated = [midpoint(v['correction_real_lower_after_infinite_tail_ball']) for v in independent]
    ax.bar(positions, uniform, color='#dce8f0', width=.7, label='Universal moment lower bound')
    ax.plot(positions, native, 'o', color=blue, label='Actual disk: native projection functions')
    ax.plot(positions, repeated, 'D', color=green, markerfacecolor='white', markersize=5,
            label='Independent infinite-tail ratio enclosures')
    ax.axhline(.5, color='#69737b', linewidth=1.1, linestyle='--')
    labels = [f'{v["bases"][0]},{v["bases"][1]}\n{v["beta"]}' for v in zeros]
    ax.set(title='D. Correction stays nonzero across a fresh actual zero', ylabel='Certified lower bound for Re(correction)',
           xlabel='Base pair and root parameter β', xticks=positions, xticklabels=labels, ylim=(.46, 1.55))
    ax.tick_params(axis='x', labelsize=8)
    ax.legend(frameon=False, fontsize=8, loc='upper left')
    ax.text(.98, .76, 'ρ ≈ 1/2 + 21.02203963877i; radius 10⁻⁵\n'
            'One simple zero: Taylor + independent Cauchy count\n'
            'β=1/2,1/4: branch jump; β=1: trivial phase\n'
            'Boundary-zero control is compatible with RH',
            transform=ax.transAxes, ha='right', va='top', fontsize=8.5)

    fig.savefig(OUT / 'cancellation.png', dpi=190)
    fig.savefig(OUT / 'cancellation.pdf')
    print('Saved cancellation-results/cancellation.png and cancellation-results/cancellation.pdf')


if __name__ == '__main__':
    main()
