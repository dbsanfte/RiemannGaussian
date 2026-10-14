#!/usr/bin/env python3
"""Export measured arithmetic/root distinctions and pair certificates."""

from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

BASE = Path(__file__).resolve().parent
OUT = BASE / 'pair-results'


def number(ball):
    return float(re.search(r'[-+]?\d+(?:\.\d+)?(?:e[-+]?\d+)?', ball).group())


def main():
    source = json.loads((OUT / 'pair_search.json').read_text())
    native = json.loads((OUT / 'pair_analytic.json').read_text())
    independent = json.loads((OUT / 'pair_analytic_verification.json').read_text())
    plt.rcParams.update({'font.size': 10, 'axes.titlesize': 12, 'axes.spines.top': False, 'axes.spines.right': False})
    fig, axes = plt.subplots(2, 2, figsize=(12, 8.3), constrained_layout=True)
    blue, orange, green, red = '#2067a6', '#bc6d17', '#297d4f', '#b33c36'

    ax = axes[0, 0]
    beta = np.linspace(0, 1, 201)
    for family, values, color, label in (('input', beta ** 2, blue, 'Transform input root'),
                                         ('output', beta, orange, 'Root of transformed output')):
        ax.plot(beta, values, color=color, label=label)
        rows = [r for r in source['zeta_profiles']['profiles'] if r['family'] == family]
        x, y = [], []
        for row in rows:
            b, baseline = Q(row['beta']), Q(1)
            for j in range(8):
                baseline *= Q(b + j, j + 1)
            x.append(float(b))
            y.append(float(Q(row['coefficients'][256]) - baseline))
        ax.scatter(x, y, s=42, color=color, edgecolor='white', zorder=3)
    ax.set(title='A. Measured root-law difference', xlabel=r'Ordinary input/output root parameter $\beta$',
           ylabel=r'Coefficient at 256 minus $\zeta^\beta$ baseline', xlim=(-.025, 1.025), ylim=(-.025, 1.1))
    ax.legend(frameon=False, loc='upper left')

    ax = axes[0, 1]
    rows = source['inverse_tree_profiles']['3']
    leaves = [r['leaves'] for r in rows]
    mass = [abs(float(Q(r['total_signed_mass']))) for r in rows]
    support = [r['support_count'] for r in rows]
    ax.plot(leaves, mass, 'o-', color=blue, label='Classical Catalan inverse mass')
    ax.plot(leaves, support, 's--', color=orange, label='Distinct integer tree labels')
    for x, y in zip(leaves, mass):
        ax.annotate(str(int(y)), (x, y), xytext=(0, 7), textcoords='offset points', ha='center')
    ax.set(title='B. Known inverse law, distinct arithmetic labels', xlabel='Leaves in ordered inverse tree',
           ylabel='Count / absolute total mass', xticks=leaves, ylim=(0, 48))
    ax.legend(frameon=False, loc='upper left')

    ax = axes[1, 0]
    rows = source['structural_controls']['domain_grammar']
    r = np.array([v['r'] for v in rows])
    edge = np.array([float(Q(v['sufficient_correction_halfplane'])) for v in rows])
    ax.plot(r, edge, 'o-', color=blue, label='Proved sufficient boundary')
    ax.axhline(.5, color='#444444', ls='--', label='Critical line')
    ax.fill_between(r, edge, 1.08, color=blue, alpha=.08)
    ax.scatter([3], [.4], marker='*', s=210, color=green, edgecolor='white', zorder=3)
    ax.annotate('Selected r = 3\ncorrection holomorphic for Re(s) > 0.4', (3, .4), xytext=(2.2, .76),
                arrowprops={'arrowstyle': '->', 'color': green}, color=green)
    ax.text(3.2, .57, '12 ordinary-root controls\non two certified zero disks', fontsize=9, color='#444444')
    ax.set(title='C. Uniform correction domain', xlabel=r'Index rule $ab(a+b)^r$',
           ylabel='Real part of s', xticks=r, ylim=(.2, 1.09))
    ax.legend(frameon=False, loc='lower left')

    ax = axes[1, 1]
    for rows, offset, marker, name in ((native['actual_zeta_ball_checks'], -.07, 'o', 'Native integral'),
                                       (independent['actual_zeta_ball_checks'], .07, 's', 'Independent sum')):
        good, bad = [], []
        for row in rows:
            tail_key = 'proved_full_coefficient_tail_ball' if offset < 0 else 'independent_full_coefficient_tail_ball'
            wrong_key = 'perturbed_difference_lower_ball' if offset < 0 else 'smaller_perturbed_difference_lower_ball'
            allowed = number(row[tail_key])
            good.append(number(row['difference_upper_ball']) / allowed)
            bad.append(number(row[wrong_key]) / allowed)
        positions = np.arange(1, 7) + offset
        ax.scatter(positions, good, marker=marker, color=green, label=name + ': correct')
        ax.scatter(positions, bad, marker=marker, color=red, label=name + ': perturbed')
    ax.axhline(1, color='#555555', ls='--')
    ax.set(title='D. Six fresh zeta comparisons and perturbations', xlabel='Comparison case',
           ylabel='Distance / proved output-tail bound', xticks=range(1, 7), yscale='log')
    ax.legend(frameon=True, facecolor='white', edgecolor='white', framealpha=.95,
              fontsize=9, loc='center', bbox_to_anchor=(.53, .43))
    for ax in axes.flat:
        ax.grid(alpha=.15)
    fig.suptitle('Nonlinear prime-sum arithmetic coupling: verified scope', fontsize=16)
    fig.savefig(OUT / 'pair_overview.png', dpi=170)
    fig.savefig(OUT / 'pair_overview.pdf')
    plt.close(fig)
    print('Saved pair-results/pair_overview.png and .pdf')


if __name__ == '__main__':
    main()
