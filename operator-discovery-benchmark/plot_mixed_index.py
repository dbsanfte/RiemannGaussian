#!/usr/bin/env python3
"""Export a scientific figure from the completed mixed-index certificates."""

from fractions import Fraction
from pathlib import Path
import json
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


BASE = Path(__file__).resolve().parent
OUT = BASE / 'mixed-index-results'


def midpoint(value):
    return float(re.match(r'\[?([-+0-9.eE]+)', value).group(1))


def main():
    source = json.loads((OUT / 'mixed_index_search.json').read_text())
    analytic = json.loads((OUT / 'mixed_index_analytic.json').read_text())
    audit = json.loads((OUT / 'mixed_index_analytic_verification.json').read_text())
    assert source['all_passed'] and analytic['all_passed'] and audit['all_passed']
    blue, green, orange, red = '#28699a', '#2d8474', '#cf7930', '#ae474b'
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                         'axes.spines.top': False, 'axes.spines.right': False})
    fig, axes = plt.subplots(2, 2, figsize=(14, 10), layout='constrained')
    fig.suptitle('Prime-binary partition search: proved domain, ordinary-root interpretation rejected', fontsize=15)

    ax = axes[0, 0]
    profiles = {item['beta']: item for item in source['zeta_coefficient_profiles']}
    indices = np.arange(2, 129)
    full = [float(Fraction(x)) for x in profiles['1']['coefficients'][2:129]]
    half = [float(Fraction(x)) for x in profiles['1/2']['coefficients'][2:129]]
    ax.vlines(indices, 0, full, colors=blue, alpha=.18, lw=1)
    ax.scatter(indices, full, s=13, color=blue, label=r'$\beta=1$')
    ax.scatter(indices, half, s=11, color=orange, label=r'$\beta=1/2$')
    ax.set(title='A. Exact coefficients depend on prime-power bit blocks',
           xlabel=r'Arithmetic index $n$ (partition the bits of $n-1$)',
           ylabel=r'$F_\beta(n)$', xlim=(0, 131), ylim=(-.025, 1.13))
    ax.text(.52, .91, r'$F_1(7)=1,\quad F_1(11)=3/4$' + '\nBoth prime; same bit count of n−1',
            transform=ax.transAxes, fontsize=10)
    ax.legend(frameon=False, loc='upper right', bbox_to_anchor=(1, .78))
    ax.grid(axis='y', alpha=.15)

    ax = axes[0, 1]
    grammar = source['parity_recurrence_grammar']
    counts = [grammar['models_scored'], grammar['training_fit_count'], len(grammar['survivors'])]
    ax.bar(range(3), counts, color=[blue, orange, green], width=.55)
    for i, count in enumerate(counts):
        ax.text(i, count * 1.15, str(count), ha='center', fontsize=11)
    ax.set_yscale('log')
    ax.set(title='B. Fresh tests isolate one recurrence, then a proof',
           ylabel='Number of programs', xticks=range(3),
           xticklabels=['Scored', 'Training fits', 'Fresh survivors'], ylim=(.65, 1200))
    ax.text(.98, .95, r'Fresh even $n\leq1024$; $\beta=1/2,1/4,2/3$',
            transform=ax.transAxes, ha='right')
    ax.text(.98, .56,
            r'$F_\beta(n)=\sum_{r=1}^{v_2(n)}\frac{\beta}{r}\frac{(k-r)!}{k!}$'
            + '\n' + r'$\times F_\beta(n-2^r+1)$'
            + '\n' + r'$k=\operatorname{popcount}(n-1),\quad n$ even',
            transform=ax.transAxes, fontsize=11, ha='right')
    ax.grid(axis='y', alpha=.15)

    ax = axes[1, 0]
    samples = np.arange(1, 7)
    rows = audit['actual_zeta_ball_checks']
    regular = [midpoint(v['regularizer_difference_upper_ball']) / midpoint(v['independent_Bell_row_tail_ball']) for v in rows]
    reverse = [midpoint(v['reverse_difference_upper_ball']) / midpoint(v['reverse_Rankin_tail_ball']) for v in rows]
    bad_regular = [midpoint(v['regularizer_perturbation_lower_ball']) / midpoint(v['independent_Bell_row_tail_ball']) for v in rows]
    bad_reverse = [midpoint(v['reverse_perturbation_lower_ball']) / midpoint(v['reverse_Rankin_tail_ball']) for v in rows]
    ax.semilogy(samples, regular, 'o-', color=blue, markersize=4, label='N: native-input coefficient bridge')
    ax.semilogy(samples, reverse, 's-', color=green, markersize=4, label='V: direct scalar ζ formula')
    ax.semilogy(samples, bad_regular, 'o--', color=orange, markersize=4, label='N: perturbed coefficient')
    ax.semilogy(samples, bad_reverse, 's--', color=red, markersize=4, label='V: perturbed coefficient')
    ax.axhline(1, color='#555555', lw=1, label='Certificate threshold')
    ax.set(title='C. Independent actual-ζ comparisons and rejection controls',
           xlabel='Fresh complex comparison case',
           ylabel='Distance bound / proved infinite tail', xticks=samples)
    ax.legend(frameon=False, fontsize=9, loc='upper left')
    ax.grid(alpha=.15)

    ax = axes[1, 1]
    original = analytic['existing_actual_zero_new_operator_controls']['records']
    independent = audit['existing_actual_zero_new_operator_controls']['records']
    positions = np.arange(2)
    a = [midpoint(v['reverse_transfer_modulus_lower_ball']) for v in original]
    b = [midpoint(v['reverse_modulus_lower_after_infinite_tail_ball']) for v in independent]
    ax.bar(positions - .17, a, width=.32, color=blue, label='48 shifted native ζ values')
    ax.bar(positions + .17, b, width=.32, color=green, label='One ζ value + arithmetic correction')
    for i in positions:
        ax.text(i, max(a[i], b[i]) + .018, f'≥ {min(a[i], b[i]):.3f}', ha='center')
    ax.set(title='D. Reverse calibration V erases actual ζ zeros',
           xlabel='Height of certified simple ζ zero (disk centre)',
           ylabel=r'Certified lower bound for $|V(s)|$ on full disk',
           xticks=positions, xticklabels=['14.134725…', '21.022040…'], ylim=(0, .91))
    ax.text(.05, .91, 'Nβ is holomorphic across both disks.\nIts B roots differ from ordinary Dirichlet roots.',
            transform=ax.transAxes, fontsize=10)
    ax.legend(frameon=False, fontsize=9, loc='upper left', bbox_to_anchor=(0, .76))
    ax.grid(axis='y', alpha=.15)

    fig.supxlabel('Written universal proofs + independent exact/Arb checks. Historical originality unresolved; no new RH estimate.', fontsize=10)
    for suffix in ('png', 'pdf'):
        filename = OUT / f'mixed_index_overview.{suffix}'
        fig.savefig(filename, dpi=190)
        print(filename)
    plt.close(fig)


if __name__ == '__main__':
    main()
