#!/usr/bin/env python3
"""Standalone plots of compressed arithmetic, component costs and finite leads."""
import argparse
import hashlib
import json
from pathlib import Path
from fractions import Fraction as Q
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def main(d):
    from inverse_prefix_report import summary
    d = Path(d).resolve(); s = summary(d)
    data = json.loads((d / 'final_evaluation.json').read_text())
    cases = json.loads((d / 'final_cases.json').read_text())
    rows = [r for r in data['actual_profile']['rows'] if r['X'] in cases['actual_scales']]
    fig, axes = plt.subplots(1, 3, figsize=(15, 4.5), constrained_layout=True)
    base = sorted([r for r in rows if r['arity'] == 2], key=lambda r: r['X'])
    axes[0].loglog([r['X'] for r in base], [r['energy'] for r in base], 'ko-', label='Actual full energy')
    for slot in [1, 2]:
        axes[0].loglog([r['X'] for r in base], [max(1, r['component_moments'][slot - 1]['energy']) for r in base],
                       'o--', label=f'Individual component {slot}')
    axes[0].set(xlabel='Integer scale X', ylabel='Exact block square energy', title='Cancellation stays necessary')
    axes[0].legend(fontsize=8)
    for k in sorted(set(r['arity'] for r in rows)):
        group = sorted([r for r in rows if r['arity'] == k], key=lambda r: r['X'])
        axes[1].loglog([r['X'] for r in group], [r['cutoff'] for r in group], 'o-', label=f'{k} inverse factors')
    axes[1].set(xlabel='Integer scale X', ylabel='Required actual inverse prefix', title='Exact input compression')
    axes[1].legend(fontsize=8)
    for i, p in enumerate(data['potential_results']):
        points = [r for r in p['observations'] if r['level'] == 12 and not r['missing']]
        axes[2].plot([r['X'] for r in points], [float(Q(r['margin'])) for r in points], 'o-', label=f'Potential lead {i}')
    axes[2].axhline(0, color='black', linewidth=.8)
    axes[2].set(xlabel='Integer scale X', ylabel='Fitted bound minus signed innovation', title='Finite tests at q=12')
    axes[2].set_xscale('log', base=2); axes[2].legend(fontsize=8)
    fig.suptitle('Verified identities; actual all-scale signed inequality remains unproved', fontsize=11)
    for suffix in ['png', 'pdf']:
        destination = d / f'inverse_prefix.{suffix}'
        if destination.exists(): raise FileExistsError(destination)
        fig.savefig(destination, dpi=170)
    plt.close(fig)
    result = {name: hashlib.sha256((d / name).read_bytes()).hexdigest() for name in ['inverse_prefix.png', 'inverse_prefix.pdf']}
    (d / 'plot_verification.json').write_text(json.dumps({'source_verification_sha256': s['verification_sha256'], 'files_sha256': result}, indent=2) + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--run-dir', required=True, type=Path)
    main(p.parse_args().run_dir)
