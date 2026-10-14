#!/usr/bin/env python3
"""Standalone figures showing finite-fit failure and synthesized bounds."""

from fractions import Fraction as Q
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

BASE = Path(__file__).resolve().parent
DEST = BASE/'estimate-results'


def main():
    data = json.loads((DEST/'estimate_search.json').read_text())
    checked = json.loads((DEST/'estimate_verification.json').read_text())
    assert data['all_passed'] and checked['all_passed']
    fig,axes = plt.subplots(1,2,figsize=(11.5,4.2),layout='constrained')
    for index,label in ((0,r'$W(u)=1-u$'),(3,r'$W(u)=(1-u)^4$')):
        row = data['cancellation_estimate_search']['records'][index]
        x = [o['X'] for o in row['observations']]
        y = [float(Q(o['exact_smoothed_sum'])) for o in row['observations']]
        axes[0].plot(x,y,'o-',label=label,ms=3,lw=1.1)
    plateau = data['cancellation_estimate_search']['finite_survivor_but_mathematically_impossible_control']
    C = float(Q(plateau['constant']))
    axes[0].axhspan(-C,C,color='#bbbbbb',alpha=.25,label='Fitted constant bound for fourth-power kernel')
    axes[0].axvline(1024,color='#555555',ls=':',lw=1)
    axes[0].set_xscale('log')
    axes[0].set_xlabel('Arithmetic scale X (training ends at dotted line)')
    axes[0].set_ylabel(r'$\sum_{n\leq X}\mu(n)W(n/X)$')
    axes[0].set_title('A false global bound survives finite tests')
    axes[0].legend(fontsize=8,loc='lower left')
    axes[0].text(.03,.97,'Known zeta zero rejects the constant-bound claim',transform=axes[0].transAxes,
                 va='top',fontsize=8,bbox={'facecolor':'white','alpha':.8,'edgecolor':'none'})
    improvements = [r for r in data['positive_energy_estimate_search']['records']
                    if r.get('strictly_improves_Jensen_for_this_mixture')]
    for i,row in enumerate(improvements):
        axes[1].bar(i-.17,float(Q(row['existing_Jensen_constant'])),width=.32,color='#a4abb4',
                    label='Previously supplied Jensen bound' if i==0 else None)
        axes[1].bar(i+.17,row['constant_approximation'],width=.32,color='#2977b5',
                    label='Detector-synthesized integral bound' if i==0 else None)
    axes[1].set_xticks(range(len(improvements)),['Mixture 1','Mixture 2'])
    axes[1].set_ylim(0,7)
    axes[1].set_ylabel(r'Constant C in $M_2([X,2X])\leq CX/\log X$')
    axes[1].set_title('Automatically derived all-scale estimates')
    axes[1].legend(fontsize=8,loc='upper right')
    axes[1].text(.03,.03,'Uses the declared classical rough-number theorem',transform=axes[1].transAxes,fontsize=8)
    for suffix in ('png','pdf'):
        fig.savefig(DEST/('estimate_search_overview.'+suffix),dpi=180)
    print('Estimate-search figures saved')


if __name__=='__main__':
    main()
