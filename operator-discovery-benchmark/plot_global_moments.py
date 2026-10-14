#!/usr/bin/env python3
"""Standalone plots of discovered moments and universal scale-cost controls."""

from fractions import Fraction as Q
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

BASE=Path(__file__).resolve().parent
DEST=BASE/'global-moment-results'


def main():
    data=json.loads((DEST/'global_moment_search.json').read_text());assert data['all_passed']
    plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
    fig,axs=plt.subplots(2,2,figsize=(12,8.5),layout='constrained')
    colors=('#236B8E','#B85C28','#507A3F')
    signed=data['recursive_family_global_moment_calibration']['records']
    sparse=data['lacunary_family_global_moment_calibration']['records']
    ax=axs[0,0]
    ax.plot([r['level'] for r in signed],[float(Q(r['exact_fourth_moment']))/r['span']**2 for r in signed],
            'o-',color=colors[0],label='Signed recursive pair')
    ax.plot([r['level'] for r in sparse],[float(Q(r['exact_fourth_moment']))/r['nonzero_coefficient_count']**2 for r in sparse],
            's-',color=colors[1],label='Positive lacunary product')
    ax.axhline(1.5,color=colors[0],ls=':',label='Signed family: uniform 3/2 bound')
    ax.set(xlabel='Recursion level j',ylabel='Fourth moment / (nonzero coefficient count)²',
           title='A bound for one family need not transfer to another')
    ax.legend(fontsize=8)
    ax=axs[0,1];ax.axis('off')
    ax.text(0,1,'Learned moment transfers',fontsize=14,va='top',weight='bold')
    ax.text(0,.83,'E = ∫ (|P|⁴ + |R|⁴)      C = ∫ |PR|²',fontsize=12)
    ax.text(0,.66,'Opposite signed rows\n(E′, C′) = (2E + 8C, E)\nE + 2C propagates at rate 4',fontsize=12,color=colors[0])
    ax.text(0,.37,'Proportional rows with wider phase separation\n(E′, C′) = (2E + 8C, E + 4C)\nE + 4C propagates at rate 6',fontsize=12,color=colors[1])
    ax.text(0,.09,'48 operator programs → 24 certified transfers\n16 small-input recurrence fits fail on changed inputs',fontsize=10)
    ax=axs[1,0];levels=np.arange(1,33)
    for beta,color in zip((1,2,3),colors):
        ratio=4/2**beta;values=[sum(ratio**k for k in range(int(j))) for j in levels]
        ax.plot(levels,values,label=f'β = {beta}, normalized ratio = {ratio:g}',color=color)
    ax.set_yscale('log');ax.set(xlabel='Number of scale levels',ylabel='Accumulated normalized forcing cost',
                               title='At the critical rate, forcing leaves a logarithmic loss')
    ax.legend(fontsize=8)
    ax=axs[1,1];rows=data['additive_arithmetic_energy_search']['actual_zeta_inverse_family_observations']
    ratio=[r['exact_complete_residue_energy']/(r['row_modulus']*r['maximum_bucket_size']*r['coefficient_squared_norm']) for r in rows]
    ax.plot([r['scale'] for r in rows],ratio,'o-',color=colors[0])
    for row,value in zip(rows,ratio):ax.annotate(f"p={row['row_modulus']}, d={row['index_degree']}",(row['scale'],value),xytext=(4,7),textcoords='offset points',fontsize=8)
    ax.axhline(1,color=colors[1],ls=':',label='Generic universal bound')
    ax.set_xscale('log',base=2);ax.set_ylim(0,1.2)
    ax.set(xlabel='Complete Möbius coefficient scale D',ylabel='Observed energy / generic bound',
           title='Actual zeta-inverse observations; no new cancellation theorem')
    ax.legend(fontsize=8)
    fig.suptitle('Global moment discovery with separate family and scale certificates',fontsize=16)
    fig.savefig(DEST/'global_moment_overview.png',dpi=180)
    fig.savefig(DEST/'global_moment_overview.pdf')
    print('Saved global-moment-results/global_moment_overview.png and .pdf')


if __name__=='__main__':main()
