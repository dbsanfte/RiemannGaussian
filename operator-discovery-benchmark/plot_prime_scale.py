#!/usr/bin/env python3
"""Export finite prime observations and proved scale-filter limitations."""

from fractions import Fraction as Q
from pathlib import Path
import json
import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

BASE=Path(__file__).resolve().parent
DEST=BASE/'prime-scale-results'


def number(value):return float(flint.arb(value).mid())


def main():
    source=json.loads((DEST/'prime_scale_search.json').read_text())
    data=json.loads((DEST/'prime_scale_analytic.json').read_text())
    audit=json.loads((DEST/'prime_scale_analytic_verification.json').read_text())
    assert source['all_passed'] and data['all_passed'] and audit['all_passed']
    plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False})
    fig,axes=plt.subplots(2,2,figsize=(14.2,10.8))
    fig.suptitle('Priority: actual prime information across scales',fontsize=19,y=.97)

    ax=axes[0,0]
    rows=source['actual_prime_scale_observations']['records']
    for label,color,marker in (('complete dyadic window','#176e81','o'),
                               ('complete distant short window','#b45532','s')):
        selected=[r for r in rows if r['sample_type']==label]
        x=[r['lower_exclusive'] for r in selected]
        y=[r['prime_count']/(r['upper_inclusive']-r['lower_exclusive']) for r in selected]
        ax.plot(x,y,marker,color=color,ms=6,label='Dyadic windows (X, 2X]' if marker=='o' else 'Short windows (X, X + 4096]')
    ax.set_xscale('log');ax.set_yscale('log')
    ax.set_xlabel('Window start X');ax.set_ylabel('Exact count / window length')
    ax.set_title('Finite observations through a window near $10^{12}$',loc='left',fontsize=12)
    ax.legend(fontsize=9.5);ax.grid(alpha=.18,which='both')
    ax.text(.97,.47,'These points are not\na uniform prime bound.',transform=ax.transAxes,
            ha='right',fontsize=10,color='#46525a')

    ax=axes[0,1]
    grammar=source['floor_filter_grammar'];alias=grammar['first_coarse_grid_alias']['coefficients']
    points=np.arange(421)/420
    def value(c,k):return sum(v*(a*k//420) for a,v in enumerate(c,1))
    ax.step(points,[value(alias,k) for k in range(421)],where='post',color='#b45532',lw=1.8,
            label='Quarter-grid false positive')
    ax.step(points,[value([-2,1],k) for k in range(421)],where='post',color='#176e81',lw=2,
            label='Central-binomial filter: proved nonnegative')
    ax.scatter(np.arange(4)/4,[value(alias,k*105) for k in range(4)],color='#b45532',s=45,zorder=3,
               label='Four training samples')
    ax.axhline(0,color='#7c8890',lw=.9);ax.set_xlabel('Fractional scale t');ax.set_ylabel('Integer floor-filter weight')
    ax.set_title('All jump intervals must be certified',loc='left',fontsize=12)
    ax.legend(fontsize=9.2,loc='upper right');ax.grid(alpha=.18)
    ax.text(.03,.08,'78,125 programs; 341 coarse survivors;\n67 exact periodic positivity certificates.',
            transform=ax.transAxes,fontsize=10,color='#46525a')

    ax=axes[1,0]
    rows=data['scale_decoder_norm_controls']['finite_saturating_lower_bounds']
    for sig,color in (('1/2','#b45532'),('1','#8a679e'),('5/4','#78a442'),('2','#176e81')):
        selected=[r for r in rows if r['sigma']==sig]
        ax.plot([r['X'] for r in selected],[number(r['finite_generic_decoder_norm_lower_ball']) for r in selected],
                'o-',lw=2,color=color,label=f'sigma = {sig}')
    ax.set_xscale('log',base=4);ax.set_yscale('log')
    ax.set_xlabel('Scale cutoff N');ax.set_ylabel('Saturating generic norm lower bound')
    ax.set_title('Möbius scale decoder: bounded iff sigma > 1',loc='left',fontsize=12)
    ax.legend(fontsize=10);ax.grid(alpha=.18,which='both')
    ax.text(.97,.43,'A new estimate on structured\nprime inputs remains possible.',
            transform=ax.transAxes,ha='right',fontsize=10,color='#46525a')

    ax=axes[1,1]
    control=data['positive_trace_negative_prime_contrast_control']
    values=[number(control['positive_raw_trace_ball']),number(control['decoded_prime_contrast_ball'])]
    ax.bar([0,1],values,color=['#176e81','#b45532'],width=.5)
    ax.axhline(0,color='#7c8890',lw=.9)
    ax.set_xticks([0,1],['Floor trace: log 252','Decoded contrast: log(7/10)'])
    ax.set_ylabel('Exact all-scale observable at X = 5');ax.set_ylim(-1,7.8)
    ax.set_title('Positive smoothing loses prime fluctuation signs',loc='left',fontsize=12)
    ax.text(.97,.89,'Mellin trace: zeta-zero poles cancel\nMellin decoder: those poles return',
            transform=ax.transAxes,ha='right',fontsize=10,color='#46525a')
    ax.text(.97,.49,'Decoded statistic includes prime powers:\npsi(10) - 2 psi(5).\nActual primes require the separate extraction.',
            transform=ax.transAxes,ha='right',fontsize=9.5,color='#46525a')
    ax.grid(axis='y',alpha=.18)

    fig.text(.055,.025,'Six exact and six analytic gates pass. Complete distant windows have 312, 228, 170, 140 primes. '
             'Their counts are finite observations.\n'
             'Universal identities, positivity and the generic norm barrier are proved separately. '
             'No new prime-distribution bound, historical novelty or RH proof is established.',fontsize=10,color='#46525a')
    fig.subplots_adjust(left=.065,right=.975,bottom=.12,top=.9,wspace=.27,hspace=.32)
    fig.savefig(DEST/'prime_scale_overview.png',dpi=180)
    fig.savefig(DEST/'prime_scale_overview.pdf')
    print('Saved prime-scale overview PNG/PDF',flush=True)


if __name__=='__main__':main()
