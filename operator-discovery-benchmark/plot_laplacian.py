#!/usr/bin/env python3
"""Export arithmetic support, distinct convergence domains, and root bounds."""

from fractions import Fraction
from math import isqrt
from pathlib import Path
import json

import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

BASE=Path(__file__).resolve().parent
DEST=BASE/'laplacian-results'


def value(s):
    return float(flint.arb(s).mid())


def main():
    exact=json.loads((DEST/'laplacian_search.json').read_text())
    native=json.loads((DEST/'laplacian_analytic.json').read_text())
    checked=json.loads((DEST/'laplacian_analytic_verification.json').read_text())
    assert all(data['all_passed'] for data in (exact,native,checked))
    plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,
                         'axes.grid':True,'grid.alpha':0.18})
    fig,axes=plt.subplots(2,2,figsize=(13.2,9.2),layout='constrained')
    fig.suptitle('Prime gap-Laplacian: arithmetic shear and cancellation domains\n'
                 'Known kernel calibration, universal proofs, and independent Arb checks',fontsize=15)

    ax=axes[0,0]
    coefs=next(row['coefficients'] for row in exact['zeta_profiles'] if row['r']==4)
    for square,color,label in ((True,'#2468a2','Squares: positive diagonal terms'),
                               (False,'#ad482d','Nonsquares: negative cross terms')):
        ns=[n for n in range(2,1001) if Fraction(coefs[n]) and (isqrt(n)**2==n)==square]
        ys=[float(Fraction(coefs[n])) for n in ns]
        ax.vlines(ns,0,ys,color=color,linewidth=1.5,alpha=0.7)
        ax.scatter(ns,ys,color=color,s=35,label=label,zorder=3)
    ax.axhline(0,color='#444444',linewidth=0.8)
    ax.set_xscale('log')
    ax.set(xlabel='Encoded arithmetic index N',ylabel='Zeta-log correction coefficient',
           title='Complete prime fibres separate the coefficient signs',ylim=(-2.6,2.9))
    ax.legend(loc='upper left',frameon=False,fontsize=9)
    ax.text(0.30,0.38,'Prime coefficients stay fixed.\nExact inverse: parameter -t.',
            transform=ax.transAxes,fontsize=9)

    ax=axes[0,1]
    rs=np.arange(4,13,2)
    ax.plot(rs,2/(rs+2),'o-',color='#2468a2',label='Paired correction edge: 2/(r+2)')
    ax.plot(rs,np.full(len(rs),0.5),'s-',color='#ad482d',label='Ordinary correction coefficient edge: 1/2')
    ax.axhline(1,color='#666666',linestyle='--',label='Full transformed ordinary series: 1')
    ax.set_xticks(rs)
    ax.set(xlabel='Even gap exponent r',ylabel='Absolute convergence / continuation boundary',
           title='Cancellation extends a grouped sum beyond its coefficients',ylim=(0.03,1.35))
    ax.legend(loc='upper right',frameon=False,fontsize=8.7)
    ax.text(0.03,0.45,'The paired and correction-coefficient endpoints converge.\n'
            'The full series has a nonremovable zeta pole at one.',transform=ax.transAxes,fontsize=9)

    ax=axes[1,0]
    rows=checked['actual_zeta_ball_checks']
    xs=np.arange(len(rows))
    good=[value(row['difference_upper_ball']) for row in rows]
    tail=[value(row['integer_absolute_majorant_tail_ball']) for row in rows]
    bad=[value(row['changed_difference_lower_ball']) for row in rows]
    ax.semilogy(xs,good,'o',color='#2468a2',markersize=7,label='Valid difference upper')
    ax.semilogy(xs,tail,'s',color='#666666',markersize=7,label='Signed EXP tail bound')
    ax.semilogy(xs,bad,'x',color='#ad482d',markersize=9,markeredgewidth=2,label='Coefficient error lower')
    ax.set_xticks(xs,[f"{row['s'][0]}\n{row['s'][1]}i" for row in rows])
    ax.set(xlabel='Fresh full transformed-zeta arguments',ylabel='Bound magnitude (log scale)',
           title='Independent scalar checks reject smaller coefficient errors')
    ax.set_ylim(min(good)*0.6,max(bad)*70)
    ax.legend(loc='upper center',ncol=3,frameon=False,fontsize=8,columnspacing=0.8)
    ax.text(0.02,0.90,'All six also reject substituting positive Hermitian energy.',
            transform=ax.transAxes,fontsize=9)

    ax=axes[1,1]
    betas=(1,0.5,0.25)
    for index,color in ((0,'#2468a2'),(1,'#a15e1d')):
        row=native['whole_actual_zero_correction_controls']['records'][index]
        old=checked['whole_actual_zero_correction_controls']['records'][index]
        lower=[value(v['modulus_lower_ball']) for v in row['input_root_factor_bounds']]
        M=flint.arb(old['whole_disk_Gamma_modulus_upper_ball'])
        independent=[float((-flint.arb(beta)**2*M).exp().mid()) for beta in betas]
        label=f"Height {float(row['disk_centre'][1]):.5f}"
        ax.plot(range(3),lower,'o-',color=color,label=label+': source bound')
        ax.plot(range(3),independent,'^--',color=color,alpha=0.7,label=label+': independent bound')
    ax.set_xticks(range(3),('1','1/2','1/4'))
    ax.set(xlabel='Ordinary input-root exponent beta',ylabel=r'Whole-disk lower bound for $|e^{\beta^2 H_4}|$',
           title='Nonzero correction factors on two complete zero disks',ylim=(0,1.22))
    ax.legend(loc='upper left',frameon=False,fontsize=8.5)
    ax.text(0.03,0.02,'Both certified simple-zero disks are reused.\n'
            'Ordinary root monodromy survives; no RH estimate is proved.',
            transform=ax.transAxes,fontsize=9)

    for suffix in ('png','pdf'):
        fig.savefig(DEST/f'laplacian_overview.{suffix}',dpi=180)
    plt.close(fig)
    print('Saved laplacian-results/laplacian_overview.png and .pdf')


if __name__=='__main__':
    main()
