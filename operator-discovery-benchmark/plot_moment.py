#!/usr/bin/env python3
"""Export certified uniform root factors and a coefficientwise-limit trap."""

from fractions import Fraction as Q
from pathlib import Path
import json
import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

BASE=Path(__file__).resolve().parent
DEST=BASE/'moment-results'


def number(s):
    return float(flint.arb(s).mid())


def main():
    data=json.loads((DEST/'moment_analytic.json').read_text())
    independent=json.loads((DEST/'moment_analytic_verification.json').read_text())
    assert data['all_passed'] and independent['all_passed']
    plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False})
    fig,axes=plt.subplots(2,2,figsize=(14.2,10.8))
    fig.suptitle('Higher prime moments: certified limits and ordinary zeta roots',fontsize=19,y=.965)
    ax=axes[0,0]
    orders=np.arange(4,65,2)
    ax.plot(orders,4*6.0**orders,color='#176e81',lw=2.4,label='Gap >= 2: first index $4\\,6^m$')
    ax.plot(orders,2.0**orders,color='#b45532',lw=2.4,label='Unmasked: first index $2^m$')
    ax.axhline(128,color='#7c8890',ls=':',label='Fixed prefix 128')
    ax.set_yscale('log');ax.set_xlabel('Even cancellation order m');ax.set_ylabel('First changed arithmetic index')
    ax.set_title('Both operators tend coefficientwise to identity',loc='left',fontsize=12)
    ax.legend(fontsize=10,loc='upper left');ax.grid(alpha=.18)

    ax=axes[0,1]
    rows=data['uniform_height_bounds']['records']
    m=[r['m'] for r in rows]
    y=[number(r['uniform_relative_zeta_factor_error_bound_ball']) for r in rows]
    half=[number(r['input_half_root_factor_error_bound_ball']) for r in rows]
    ind=[number(r['independent_integer_bound_ball']) for r in independent['uniform_audit']['records']]
    ax.plot(m,y,'o-',color='#176e81',lw=2,label='Factor error: $|e^{R_m}-1|$')
    ax.plot(m,half,'s-',color='#78a442',lw=2,label='Input half-root: $|e^{R_m/4}-1|$')
    ax.plot(m,ind,'--',color='#7c8890',label='Independent integer bound on $|R_m|$')
    ax.set_yscale('log');ax.set_xlabel('Even cancellation order m');ax.set_ylabel('Proved upper bound, every height')
    ax.set_title('Uniform for all Re(s) >= 1/2',loc='left',fontsize=12)
    ax.legend(fontsize=10);ax.grid(alpha=.18)
    ax.annotate('m = 64: factor error < $2.770\\times10^{-9}$',xy=(64,y[-1]),xytext=(19,5e-8),
                arrowprops={'arrowstyle':'->','color':'#176e81'},fontsize=10,color='#176e81')

    ax=axes[1,0]
    trap=data['unmasked_coefficientwise_limit_counterexample']['records']
    ax.plot([r['m'] for r in trap],[number(r['unmasked_infinite_correction_modulus_lower_ball']) for r in trap],
            'o-',color='#b45532',lw=2.2,label='Unmasked: proved modulus LOWER bound')
    ax.plot([r['m'] for r in trap],[number(r['regularized_uniform_bound_ball']) for r in trap],
            's-',color='#176e81',lw=2.2,label='Gap >= 2: proved modulus UPPER bound')
    ax.set_yscale('log');ax.set_xlabel('Even cancellation order m');ax.set_ylabel('Infinite correction modulus bounds')
    ax.set_title(r'Critical-line counterexample: $t=\\pi/\\log(3/2)$'.replace('\\\\','\\'),loc='left',fontsize=12)
    ax.legend(fontsize=9.7);ax.grid(alpha=.18)

    ax=axes[1,1]
    degree=np.arange(2,33,2)
    ax.plot(degree,1/(degree+1),'o-',color='#176e81',label='Paired continuation: Re(s) > 1/(m+1)')
    ax.plot(degree,1/degree,'s-',color='#78a442',label='Ordinary correction: Re(s) > 1/m')
    ax.axhline(.5,color='#b45532',ls='--',label='Critical line: Re(s) = 1/2')
    star=(float(Q(data['sharp_uniform_limit_threshold']['lower']))+float(Q(data['sharp_uniform_limit_threshold']['upper'])))/2
    ax.axhline(star,color='#8a679e',ls=':',lw=2,label=f'Uniform-in-m limit threshold: {star:.6f}')
    ax.set_xlabel('Even cancellation order m');ax.set_ylabel('Real part of s');ax.set_ylim(0,.56)
    ax.set_title('Convergence domains and parameter limit differ',loc='left',fontsize=12)
    ax.legend(fontsize=9.7,loc='upper right');ax.grid(alpha=.18)

    fig.text(.055,.025,'Bounds concern nonzero correction factors. Zeta zero multiplicities and fractional-root branching persist.\n'
             'No off-line zeros are excluded. Two existing zero disks are reused; historical novelty remains unresolved.',
             fontsize=11,color='#46525a')
    fig.subplots_adjust(left=.07,right=.975,bottom=.12,top=.895,hspace=.35,wspace=.28)
    fig.savefig(DEST/'moment_overview.png',dpi=180)
    fig.savefig(DEST/'moment_overview.pdf')
    print('Saved moment overview PNG/PDF',flush=True)


if __name__=='__main__':
    main()
