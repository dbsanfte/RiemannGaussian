#!/usr/bin/env python3
"""Standalone figure separating finite scores and a proved all-scale bound."""

from fractions import Fraction as Q
from pathlib import Path
import json
import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

BASE=Path(__file__).resolve().parent
DEST=BASE/'shift-ratio-results'


def main():
    source=json.loads((DEST/'shift_ratio_search.json').read_text())
    audit=json.loads((DEST/'shift_ratio_verification.json').read_text())
    assert source['all_passed'] and audit['all_passed']
    row=next(r for r in source['profiles'] if r['v']=='1/2')
    B=[float(flint.arb(s)) for s in row['B_coefficients']]
    ps=[n for n in range(2,513) if flint.fmpz(n).is_prime()]
    cs=[n for n in range(2,513) if not flint.fmpz(n).is_prime()]
    moments=[r for r in source['sieve_second_moment_controls']['records'] if r['v']=='1/2']
    plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
    fig,axes=plt.subplots(1,2,figsize=(11.4,4.7),layout='constrained')
    ax=axes[0]
    ax.scatter(cs,[B[n] for n in cs],s=11,color='#BF7025',alpha=.65,label='Composite coefficients')
    ax.scatter(ps,[B[n] for n in ps],s=13,color='#146A83',label='Prime coefficients: exactly 1')
    ax.axhspan(-1/3,1/3,color='#BF7025',alpha=.07)
    ax.axhline(-1/3,color='#BF7025',ls='--',lw=1)
    ax.axhline(1/3,color='#BF7025',ls='--',lw=1,label='Proved composite modulus ≤ 1/3')
    ax.set(xlabel='Arithmetic index n',ylabel=r'$B_{1/2}(n)$',title='Primes remain uniformly separated',
           xlim=(0,520),ylim=(-.42,1.1));ax.grid(alpha=.15);ax.legend(fontsize=9,loc='center right')
    ax=axes[1]
    xs=[r['X'] for r in moments]
    ys=[float(flint.arb(r['M2_ball'])*flint.arb(r['X']).log()/r['X']) for r in moments]
    ax.semilogx(xs,ys,'o-',color='#146A83',label='Independently checked finite moments')
    ax.axhline(6,color='#BF7025',ls='--',label='Proved bound for every integer X ≥ 2')
    ax.fill_between([2,2048],0,6,color='#BF7025',alpha=.05)
    ax.set(xlabel='Doubling interval [X, 2X]',ylabel=r'$M_2([X,2X])\log(X)/X$',
           title='Second moment bounded at every scale',ylim=(0,6.6),xlim=(1.7,2600))
    ax.grid(alpha=.2);ax.legend(fontsize=9,loc='center right')
    fig.suptitle('Unequal-shift zeta decoder at v = 1/2\n'
                 'Prime-gap proof and imported sieve bound; no new distribution or RH estimate',fontsize=12)
    for suffix in ('png','pdf'):fig.savefig(DEST/('shift_ratio_overview.'+suffix),dpi=180)
    print('Wrote shift-ratio-results/shift_ratio_overview.png and .pdf')


if __name__=='__main__':main()
