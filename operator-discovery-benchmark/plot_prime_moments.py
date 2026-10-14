#!/usr/bin/env python3
"""Standalone scientific figure; finite observations and universal gap distinguished."""

from fractions import Fraction as Q
from pathlib import Path

import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

from exact_arithmetic import program_value
from prime_moment_transfer import dyadic_enclosure
from global_moment_grammar import separated_support_count_bounds

BASE=Path(__file__).resolve().parent
DEST=BASE/'prime-moment-results'


def main():
    flint.ctx.prec=320;N=4096;delta=Q(5,12)
    scores=program_value({'kind':'fractional_prime_program','family':'fractional_prime_decoder',
                          'alpha':'1/2','input':'f'},{'f':[0]+[1]*N})
    primes=[n for n in range(2,N+1) if flint.fmpz(n).is_prime()]
    prime_set=set(primes);orders=list(range(2,22,2));observed=[];envelope=[];ranges=[]
    for q in orders:
        composite=sum((scores[n]**q for n in range(2,N+1) if n not in prime_set),flint.arb(0))
        observed.append(float(composite));envelope.append(float(delta**q*(N-1)))
        moment=sum((scores[n]**q for n in range(2,N+1)),flint.arb(0));lo,hi=dyadic_enclosure(moment)
        bounds=separated_support_count_bounds(lo,hi,N-1,delta,q//2)
        lower=bounds['count_lower'];upper=bounds['count_upper']
        ranges.append((-((-lower.numerator)//lower.denominator),upper.numerator//upper.denominator))
    plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
    fig,axes=plt.subplots(1,2,figsize=(11.2,4.8),layout='constrained')
    ax=axes[0];ax.semilogy(orders,observed,'o-',color='#176B87',label='Measured composite contribution')
    ax.semilogy(orders,envelope,'--',color='#BD6D20',label=r'Uniform gap bound $\delta^q W$')
    ax.set(xlabel='Coefficient moment order q',ylabel='Composite contribution to the moment',
           title='Higher moments suppress composite scores',xticks=orders[::2]);ax.grid(alpha=.2);ax.legend(fontsize=9)
    ax=axes[1]
    selected=6;xs=orders[:selected];low=[v[0] for v in ranges[:selected]];high=[v[1] for v in ranges[:selected]]
    mids=[(a+b)/2 for a,b in zip(low,high)]
    ax.errorbar(xs,mids,yerr=([m-a for m,a in zip(mids,low)],[b-m for m,b in zip(mids,high)]),
                fmt='o',capsize=6,color='#176B87',label='Certified integer count interval')
    ax.axhline(len(primes),color='#BD6D20',linestyle='--',label=f'Independent count: {len(primes)}')
    ax.annotate(f'Unique count at q=10: {len(primes)}',xy=(10,len(primes)),xytext=(6,330),
                arrowprops={'arrowstyle':'->','color':'#444'},fontsize=10)
    ax.set(xlabel='Coefficient moment order q',ylabel='Prime count',title='An aggregate moment isolates the count',
           xticks=xs,ylim=(0,800));ax.grid(alpha=.2);ax.legend(fontsize=9,loc='upper right')
    fig.suptitle('Zeta-derived prime moments on 2 ≤ n ≤ 4096\n'
                 'Finite energy values; proved score gap δ = 5/12; no new distribution estimate',fontsize=12)
    DEST.mkdir(exist_ok=True)
    for suffix in ('png','pdf'):fig.savefig(DEST/('prime_moment_overview.'+suffix),dpi=180)
    print('Wrote prime-moment-results/prime_moment_overview.png and .pdf')


if __name__=='__main__':main()
