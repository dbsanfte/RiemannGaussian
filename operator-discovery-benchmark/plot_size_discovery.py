#!/usr/bin/env python3
"""Standalone scientific figure for exact size kernels and zeta controls."""

from fractions import Fraction
from pathlib import Path
import json
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap, BoundaryNorm
from matplotlib.patches import Patch
import numpy as np


BASE=Path(__file__).resolve().parent
OUT=BASE/'size-results'


def height(n,b):
    h=0
    while n>=b:
        n//=b
        h+=1
    return h


def selected(a,d,b,upper=False):
    h=lambda n:height(n,b)+(int(n!=b**height(n,b)) if upper else 0)
    return int(h(a*d)==h(a)+h(d))


def ball_midpoint(value):
    return float(re.match(r'\[?([-+0-9.eE]+)',value).group(1))


def correction_curve(base,exponents,beta,s):
    # Numerical illustration only: the positive-real-part domain is proved
    # by the beta moment integral, not certified by this plotted truncation.
    coefficients=[1.0]
    for k in range(160):
        ratio=np.prod([(beta+e*k+j)/(e*k+j+1) for e in exponents for j in range(e)])
        coefficients.append(coefficients[-1]*ratio)
    return np.polynomial.polynomial.polyval(np.exp(-s*np.log(base)),coefficients)


def main():
    arithmetic=json.loads((OUT/'size_carry_search.json').read_text())
    analytic=json.loads((OUT/'size_analytic_probe.json').read_text())
    colors=['#dce2e7','#2969a1','#ce792f','#308575']
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                         'axes.spines.top':False,'axes.spines.right':False})
    fig,axes=plt.subplots(2,2,figsize=(13.5,10.5),layout='constrained')
    fig.suptitle('Integer size carries: exact products and actual zeta root checks',fontsize=17)

    ax=axes[0,0]
    grid=np.array([[selected(a,d,6)+2*selected(a,d,6,True) for a in range(1,25)] for d in range(1,25)])
    ax.imshow(grid,origin='lower',extent=(.5,24.5,.5,24.5),interpolation='nearest',
              cmap=ListedColormap(colors),norm=BoundaryNorm(np.arange(-.5,4.5),4))
    ax.set(title='A. Which divisor pairs survive?  Base 6',xlabel='Factor a',ylabel='Factor d')
    ax.set_xticks((1,6,12,18,24));ax.set_yticks((1,6,12,18,24))
    ax.legend(handles=[Patch(color=c,label=l) for c,l in zip(colors,('Neither','Floor only','Ceiling only','Both'))],
              loc='upper left',bbox_to_anchor=(0,-.13),ncol=4,fontsize=9,frameon=False)

    ax=axes[0,1]
    indices=[4,6,9,15,35]
    for offset,orientation,color,label in ((-.18,'floor',colors[1],'Floor U(u)'),(.18,'ceil',colors[2],'Ceiling U(u)')):
        profile=next(x for x in arithmetic['zeta_profiles'] if x['base']==2 and x['orientation']==orientation)
        values=[float(Fraction(profile['limit_coefficients'][n])) for n in indices]
        ax.bar(np.arange(len(indices))+offset,values,width=.34,color=color,label=label)
        for i,value in enumerate(values):
            ax.text(i+offset,value+.035,f'{value:g}',ha='center',fontsize=9,color=color)
    ax.axhline(1,color='#a0a9b2',linestyle=':',linewidth=1)
    ax.set(title='B. Actual integer values change the transfer',xlabel='Integer n (base 2)',ylabel='Exact zeta-input coefficient',ylim=(0,1.25))
    ax.set_xticks(np.arange(len(indices)),indices)
    ax.legend(frameon=False,loc='upper right')

    ax=axes[1,0]
    records=analytic['actual_zeta_ball_checks']
    for j,label,color in ((0,'Paired root',colors[3]),(1,'Floor square',colors[1])):
        positions=np.arange(len(records))+(j-.5)*.17
        differences=[ball_midpoint(x['comparisons'][j]['difference_upper_ball']) for x in records]
        bounds=[ball_midpoint(x['comparisons'][j]['proved_infinite_tail_bound_ball']) for x in records]
        ax.vlines(positions,differences,bounds,color=color,alpha=.4,linewidth=1.5)
        ax.scatter(positions,differences,color=color,s=28,label=label+' error upper bound')
        ax.scatter(positions,bounds,color=color,marker='_',s=90)
    ax.set_yscale('log')
    ax.set(title='C. Six fresh actual-zeta points, two formulas',ylabel='Difference and proved infinite error bound',xlabel='Base b and Im(s) (rounded)')
    ax.set_xticks(np.arange(len(records)),[f"b={x['base']}\n{float(x['s'][1]):+.0f}" for x in records])
    ax.grid(axis='y',alpha=.15)
    ax.legend(frameon=False,fontsize=9,loc='lower left')
    ax.text(.98,.97,'Horizontal caps: proved tails\nAll coefficient errors rejected',
            transform=ax.transAxes,ha='right',va='top',fontsize=9)

    ax=axes[1,1]
    heights=np.linspace(0,20,501)
    for base,exponents,color in ((2,(1,),colors[1]),(6,(1,1),colors[3]),(12,(2,1),colors[2])):
        curve=correction_curve(base,exponents,.5,.5+1j*heights)
        ax.plot(heights,curve.real,color=color,linewidth=1.7,label=f'b={base}')
    ax.axhline(.5,color='#555d65',linestyle='--',linewidth=1.2,label='Universal lower bound')
    ax.axvline(14.13472514173469,color='#969ea6',linestyle=':',linewidth=1.2)
    ax.text(14.25,1.79,"First zeta zero\nRe(s)=1/2",fontsize=9,va='top')
    ax.set(title='D. The paired correction stays away from zero',xlabel='Im(s), with Re(s)=1/2 and beta=1/2',ylabel='Re R(b,beta)(s)',ylim=(.4,2.02))
    ax.legend(frameon=False,ncol=2,fontsize=9,loc='upper right')
    ax.text(.02,.13,'Curves illustrate the moment proof.\nIndividual transfer continuation remains open.',
            transform=ax.transAxes,fontsize=9,va='bottom')
    fig.savefig(OUT/'size_discovery.png',dpi=190)
    fig.savefig(OUT/'size_discovery.pdf')
    print('Saved size-results/size_discovery.png and size-results/size_discovery.pdf')


if __name__=='__main__':main()
