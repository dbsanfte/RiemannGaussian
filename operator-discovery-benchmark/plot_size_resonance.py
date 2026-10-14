#!/usr/bin/env python3
"""Scientific figure for verified size-lift singularity controls."""

from fractions import Fraction
from math import factorial,pi
from pathlib import Path
import json
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


BASE=Path(__file__).resolve().parent
OUT=BASE/'size-results'


def midpoint(value):
    return float(re.match(r'\[?([-+0-9.eE]+)',value).group(1))


def main():
    source=json.loads((OUT/'size_resonance_probe.json').read_text())
    audit=json.loads((OUT/'size_resonance_verification.json').read_text())
    colors={2:'#28699a',6:'#2d8474',12:'#cf7930'}
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                         'axes.spines.top':False,'axes.spines.right':False})
    fig,axes=plt.subplots(2,2,figsize=(13.3,9.7),layout='constrained')
    fig.suptitle('Size products: a verified obstruction to individual RH holomorphy',fontsize=16)

    ax=axes[0,0]
    q=np.arange(1,17)
    ax.semilogy(q,[1/factorial(int(x)) for x in q],color=colors[2],linewidth=1.6,label='Proved 1/q! coefficient')
    grammar=source['volume_grammar']
    for key,color,label in (('training_geometry','#959fa8','Training boxes'),('fresh_geometry',colors[6],'Fresh boxes')):
        records=grammar[key]
        lower=np.array([float(Fraction(x['lower'])) for x in records])
        upper=np.array([float(Fraction(x['upper'])) for x in records])
        centre=(lower+upper)/2
        ax.errorbar([x['q'] for x in records],centre,yerr=[centre-lower,upper-centre],fmt='o',markersize=4,
                    capsize=3,color=color,label=label)
    ax.set(title='A. The real-pole coefficient shrinks with root order',xlabel='Finite root order q',ylabel='Simplex volume / Abelian coefficient',xticks=(1,2,4,8,12,16))
    ax.grid(axis='y',alpha=.15)
    ax.legend(frameon=False,fontsize=9)
    ax.text(.96,.66,'600 programs scored\n4 aliases for one law',transform=ax.transAxes,ha='right',fontsize=9)

    ax=axes[0,1]
    ks=(20,28,36)
    for key,color,label in (('floor_distance_to_residue_upper_ball',colors[2],'Floor lift'),
                            ('ceiling_distance_to_opposite_residue_upper_ball',colors[12],'Ceiling lift')):
        values=[]
        for k in ks:
            records=[x for x in source['artificial_singularity_checks'] if x['epsilon_power_of_two']==-k]
            values.append(max(midpoint(x[key])*2*pi*abs(x['harmonic']) for x in records))
        ax.semilogy(ks,values,'o-',color=color,label=label)
    ax.axhline(.5,color='#67717a',linestyle='--',linewidth=1.2)
    ax.text(35.5,.57,'Below 1/2 certifies a nonzero residue',ha='right',fontsize=9)
    ax.set(title='B. Artificial size harmonics stay singular',xlabel='-log2(epsilon), approaching Re(s)=1',ylabel='Maximum certified relative error to predicted residue',xticks=ks,ylim=(1e-5,.9))
    ax.legend(frameon=False,fontsize=9)
    ax.text(.98,.045,'27 controls; actual zeta is zero-free nearby',transform=ax.transAxes,ha='right',fontsize=9)

    ax=axes[1,0]
    for base,color in colors.items():
        records=[x for x in source['actual_zeta_log_angle_controls'] if x['base']==base]
        masses=[midpoint(x['log_zeta_positive_real_mass_ball']) for x in records]
        maxima=[max(midpoint(y['normalised_angular_moment_modulus_upper_ball']) for y in x['modes']) for x in records]
        ax.plot(masses,maxima,'o-',color=color,label=f'b={base}')
    ax.set(title='C. Actual log-zeta angular moments approach zero',xlabel='L = log(zeta(1+epsilon))',ylabel='Maximum of 31 nonconstant moment bounds')
    ax.grid(axis='y',alpha=.15)
    ax.legend(frameon=False)
    ax.text(.98,.95,'Branches certified from Re(s)=4\nIndependent anchor at Re(s)=5',transform=ax.transAxes,ha='right',va='top',fontsize=9)

    ax=axes[1,1]
    for base,color in colors.items():
        records=[x for x in source['actual_zeta_log_angle_controls'] if x['base']==base]
        masses=[midpoint(x['log_zeta_positive_real_mass_ball']) for x in records]
        bounds=[midpoint(next(y for y in x['mark_lower_bounds'] if y['orientation']=='floor')['genuine_U_zeta_series_lower_ball']) for x in records]
        independent=[]
        for x in records:
            record=next(y for y in audit['actual_zeta_log_angle_controls'] if y['base']==base and y['epsilon_power_of_two']==x['epsilon_power_of_two'])
            independent.append(midpoint(next(y for y in record['independent_U_lower_bounds'] if y['orientation']=='floor')['genuine_U_lower_ball']))
        ax.plot(masses,bounds,'o-',color=color,label=f'b={base}')
        ax.plot(masses,independent,'s--',color=color,markerfacecolor='white',alpha=.7)
    ax.set(title='D. Rigorous lower bounds for the infinite U series',xlabel='L = log(zeta(1+epsilon))',ylabel='Certified U_floor(u)(1+epsilon) lower bound')
    ax.grid(axis='y',alpha=.15)
    ax.legend(frameon=False,loc='upper left',fontsize=9)
    ax.text(.98,.065,'Solid: three exponential terms\nDashed: independent four-term bounds\nValues are bounds, not estimates of full U',
            transform=ax.transAxes,ha='right',fontsize=9)
    fig.savefig(OUT/'size_resonance.png',dpi=190)
    fig.savefig(OUT/'size_resonance.pdf')
    print('Saved size-results/size_resonance.png and size-results/size_resonance.pdf')


if __name__=='__main__':main()
