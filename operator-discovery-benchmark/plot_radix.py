#!/usr/bin/env python3
"""Export certified radix degrees, uniform bounds and zeta-root controls."""

from fractions import Fraction as Q
from pathlib import Path
import json
import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
import numpy as np

BASE=Path(__file__).resolve().parent
DEST=BASE/'radix-results'


def number(value):
    return float(flint.arb(value).mid())


def main():
    exact=json.loads((DEST/'radix_search.json').read_text())
    data=json.loads((DEST/'radix_analytic.json').read_text())
    independent=json.loads((DEST/'radix_analytic_verification.json').read_text())
    assert exact['all_passed'] and data['all_passed'] and independent['all_passed']
    plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False})
    fig,axes=plt.subplots(2,2,figsize=(14.2,10.8))
    fig.suptitle('Global radix transfers: root types and complete branch tests',fontsize=19,y=.97)

    ax=axes[0,0]
    rows=exact['log_polynomial_grammar']['records']
    bases=[row['radix'] for row in rows]
    degrees=[row['inferred_polynomial_degree'] for row in rows]
    line=np.arange(2,8)
    ax.plot(line,line-1,color='#176e81',lw=2,label='Proved degree: b - 1')
    ax.scatter(bases,degrees,s=65,color='#b45532',zorder=3,label='Exact grammar observations')
    ax.set_xticks(bases);ax.set_yticks(range(1,7))
    ax.set_xlabel('Radix b');ax.set_ylabel('Polynomial degree in LOG zeta')
    ax.set_title('Nilpotence determines the required branch difference',loc='left',fontsize=12)
    ax.legend(loc='upper left',fontsize=10);ax.grid(alpha=.18)
    ax.text(.97,.04,'Radix 3: compare F\u2080, F\u2081, F\u2082\nA single pointwise jump can vanish.',
            transform=ax.transAxes,ha='right',fontsize=10,color='#46525a')

    ax=axes[0,1]
    rows=data['leading_self_similarity_controls']['records']
    x=np.arange(len(rows))
    lower=[number(row['uniform_critical_half_plane_H_modulus_lower_ball']) for row in rows]
    ax.bar(x,lower,color='#176e81',width=.55)
    for i,value in enumerate(lower):ax.text(i,value+.025,f'{np.floor(value*1e4)/1e4:.4f}',ha='center',fontsize=10)
    ax.set_xticks(x,[str(row['radix']) for row in rows]);ax.set_ylim(0,1.15)
    ax.set_xlabel('Radix b, beta = 1');ax.set_ylabel('Proved lower bound on |H(s)|')
    ax.set_title('Leading coefficient is nonzero at every height',loc='left',fontsize=12)
    ax.text(.04,.95,'Re(s) >= 1/2\nH(s) = F(b s; b, beta/b)',transform=ax.transAxes,
            va='top',fontsize=10,color='#46525a')
    ax.grid(axis='y',alpha=.18)

    ax=axes[1,0]
    source=data['created_operator_zero'];audit=independent['created_operator_zero_audit']
    radius=1e6*float(Q(source['radius']));inner=1e6*float(Q(audit['radius']))
    ax.add_patch(Circle((0,0),radius,facecolor='#dceef1',edgecolor='#176e81',lw=2,
                        label='Producer: radius 10 micro-units'))
    ax.add_patch(Circle((0,0),inner,facecolor='#c4d9b2',edgecolor='#6c913d',lw=2,
                        label='Independent: radius 5 micro-units'))
    ax.scatter([0],[0],color='#46525a',marker='+',s=90,zorder=4,label='Numerical disk centre c')
    ax.set_xlim(-13,13);ax.set_ylim(-13,13);ax.set_aspect('equal')
    ax.set_xlabel('Re(s - c), micro-units');ax.set_ylabel('Im(s - c), micro-units')
    ax.set_title('Same simple operator zero; zeta is nonzero',loc='left',fontsize=12)
    ax.legend(fontsize=8.4,loc='upper right')
    centre=source['disk_centre']
    ax.text(.02,.04,f'c = {float(centre[0]):.6f} + {float(centre[1]):.6f}i\n'
            '|zeta| > 0.4895; |S\u2083(input half-root)| > 0.5972',
            transform=ax.transAxes,fontsize=8.5,color='#46525a')
    ax.grid(alpha=.15)

    ax=axes[1,1]
    rows=data['actual_zeta_zero_branch_ladder_controls']['records']
    x=np.arange(3);width=.32
    for i,row in enumerate(rows):
        values=[number(r['second_log_monodromy_difference_modulus_lower_ball'])
                for r in row['root_parameters_and_second_monodromy_bounds']]
        ax.bar(x+(i-.5)*width,values,width,color=('#176e81','#78a442')[i],
               label=f'Existing zero: t = {float(row["disk_centre"][1]):.5f}')
    ax.set_xticks(x,['1','1/2','1/4']);ax.set_ylim(0,31)
    ax.set_xlabel('Ordinary input exponent beta')
    ax.set_ylabel('Lower bound on |F\u2082 - 2F\u2081 + F\u2080|')
    ax.set_title('Branch differences detect ordinary zeta zeros',loc='left',fontsize=12)
    ax.legend(loc='upper right',fontsize=9)
    ax.text(.97,.46,'Whole-disk bounds,\nnot sampled loops',transform=ax.transAxes,
            ha='right',fontsize=10,color='#46525a')
    ax.grid(axis='y',alpha=.18)

    fig.text(.055,.025,'Six new full coefficient/native-zeta comparisons bring the total to 144. '
             'Five exact and six analytic audit gates pass.\n'
             'Typed roots differ from ordinary output roots. No zeta zero is newly located, '
             'no off-line zero is excluded, and historical novelty is unresolved.',fontsize=10,color='#46525a')
    fig.subplots_adjust(left=.065,right=.975,bottom=.12,top=.9,wspace=.27,hspace=.32)
    fig.savefig(DEST/'radix_overview.png',dpi=180)
    fig.savefig(DEST/'radix_overview.pdf')
    print('Saved radix overview PNG/PDF',flush=True)


if __name__=='__main__':
    main()
