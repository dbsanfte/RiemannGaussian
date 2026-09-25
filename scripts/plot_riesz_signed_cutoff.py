#!/usr/bin/env python3
"""Plot the optional cutoff MODEL; no discrete-prime or tail bound is shown."""
import argparse
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--order',type=int,default=512)
    args=parser.parse_args()
    data=json.loads(args.input.read_text())
    rows=[r for r in data['rows'] if r['N']==args.order]
    counts=sorted({r['count'] for r in rows})
    groups=[np.array([r['signed'] for r in rows if r['count']==k]) for k in counts]
    mean=np.array([np.mean(g) for g in groups])
    lo=np.array([np.min(g) for g in groups]);hi=np.array([np.max(g) for g in groups])
    plt.rcParams.update({'font.size':11,'svg.hashsalt':'riesz-signed-cutoff-model'})
    fig,axes=plt.subplots(1,2,figsize=(12,4.8),gridspec_kw={'width_ratios':[1.1,1]})
    axes[0].bar(counts,mean*1000,color=['#dd7958' if v>=0 else '#397faa' for v in mean])
    axes[0].errorbar(counts,mean*1000,yerr=np.vstack((mean-lo,hi-mean))*1000,
                    fmt='none',ecolor='#202b36',capsize=3)
    axes[0].axhline(0,color='#202b36',lw=.8)
    axes[0].set(xlabel='Number of prime factors',ylabel='Signed model contribution × 1000',
                title='Opposing counts carry the main cancellation',xticks=counts)
    summaries=[r for r in data['summaries'] if r['N']==args.order]
    for i,row in enumerate(summaries):
        axes[1].plot(data['profile_slots'],np.array(row['weighted_profile'])*1000,
                     alpha=.8,lw=1.5,label=f'Scramble {i+1}')
    axes[1].axhline(0,color='#202b36',lw=.8)
    axes[1].set(xlabel='Position across the divisor-cutoff window',
                ylabel='Joint weighted profile × 1000',title='Small imbalance remains after joining counts')
    axes[1].legend(frameon=False,fontsize=9)
    for ax in axes:
        ax.spines[['top','right']].set_visible(False)
        ax.grid(axis='y',alpha=.15)
    fig.suptitle(f'Weighted signed cutoff investigation · N={args.order} · y=0',fontsize=15)
    fig.text(.5,.015,'Ordinary-prime-density MODEL, counts 3–14. Bars show scramble ranges, not certified errors.\n'
             'No discrete-prime transport or estimate for counts 15–55.',ha='center',fontsize=9,color='#52606b')
    fig.tight_layout(rect=[0,.09,1,.94])
    fig.savefig(args.output,metadata={'Date':None})
    if args.output.suffix.lower()=='.svg':
        args.output.write_text('\n'.join(line.rstrip() for line in
                                        args.output.read_text().splitlines())+'\n')


if __name__=='__main__':
    main()
