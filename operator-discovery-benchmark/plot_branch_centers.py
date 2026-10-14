#!/usr/bin/env python3
"""Standalone evidence: signed errors, full-center costs, and finite scope."""
from pathlib import Path
import argparse
from fractions import Fraction as Q
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import flint
from stable_scale_report import BASE,read,sha
from stable_scale_search import write
from branch_center_report import summary

def main(d):
    s=summary(d);batch=read(d/'candidate_batch.json');final=read(d/'final_evaluation.json');cases=read(d/'final_cases.json');programs=batch['programs'];q=cases['levels'][0]
    chosen=sorted(programs,key=lambda p:(-p['recovery_certificate'].get('first_nonzero_moment_order',0),p['id']))[:4];fig,axes=plt.subplots(1,3,figsize=(15.5,4.8));palette=['#335C81','#D1495B','#447A45','#9A6FB0']
    for p,color in zip(chosen,palette):
        xs=sorted(cases['points'],key=Q);ys=[float(flint.arb(final['responses'][p['id']][str(q)][x]).mid())/float(Q(x))**0.5 for x in xs];m=p['recovery_certificate']['first_nonzero_moment_order'];axes[0].plot([float(Q(x)) for x in xs],ys,'o-',color=color,label=f"m={m}, {p['id'][:6]}")
    axes[0].axhline(0,color='#888888',lw=.8);axes[0].set_xscale('log');axes[0].set_xlabel('Ordinary arithmetic scale x');axes[0].set_ylabel(r'Signed normalized family error / $\sqrt{x}$');axes[0].set_title(f'Complete real-cut center; fresh q={q}');axes[0].legend(fontsize=8)
    ms=[p['recovery_certificate'].get('first_nonzero_moment_order',0) for p in programs];keys=sorted(set(ms));axes[1].bar(keys,[ms.count(m) for m in keys],color='#335C81');axes[1].set_xticks(keys);axes[1].set_xlabel('First nonzero parameter moment m');axes[1].set_ylabel('Families with conditional all-height recovery');axes[1].set_title('Signed parameter filters retain ordinary zeros')
    comp=s['ablation_comparison'];costs=[r['best_finite_validated_charged_cost'] for r in comp];axes[2].bar(['Promotion','Equal-slot random'],[v or 0 for v in costs],color=['#447A45','#D1495B']);axes[2].set_ylabel('Best fully charged conditional reciprocal cost');axes[2].set_title('Finite validation at the same response budget')
    fig.suptitle('Fractional arithmetic: full centers and cofinal recovery\nProved global power = 1; critical signed estimates remain unproved',fontsize=13);fig.tight_layout(rect=[0,0,1,.88]);fig.savefig(d/'branch_center_evidence.png',dpi=165);fig.savefig(d/'branch_center_evidence.pdf');plt.close(fig)
    write(d/'plot_observations.json',{'source_protocol_sha256':sha(d/'protocol.json'),'source_archive_sha256':sha(d/'archive.json'),'source_final_sha256':sha(d/'final_evaluation.json'),'source_verification_sha256':sha(d/'verification.json'),
        'signed_actual_arithmetic_used':True,'full_real_cut_centers_used':True,'normalizations_charged':True,'ordinary_power_is_one':True,'conditional_costs_are_finite_only':True,'RH_proved':False})

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);main(p.parse_args().run_dir.resolve())
