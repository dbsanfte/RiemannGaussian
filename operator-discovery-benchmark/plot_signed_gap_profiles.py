#!/usr/bin/env python3
"""Standalone actual signed-gap and anonymous estimate evidence."""
import argparse,json
from pathlib import Path
from fractions import Fraction as Q
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from stable_scale_report import read,sha
from signed_gap_profile_report import summary


def main(d):
    s=summary(d);b=read(d/'candidate_batch.json');v=read(d/'validation.json');f=read(d/'final_evaluation.json');a=read(d/'analytical_review.json');fig,axes=plt.subplots(1,3,figsize=(15,4.5))
    for split,data in [('training',b['training_arithmetic']),('validation',v['arithmetic']),('fresh',f['arithmetic'])]:
        rows=data['rows'];axes[0].scatter([r['X'] for r in rows],[r['signed_defect']/r['X']**2 for r in rows],label=split)
    axes[0].set_xscale('log',base=2);axes[0].axhline(0,color='grey',lw=.7);axes[0].set(xlabel='Actual X',ylabel='Full signed defect / X²',title='The missing arithmetic estimate');axes[0].legend(fontsize=8)
    byid={r['program_id']:r for r in a['candidate_attempts']};xs=[];ys=[];colors=[]
    for r in f['program_results']:
        score=r['score'];xs.append(float(Q(score['max_charged_bound_over_generic'])));ys.append(score['finite_passes']);colors.append('tab:orange' if byid[r['program_id']]['conditional_constant_growth_consequences']['would_force_simple_critical_zeros_if_global_bound_proved'] else 'tab:blue')
    axes[1].scatter(xs,ys,c=colors,alpha=.6);axes[1].set_xscale('log');axes[1].set(xlabel='Maximum charged cost / generic upper bound',ylabel='Fresh finite half-gap passes',title='Orange adds a zero-simplicity condition')
    for split,rows in [('training',b['anonymous_minimum_responses']),('fresh',f['fresh_minimum_observations'])]:axes[2].scatter([r['mass'] for r in rows],[r['anonymous_response'] for r in rows],label=split,alpha=.6)
    terms=a['minimum_lead']['terms'];J=list(range(17));P=[sum(float(Q(c))*j**i for i,m,c in terms) for j in J];axes[2].plot(J,P,color='grey',label='detected and proved polynomial');axes[2].set(xlabel='Omitted tail-row count J',ylabel='Minimum binary-prefix square energy',title='A global bound inferred then proved');axes[2].legend(fontsize=8)
    fig.suptitle('Constants and critical exponents are decoupled; the global signed arithmetic gap remains open',fontsize=12);fig.tight_layout();fig.savefig(d/'signed_gap_profile_evidence.png',dpi=170);fig.savefig(d/'signed_gap_profile_evidence.pdf');plt.close(fig)
    obs={key:sha(d/name) for key,name in [('source_protocol_sha256','protocol.json'),('source_final_sha256','final_evaluation.json'),('source_queue_sha256','proof_queue.json'),('source_verification_sha256','verification.json'),('source_analytical_sha256','analytical_review.json'),('source_analytical_verification_sha256','analytical_verification.json')]};obs.update({'actual_signed_arithmetic_kept':True,'new_constants_not_fit_from_final':True,'new_case_fit_or_selection':False,'global_critical_signed_bound_proved':False,'RH_proved':False});(d/'plot_observations.json').write_text(json.dumps(obs,indent=2)+'\n');print('Saved actual signed-gap and inferred global-bound plots',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);main(p.parse_args().run_dir.resolve())
