#!/usr/bin/env python3
"""Standalone exact detector evidence; no extra fitting or lead selection."""
import argparse,json
from pathlib import Path
from fractions import Fraction as Q
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from stable_scale_report import read,sha
from divisor_dual_report import summary


def main(d):
    s=summary(d);val=read(d/'validation.json');arc=read(d/'archive.json');batch=read(d/'candidate_batch.json');final=read(d/'final_evaluation.json');fig,axes=plt.subplots(1,3,figsize=(15,4.5))
    for origin,label in [('baseline','baseline'),('learned_zero_forcing_mask','learned mask'),('equal_slot_random_mask','random mask')]:
        pids={p['id'] for p in batch['programs'] if p['origin']==origin};scores=[r for r in val['scores'] if r['program_id']in pids];axes[0].scatter(range(len(scores)),[r['positive_matrix_cases'] for r in scores],label=label,alpha=.65)
    axes[0].set(xlabel='Frozen scalar-profile index',ylabel='Finite positive validation matrices',title='Equal-profile mask evidence');axes[0].legend(fontsize=8)
    rows=final['matrix_certificates']
    for positive,label,color in [(True,'exact positive matrix','tab:green'),(False,'exact negative direction / missing','tab:red')]:
        sub=[r for r in rows if bool(r['certificate'].get('finite_matrix_PSD'))==positive];axes[1].scatter([r['X'] for r in sub],[float(Q(r['fully_charged_bound_over_generic'])) for r in sub],label=label,color=color,alpha=.7)
    axes[1].axhline(1,color='grey',ls='--');axes[1].set_yscale('log');axes[1].set(xlabel='Fresh X',ylabel='Fully charged bound / generic upper bound',title='All arithmetic and forcing costs kept');axes[1].legend(fontsize=8)
    actual=final['actual_signed_defects'];axes[2].plot([r['X'] for r in actual],[r['exact_actual_signed_defect']/r['X']**2 for r in actual],marker='o',label='actual µ signed defect / X²');axes[2].axhline(0,color='grey',lw=.7);axes[2].set(xlabel='Fresh X',ylabel='Signed energy defect / X²',title='Actual arithmetic, finite scales');axes[2].legend(fontsize=8)
    fig.suptitle('Exact leads are frozen for analytical proof attempts; global RH estimate remains open',fontsize=12);fig.tight_layout();fig.savefig(d/'divisor_dual_evidence.png',dpi=170);fig.savefig(d/'divisor_dual_evidence.pdf');plt.close(fig)
    obs={key:sha(d/name) for key,name in [('source_protocol_sha256','protocol.json'),('source_archive_sha256','archive.json'),('source_queue_sha256','proof_queue.json'),('source_final_sha256','final_evaluation.json'),('source_verification_sha256','verification.json')]};obs.update({'fully_charged_full_signed_defect_retained':True,'new_case_fit_or_selection':False,'global_critical_matrix_PSD_proved':False,'RH_proved':False});(d/'plot_observations.json').write_text(json.dumps(obs,indent=2)+'\n');print('Saved divisor-dual standalone evidence plots',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);main(p.parse_args().run_dir.resolve())
