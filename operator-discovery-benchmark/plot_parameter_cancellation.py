#!/usr/bin/env python3
"""Standalone evidence plots with unchanged observed and proved semantics."""
import argparse
from pathlib import Path
from fractions import Fraction as Q
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import flint
from stable_scale_report import read,sha
from parameter_cancellation_report import summary


def main(d):
    s=summary(d);batch=read(d/'candidate_batch.json');val=read(d/'validation.json');arc=read(d/'archive.json');final=read(d/'final_evaluation.json');fig,axes=plt.subplots(1,3,figsize=(15,4.4));byid={r['id']:r for r in batch['radius_programs']}
    for mode,rid in arc['best_radius_by_mode'].items():
        rows=next(r['observations'] for r in val['radius_results'] if r['radius_id']==rid);points=[r for r in rows if r['index']==2];axes[0].loglog([float(Q(r['coordinate'])) for r in points],[float(flint.arb(r['bound_ball']).mid()) for r in points],marker='o',label=mode)
    axes[0].set(xlabel='Envelope coordinate V',ylabel='Proved coefficient envelope, m=2',title='Frozen radius selection');axes[0].legend(fontsize=8)
    families=sorted(batch['programs'],key=lambda r:(-r['family_certificate']['moment'],r['id']));pid=families[0]['id'];observations=[r for r in final['family_observations'] if r['program_id']==pid and Q(r['x']).denominator==1 and Q(r['x'])>3]
    for q in sorted({r['level'] for r in observations}):
        rr=[r for r in observations if r['level']==q];axes[1].loglog([float(Q(r['x'])) for r in rr],[float(flint.arb(r['certificate']['bound_ball']).mid())/float(Q(r['x'])) for r in rr],marker='o',label=f'new bound / x, q={q}')
        axes[1].loglog([float(Q(r['x'])) for r in rr],[r['old_triangle_certificate']['constant']*float(flint.arb(float(Q(r['x']))).log()+1) for r in rr],linestyle=':',label=f'old triangle / x, q={q}')
    axes[1].set(xlabel='Actual arithmetic scale x',ylabel='Certified upper envelope / x',title='High-order family normalization');axes[1].legend(fontsize=7)
    for m in s['compiled_jet_indices']:
        rows=[r for r in final['jet_observations'] if r['index']==m and Q(r['x']).denominator==1 and Q(r['x'])>3];axes[2].plot([float(Q(r['x'])) for r in rows],[float(flint.arb(r['signed_error_ball']).mid()) for r in rows],marker='o',label=f'jet m={m}')
    axes[2].axhline(0,color='grey',lw=.7);axes[2].set(xlabel='Actual arithmetic scale x',ylabel='Signed sum minus full center',title='Fresh actual signed jet observations');axes[2].legend(fontsize=8)
    fig.suptitle('Power-one bounds are proved; critical signed estimates remain open',fontsize=13);fig.tight_layout();fig.savefig(d/'parameter_cancellation_evidence.png',dpi=170);fig.savefig(d/'parameter_cancellation_evidence.pdf');plt.close(fig)
    obs={'source_protocol_sha256':sha(d/'protocol.json'),'source_archive_sha256':sha(d/'archive.json'),'source_final_sha256':sha(d/'final_evaluation.json'),'source_verification_sha256':sha(d/'verification.json'),
        'signed_actual_arithmetic_used':True,'full_parameter_jet_centers_used':True,'normalizations_and_factorials_charged':True,'ordinary_power_is_one':True,
        'envelope_coordinates_are_not_huge_prime_samples':True,'selected_family_id':pid,'selected_radius_ids':arc['best_radius_by_mode'],'new_case_fit_or_selection':False,'RH_proved':False}
    (d/'plot_observations.json').write_text(__import__('json').dumps(obs,indent=2)+'\n');print('Saved standalone parameter-cancellation evidence plots',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);main(p.parse_args().run_dir.resolve())
