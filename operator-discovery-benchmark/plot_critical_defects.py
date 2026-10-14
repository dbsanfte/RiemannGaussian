#!/usr/bin/env python3
"""Standalone signed-defect plots; the full residual is always retained."""
import argparse,json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from stable_scale_report import read,sha
from critical_defect_report import summary


def main(d):
    s=summary(d);batch=read(d/'candidate_batch.json');val=read(d/'validation.json');arc=read(d/'archive.json');final=read(d/'final_evaluation.json');pid=arc['selected_component_candidate_id'];fig,axes=plt.subplots(1,3,figsize=(15,4.5));rows=[]
    for split,data in [('training',batch['training']),('validation',val['data']),('fresh',final['data'])]:
        for row in data['rows']:
            o=next(o for o in row['candidate_observations'] if o['candidate_id']==pid);X=row['whole']['X'];rows.append({'X':X,'split':split,'diagonal':row['whole']['diagonal_defect']/X**2,'projected':o['signed_projection_defect']/X**2,'dense':o['signed_dense_residual_defect']/X**2,'full':row['whole']['signed_defect']/X**2})
    for key in ['diagonal','projected','dense','full']:axes[0].plot([r['X'] for r in rows],[r[key] for r in rows],marker='o',label=key)
    axes[0].set_xscale('log',base=2);axes[0].axhline(0,color='grey',lw=.7);axes[0].set(xlabel='Actual dyadic scale X',ylabel='Signed defect / X²',title='The dense arithmetic remainder stays');axes[0].legend(fontsize=8)
    ps=batch['candidates'];axes[1].plot([float(__import__('fractions').Fraction(p['beta'])) for p in ps],[float(__import__('fractions').Fraction(p['certificate']['component_power'])) for p in ps],marker='.',label='proved component power');axes[1].axhline(2,color='grey',linestyle='--',label='critical energy power');axes[1].axvline(float(__import__('fractions').Fraction(s['selected_cutoff_power'])),color='tab:green',linestyle=':',label='selected coverage');axes[1].set(xlabel='Primitive-cutoff power β',ylabel='Power charged to the component',title='Component bound does not bound full sum');axes[1].legend(fontsize=8)
    rr=final['positive_coefficient_controls'];axes[2].loglog([r['whole']['X'] for r in rr],[r['whole']['signed_defect']/r['whole']['X']**2 for r in rr],marker='o',label='positive full defect / X²');axes[2].loglog([r['whole']['X'] for r in rr],[r['projection']['all_scale_absolute_defect_upper']/r['whole']['X']**2 for r in rr],marker='s',label='proved positive projection bound / X²');axes[2].set(xlabel='Fresh dyadic scale X',ylabel='Counterfeit control / X²',title='Sparse control can hide a cubic full defect');axes[2].legend(fontsize=8)
    fig.suptitle('RH target: a uniform bound for the FULL signed defect is still missing',fontsize=13);fig.tight_layout();fig.savefig(d/'critical_defect_evidence.png',dpi=170);fig.savefig(d/'critical_defect_evidence.pdf');plt.close(fig)
    obs={'source_protocol_sha256':sha(d/'protocol.json'),'source_archive_sha256':sha(d/'archive.json'),'source_final_sha256':sha(d/'final_evaluation.json'),'source_verification_sha256':sha(d/'verification.json'),
        'signed_actual_arithmetic_used':True,'whole_signed_defect_and_dense_residual_retained':True,'component_bound_not_full_bound':True,'selected_cutoff_power':s['selected_cutoff_power'],
        'new_case_fit_or_selection':False,'RH_proved':False};(d/'plot_observations.json').write_text(json.dumps(obs,indent=2)+'\n');print('Saved signed-defect standalone evidence plots',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);main(p.parse_args().run_dir.resolve())
