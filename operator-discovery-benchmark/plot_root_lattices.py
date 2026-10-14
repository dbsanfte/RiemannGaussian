#!/usr/bin/env python3
"""Standalone plot of normalized actual roots and typed signed cancellation."""
import argparse,json,math
from pathlib import Path
from fractions import Fraction as Q
import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from stable_scale_report import read,sha
from root_lattice_report import summary


def magnitude(txt):
    value=float(abs(flint.arb(txt)).upper())
    return max(value,1e-300)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--run-dir',type=Path,required=True);args=parser.parse_args();d=args.run_dir.resolve();s=summary(d);final=read(d/'final_evaluation.json');spec=read(d/'protocol.json');obs=final['program_observables'];fig,axes=plt.subplots(1,3,figsize=(16,5));observed=[]
    for r in ['1/2','1/3','1/6']:
        choices=[row for row in s['recovering_records'] if row['program']['parameters'][2]==r]
        if not choices:continue
        row=min(choices,key=lambda row:row['final_outcome']['maximum_ratio']);p=row['program'];c=row['candidate'];o=row['final_outcome'];q=max(o['constants'],key=int)
        values=sorted((float(Q(M)),magnitude(v['actual_centered_ball'])) for M,v in obs[p['id']].items());xs=[x for x,y in values];ys=[y for x,y in values]
        line=axes[0].loglog(xs,ys,'o',label=f'Actual signed r={r}')[0];color=line.get_color();f=c['frontier'];theta=float(Q(f['limit']))+float(Q(f['margin']))/int(q)**float(Q(f['approach_power']));C=float(Q(o['constants'][q]));dd=float(Q(f['log_power']))
        axes[0].loglog(xs,[C*x**theta*math.log(math.e+x)**dd for x in xs],'--',color=color,alpha=.7)
        observed.append({'program_id':p['id'],'channel':'actual_centered_ball','points':values,'fitted_q':q,'fitted_curve_is_global_proof':False})
    axes[0].set_title('Actual roots: critical fits remain unproved',fontsize=10);axes[0].set_xlabel('Ordinary arithmetic index M, X=M^r');axes[0].set_ylabel('Absolute centered signed response');axes[0].legend(fontsize=8);axes[0].grid(alpha=.2)
    if s['signed_calibration_records']:
        row=s['signed_calibration_records'][0];p=row['program'];values=sorted((float(Q(M)),magnitude(v['actual_centered_ball'])) for M,v in obs[p['id']].items());xs=[x for x,y in values];ys=[y for x,y in values];cert=p['rapid_certificates']['1'];C=float(flint.arb(cert['constant_ball']).upper())
        axes[1].loglog(xs,ys,'o',label='Actual signed mu*1 collapse');axes[1].loglog(xs,[C/x for x in xs],label='Proved C/M, all M>0');observed.append({'program_id':p['id'],'channel':'actual_centered_ball','points':values,'proved_decay_order':'1','ordinary_zeta_information_preserved':False})
        axes[1].legend(fontsize=8)
    axes[1].set_title('Signed global decay: ordinary zeros erased',fontsize=10);axes[1].set_xlabel('M');axes[1].set_ylabel('Absolute response (floored at 1e-300)');axes[1].grid(alpha=.2)
    pairs=[]
    for r in s['arithmetic_dilation_factors']:
        rows=[row for row in s['recovering_records'] if row['program']['parameters'][2]==r];costs=[row['final_outcome']['recovery_cost']['best_log_cost'] for row in rows if row['final_outcome']['recovery_cost']['best_log_cost'] is not None]
        if costs:pairs.append((r,min(costs)))
    axes[2].bar(range(len(pairs)),[v for r,v in pairs],color='steelblue');axes[2].set_xticks(range(len(pairs)),[f'r={r}' for r,v in pairs]);axes[2].set_ylabel('Conditional reciprocal bound: log cost');axes[2].set_title('Full Mellin normalization charged',fontsize=10);axes[2].grid(axis='y',alpha=.2)
    axes[2].text(.5,.97,'Costs require an unproved uniform signed estimate',ha='center',va='top',transform=axes[2].transAxes,fontsize=8);axes[2].margins(y=.18)
    fig.suptitle('Arithmetic roots include square, cube and sixth roots; RH-strength signed control is still open',fontsize=11);fig.tight_layout(rect=(0,0,1,.94));fig.savefig(d/'root_lattice_evidence.png',dpi=160);fig.savefig(d/'root_lattice_evidence.pdf');plt.close(fig)
    record={'source_protocol_sha256':sha(d/'protocol.json'),'source_archive_sha256':sha(d/'archive.json'),'source_final_sha256':sha(d/'final_evaluation.json'),'source_verification_sha256':sha(d/'verification.json'),
        'observations':observed,'conditional_cost_by_arithmetic_root':pairs,'complete_infinite_arithmetic_values_used':True,'scales_normalized_to_ordinary_index':True,
        'signed_reference_is_actual_inverse_arithmetic':True,'signed_rapid_bound_erases_ordinary_zeta':True,'root_dashed_curves_are_fitted_only':True,'RH_proved':False}
    (d/'plot_observations.json').write_text(json.dumps(record,indent=2)+'\n');print('Saved standalone root arithmetic evidence PNG and PDF')


if __name__=='__main__':main()
