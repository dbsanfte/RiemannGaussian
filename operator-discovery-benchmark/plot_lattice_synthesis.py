#!/usr/bin/env python3
"""Standalone evidence figure; proved reference bounds are explicitly typed."""
import argparse
from pathlib import Path
from fractions import Fraction as Q
import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from stable_scale_report import read,sha,digest
from lattice_synthesis_report import summary


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--run-dir',type=Path,required=True);args=parser.parse_args();d=args.run_dir.resolve();s=summary(d);final=read(d/'final_evaluation.json');batch=read(d/'candidate_batch.json');spec=read(d/'protocol.json')
    ps={p['id']:p for p in batch['programs']};ref=s['reference_records'][0]['program'];actual=(s['RH_if_uniform_finite_survivors'] or s['records'])[0];p=actual['program'];c=actual['candidate'];o=actual['final_outcome'];q=min(o['constants'],key=int);rows=final['program_observables'];fig,axes=plt.subplots(1,3,figsize=(16,5));observed=[]
    for ax,program,channel,label in [(axes[0],ref,'unit_two_residue_residual_ball','Unit reference: globally certified'),(axes[1],p,'inverse_centered_ball','Actual Möbius arithmetic: critical bound unproved')]:
        values=sorted((float(Q(X)),float(abs(flint.arb(v[channel])).upper())) for X,v in rows[program['id']].items());xs=[x for x,y in values];ys=[max(y,1e-65) for x,y in values]
        ax.loglog(xs,ys,'o',label='Complete infinite response enclosure');ax.set_title(label,fontsize=10);ax.set_xlabel('X');ax.set_ylabel('Absolute centered response');ax.grid(alpha=.2)
        if channel.startswith('unit'):
            C=float(flint.arb(program['reference_decay_certificates']['1']['constant_ball']).upper());ax.loglog(xs,[C/x for x in xs],label='Proved C / X (unit arithmetic only)')
        else:
            r=float(Q(program['parameters'][2]));V=float(flint.arb(program['weak_actual']['constant_ball']).upper());f=c['frontier'];theta=float(Q(f['limit']))+float(Q(f['margin']))/int(q)**float(Q(f['approach_power']));C=float(Q(o['constants'][q]));d0=float(Q(f['log_power']))
            ax.loglog(xs,[V*x**(1/r) for x in xs],label='Proved weak actual bound');ax.loglog(xs,[C*x**theta*__import__('math').log(__import__('math').e+x)**d0 for x in xs],'--',label=f'Fitted critical frontier, q={q}')
        ax.legend(fontsize=8);observed.append({'program_id':program['id'],'channel':channel,'points':values})
    parts=[]
    for r in spec['r_enumeration']['selected']:
        candidate=next(p for p in ps.values() if p['parameters'][2]==r);parts.append((r,list(map(Q,candidate['zero_exceptions']['real_parts']))))
    ax=axes[2]
    for i,(r,E) in enumerate(parts):
        ax.scatter([float(x) for x in E],[i]*len(E),s=60)
        if not E:ax.text(.58,i,'Empty: individual RH bridge',va='center',fontsize=9)
    ax.axvline(.5,color='black',ls=':');ax.set_xlim(.48,1.02);ax.set_yticks(range(len(parts)),[f'r = {r}' for r,E in parts]);ax.set_xlabel('Exceptional Re(ρ), conditional on a uniform bound');ax.set_title('Fractional constraints combine by exact intersection',fontsize=10);ax.grid(axis='x',alpha=.2)
    fig.suptitle('Reference estimates are proved; RH-strength actual signed estimates remain open',fontsize=12);fig.tight_layout(rect=(0,0,1,.94));fig.savefig(d/'lattice_synthesis_evidence.png',dpi=160);fig.savefig(d/'lattice_synthesis_evidence.pdf');plt.close(fig)
    obs={'source_protocol_sha256':sha(d/'protocol.json'),'source_archive_sha256':sha(d/'archive.json'),'source_final_sha256':sha(d/'final_evaluation.json'),'source_verification_sha256':sha(d/'verification.json'),
        'observations':observed,'complete_infinite_arithmetic_values_used':True,'reference_curve_is_proved_unit_bound_only':True,
        'actual_solid_curve_is_weak_global_bound':True,'actual_dashed_curve_is_fitted_only':True,'exception_sets_are_conditional_on_unproved_actual_bounds':True,'RH_proved':False}
    (d/'plot_observations.json').write_text(__import__('json').dumps(obs,indent=2)+'\n');print('Saved standalone lattice evidence PNG and PDF')


if __name__=='__main__':main()
