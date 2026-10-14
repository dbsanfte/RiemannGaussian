#!/usr/bin/env python3
"""Standalone figure of complete signed sums, fitted targets and proved scope."""
import argparse,json,math
from fractions import Fraction as Q
from pathlib import Path
import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from kernel_correlation_report import summary,text_report
from stable_scale_report import read,sha


def write(path,value):Path(path).write_text(json.dumps(value,indent=2)+'\n')


def number(txt):return float(flint.arb(txt).mid())


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run-dir',type=Path,required=True);args=parser.parse_args();d=args.run_dir.resolve();s=summary(d)
    spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');validation=read(d/'validation_data.json');final=read(d/'final_evaluation.json');cal=read(d/'parameter_calibration.json')
    survivors=s['RH_if_uniform_finite_survivors']
    def best(kind):
        rows=[r for r in survivors if r['candidate']['kind']==kind]
        if not rows:rows=[r for r in s['records'] if r['candidate']['kind']==kind and r['candidate']['RH_sufficient_if_uniform']]
        if not rows:return None
        return min(rows,key=lambda r:(r['candidate']['recovery_cost']['best_log_cost'] if r['candidate']['recovery_cost'].get('best_log_cost') is not None else 1e100,r['candidate']['id']))
    E,Z=best('energy'),best('density');plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
    fig,axes=plt.subplots(1,3,figsize=(15,5),layout='constrained');colors={'training':'#687582','validation':'#d27d2d','fresh':'#6c4db6'}
    def groups(record):
        i=record['program']['id']
        return [('training',batch['training_observables'][i]),('validation',validation['program_observables'][i]),('fresh',final['program_observables'][i])]
    if E:
        for label,rows in groups(E):
            pts=sorted([(float(Q(X)),number(r['energy_ball'])/number(r['diagonal_ball'])) for X,r in rows.items() if number(r['diagonal_ball'])>0])
            axes[0].scatter([p[0] for p in pts],[p[1] for p in pts],c=colors[label],s=23,label=label)
        axes[0].set_xscale('log');axes[0].set_yscale('symlog',linthresh=.001);axes[0].axhline(1,c='#9aa2a9',ls='--',lw=1)
        axes[0].set_title('Complete Gram response / diagonal');axes[0].set_ylabel(r'$E_H(X)/D_H(X)$');axes[0].legend(frameon=False)
        axes[0].text(.04,.04,r'$C_H/D_H=E_H/D_H-1$'+'\nFull signed cross terms are retained.',transform=axes[0].transAxes,fontsize=9)
    else:axes[0].text(.1,.5,'No recovering energy candidate in archive.',transform=axes[0].transAxes)
    if Z:
        c,p=Z['candidate'],Z['program'];f=c['frontier'];Cs=dict(c['illustrative_constants_by_q'],**next(o['constants'] for o in cal['illustrative_free_constants'] if o['candidate_id']==c['id']))
        observers=c['recovery_cost']['observers']+Z['final_outcome']['fresh_parameter_recovery_cost']['observers']
        available=[r for r in observers if 'log_cost' in r];q=min(available,key=lambda r:r['log_cost'])['q'] if available else min(map(int,Cs))
        theta=float(Q(f['limit']))+float(Q(f['margin']))/q**float(Q(f['approach_power']));logpower=float(Q(f['log_power']))
        xs=[]
        for label,rows in groups(Z):
            pts=sorted([(float(Q(X)),max(abs(number(r['density_correction_ball'])),1e-100)) for X,r in rows.items()]);xs.extend(p[0] for p in pts)
            axes[1].scatter([x for x,y in pts],[y/x**.25 for x,y in pts],c=colors[label],s=23)
        xmin,xmax=min(xs),max(xs);grid=[math.exp(math.log(xmin)+(math.log(xmax)-math.log(xmin))*j/100) for j in range(101)]
        C=float(Q(Cs[str(q)]));V=number(p['diagonal_certificate']['signed_remainder_constant_ball'])
        axes[1].plot(grid,[C*x**(theta-.25)*math.log(math.e+x)**logpower for x in grid],c='#6c4db6',ls='--',label=f'fitted target, q={q}')
        axes[1].plot(grid,[V*x**.25 for x in grid],c='#3d8063',lw=1.5,label='proved all-scale bound')
        axes[1].set_xscale('log');axes[1].set_yscale('log');axes[1].set_title('Signed squarefree density correction');axes[1].set_ylabel(r'$|D_H(X)-A_HX|/X^{1/4}$');axes[1].legend(frameon=False,fontsize=9)
    else:axes[1].text(.1,.5,'No recovering density candidate in archive.',transform=axes[1].transAxes)
    for kind,record,color in [('energy',E,'#24629b'),('density',Z,'#8b3f73')]:
        if not record:continue
        rows=record['candidate']['recovery_cost']['observers']+record['final_outcome']['fresh_parameter_recovery_cost']['observers']
        pairs=sorted((r['q'],r['log_cost']) for r in rows if 'log_cost' in r)
        axes[2].scatter([q for q,c in pairs],[c for q,c in pairs],c=color,s=32,label=kind)
    axes[2].set_xscale('log');axes[2].set_title('Conditional ordinary-zeta recovery');axes[2].set_ylabel('log of fully charged reciprocal bound');axes[2].legend(frameon=False)
    axes[2].text(.04,.04,'Same ordinary-zeta query: 5/8 + 16i\nGrowth premise remains unproved.',transform=axes[2].transAxes,fontsize=9)
    for i,ax in enumerate(axes):ax.set_xlabel('scale X' if i<2 else 'fractional-approach parameter q');ax.grid(alpha=.15)
    fig.suptitle('Signed arithmetic search: complete infinite sums, finite fitted estimates, no RH proof',fontsize=14)
    fig.savefig(d/'kernel_correlation_evidence.png',dpi=175);fig.savefig(d/'kernel_correlation_evidence.pdf');plt.close(fig)
    write(d/'plot_observations.json',{'source_protocol_sha256':sha(d/'protocol.json'),'source_archive_sha256':sha(d/'archive.json'),
        'source_final_sha256':sha(d/'final_evaluation.json'),'source_verification_sha256':sha(d/'verification.json'),
        'energy_candidate_id':E['candidate']['id'] if E else None,'density_candidate_id':Z['candidate']['id'] if Z else None,
        'complete_infinite_arithmetic_values_used':True,'density_green_curve_is_proved_global_sqrt_bound':True,
        'density_dashed_curve_is_only_fitted':True,'observer_panel_is_conditional':True,'finite_cases_do_not_prove_uniform_growth':True,'RH_proved':False})
    (d/'report.txt').write_text(text_report(s))
    print('Wrote scoped report and PNG/PDF evidence figure.')


if __name__=='__main__':main()
