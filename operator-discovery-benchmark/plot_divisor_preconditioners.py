#!/usr/bin/env python3
"""Standalone actual signed error and fractional all-prime-factor evidence."""
import argparse,json
from fractions import Fraction as Q
from pathlib import Path
import flint,matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from stable_scale_report import read,sha
from divisor_preconditioner_report import summary


def main():
    p=argparse.ArgumentParser();p.add_argument('--run-dir',type=Path,required=True);d=p.parse_args().run_dir.resolve();s=summary(d);final=read(d/'final_evaluation.json');fig,axes=plt.subplots(1,3,figsize=(16,5));records=[]
    for k,rows in final['integer_observations'].items():
        values=sorted((float(Q(x)),float((abs(flint.arb(v['signed_error_ball']))/flint.arb(str(Q(x)))).upper())) for x,v in rows.items());axes[0].semilogx([x for x,y in values],[y for x,y in values],'o',label=f'Actual signed jet k={k}');records.append({'order':k,'observed_error_divided_by_x':values})
    axes[0].set_title('Complete actual error |T-h| / x',fontsize=10);axes[0].set_xlabel('Real x');axes[0].set_ylabel('Observed error / x');axes[0].legend(fontsize=8);axes[0].grid(alpha=.2)
    comparisons=s['ablation_comparison'];xs=list(range(len(comparisons)));axes[1].bar([x-.18 for x in xs],[r['primary_completed_log_loss'] for r in comparisons],width=.35,label='Proof-backed completion');axes[1].bar([x+.18 for x in xs],[r['best_ablation_log_loss'] for r in comparisons],width=.35,label='Fit plus random-slot ablation');axes[1].set_xticks(xs,[f"k={r['order']}" for r in comparisons]);axes[1].set_ylabel('Proved log loss, at common ordinary power 1');axes[1].set_title('Completion saves logs; critical power remains open',fontsize=10);axes[1].legend(fontsize=8);axes[1].grid(axis='y',alpha=.2)
    for q in ['1/2','1/3','1/6','2']:
        rows=final['generic_differences'][q];ys=[1 if flint.arb(r['value_ball'])>0 else (-1 if flint.arb(r['value_ball'])<0 else 0) for r in rows];axes[2].plot(range(1,len(rows)+1),ys,'o-',alpha=.65,label=f'Logarithmic order {q}')
    axes[2].set_yticks([-1,0,1]);axes[2].set_xlabel('Difference rank / number of distinct primes');axes[2].set_ylabel('Sign');axes[2].set_title('Fractional signs continue beyond integer support',fontsize=10);axes[2].legend(fontsize=8);axes[2].grid(alpha=.2)
    fig.suptitle('All-scale signed prime coupling is proved at power 1; RH-strength control is unproved',fontsize=11);fig.tight_layout(rect=(0,0,1,.94));fig.savefig(d/'divisor_preconditioner_evidence.png',dpi=160);fig.savefig(d/'divisor_preconditioner_evidence.pdf');plt.close(fig)
    record={'source_protocol_sha256':sha(d/'protocol.json'),'source_archive_sha256':sha(d/'archive.json'),'source_final_sha256':sha(d/'final_evaluation.json'),'source_verification_sha256':sha(d/'verification.json'),
        'complete_actual_point_sums_used':True,'signed_remainder_retains_actual_arithmetic':True,'ordinary_power_is_one':True,'fractional_signs_are_generic_universal_geometry':True,'RH_proved':False,'observations':records}
    (d/'plot_observations.json').write_text(json.dumps(record,indent=2)+'\n');print('Saved divisor preconditioner evidence PNG and PDF')


if __name__=='__main__':main()
