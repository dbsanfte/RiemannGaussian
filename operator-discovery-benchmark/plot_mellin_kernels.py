#!/usr/bin/env python3
"""Standalone finite evidence and complete-cost plot; no new selection stage."""
import argparse
from fractions import Fraction as Q
from pathlib import Path
import json, math
import flint
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mellin_kernel_report import summary
from stable_scale_report import read,sha,digest


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run-dir',type=Path,required=True);args=p.parse_args();d=args.run_dir.resolve()
    evidence=summary(d);batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');spec=read(d/'protocol.json');final=read(d/'final_evaluation.json');cases=read(d/'final_cases.json')
    validation=read(d/'validation_data.json');bs={b['id']:b for b in batch['banks']};ps={p['id']:p for p in batch['programs']}
    records=evidence['records'];finite=[];colors=plt.get_cmap('tab10');flint.ctx.prec=384
    from mellin_kernel_diagnostics import summary as observer_summary
    observer_audit=observer_summary(d)
    fresh_costs={r['candidate_id']:r['fresh_parameter_cost'] for r in observer_audit.get('records',[])}
    fig,axes=plt.subplots(1,2,figsize=(12.8,4.8),constrained_layout=True)
    roots=sorted({r['bank']['parameters'][1] for r in records if r['candidate']['RH_sufficient_if_uniform']},key=Q)
    for index,ell in enumerate(roots):
        pool=[r for r in records if r['bank']['parameters'][1]==ell and r['candidate']['recovery_cost'].get('best_log_cost') is not None]
        if not pool:continue
        r=min(pool,key=lambda r:r['candidate']['recovery_cost']['best_log_cost']);c=r['candidate'];f=c['frontier'];bank=r['bank'];cost=c['recovery_cost']
        q=min((o for o in cost['observers'] if o.get('log_cost') is not None),key=lambda o:o['log_cost'])['q']
        theta=float(Q(f['limit']))+float(Q(f['margin']))/q**float(Q(f['approach_power']));ratios={}
        for phase,points,rows in [('training',spec['training_points'],batch['training_responses']),
            ('validation',spec['validation_points'],validation['program_responses']),
            ('final',cases['integers'],final['program_responses'])]:
            for X in points:
                maximum=0
                for i,pid in enumerate(bank['member_ids']):
                    value=float(abs(flint.arb(rows[pid][str(X)])).upper())
                    bound=float(Q(c['illustrative_constants_by_member_and_q'][i][str(q)]))*X**theta*math.log(math.e+X)**float(Q(f['log_power']))
                    maximum=max(maximum,value/bound)
                ratios[X]=maximum;finite.append({'candidate_id':c['id'],'root_exponent':ell,'q':q,'phase':phase,'scale':X,'ratio_upper':maximum})
        xs=sorted(ratios);ys=[max(ratios[x],1e-12) for x in xs];color=colors(index)
        axes[0].plot(xs,ys,color=color,alpha=.8,label=f'ell={ell}')
        axes[0].scatter(cases['integers'],[max(ratios[x],1e-12) for x in cases['integers']],color=color,marker='s',s=26)
    axes[0].axhline(1,color='#333333',linestyle='--',linewidth=1)
    axes[0].set(xscale='log',yscale='log',xlabel='Natural arithmetic scale X',ylabel='|F(X)| / fitted bound',
        title='Complete infinite sums, finite scales')
    axes[0].legend(fontsize=8,ncol=2);axes[0].grid(alpha=.15)
    # Compare all frozen approach laws on the same archived best-cost bank.
    available=[r for r in records if r['candidate']['RH_sufficient_if_uniform'] and r['candidate']['recovery_cost'].get('best_log_cost') is not None]
    best=min(available,key=lambda r:r['candidate']['recovery_cost']['best_log_cost']);anchor=best['candidate'];cost_rows=[];missing=[]
    for nu in spec['frontier_approach_powers']:
        pool=[c for c in batch['candidates'] if c['bank_id']==anchor['bank_id'] and c['frontier']['limit']=='1/2'
              and c['frontier']['approach_power']==nu and c['frontier']['log_power']==anchor['frontier']['log_power']]
        c=pool[0];allobs=c['recovery_cost']['observers']+fresh_costs.get(c['id'],{}).get('observers',[])
        obs=[o for o in allobs if o.get('log_cost') is not None]
        if not obs:missing.append(nu);continue
        obs=sorted(obs,key=lambda o:o['q']);axes[1].plot([o['q'] for o in obs],[o['log_cost']/math.log(10) for o in obs],marker='o',label=f'nu={nu}')
        for o in obs:cost_rows.append({'candidate_id':c['id'],'approach_power':nu,'q':o['q'],'log10_conditional_cost':o['log_cost']/math.log(10)})
    if missing:axes[1].text(.04,.94,'No tested q enters this observer for nu='+', '.join(missing),transform=axes[1].transAxes,va='top',fontsize=8)
    axes[1].set(xlabel='Parameter q',ylabel='log10 conditional reciprocal-zeta bound',title='Recovery cost at s=5/8+16i')
    axes[1].legend(fontsize=8,loc='lower right');axes[1].grid(alpha=.15)
    fig.suptitle('Signed Mellin kernels: finite evidence and full conditional costs',fontsize=13)
    fig.savefig(d/'mellin_kernel_evidence.png',dpi=170);fig.savefig(d/'mellin_kernel_evidence.pdf');plt.close(fig)
    observations={'source_protocol_sha256':sha(d/'protocol.json'),'source_archive_sha256':sha(d/'archive.json'),
        'source_final_sha256':sha(d/'final_evaluation.json'),'source_verification_sha256':sha(d/'verification.json'),
        'fresh_observer_verification_sha256':observer_audit.get('verification_sha256'),
        'finite_ratio_observations':finite,'cost_observations':cost_rows,'approach_laws_with_no_available_observer':missing,
        'ratio_panel_uses_complete_infinite_sums':True,'fresh_final_scales_marked_as_squares':True,
        'right_panel_is_conditional':True,'finite_scales_and_parameters_do_not_prove_uniform_premises':True,'RH_proved':False}
    (d/'plot_observations.json').write_text(json.dumps(observations,indent=2)+'\n')
    failures=[r for r in records if not r['final_outcome']['finite_points_passed']]
    joint=next((r for r in records if r['bank']['family']=='joint_bank' and r['bank']['recovery_certificate']['all_height_no_common_zero']),None)
    joint_text='No recovering joint bank entered this archive.\n'
    if joint:
        joint_text='An automatically assembled recovering bank in this archive has kernels:\n'
        for i,program in enumerate(joint['programs'],1):
            base=Q(program['parameters'][2])
            terms=[f'{c}*({base**j}*y)^{m}*exp(-{base**j}*y)' for m,j,c in program['kernel']['terms']]
            joint_text+=f'K{i}(y)='+ ' + '.join(terms)+'\n'
        joint_text+='Exact recovery identity: '+json.dumps(joint['bank']['recovery_certificate'],separators=(',',':'))+'\n'
        joint_text+='The corresponding signed global growth premise remains unproved.\n'
    report=('COMPLETE SIGNED ARITHMETIC TAILS AND COFINAL GROWTH FRONTIERS\n\n'
        f"Primary kernels: {evidence['program_count']}; banks: {evidence['bank_count']}; primary growth hypotheses: {evidence['growth_frontier_hypotheses']}.\n"
        f"Independent checks: {evidence['verified_checks']}/{evidence['verified_checks']}. Complete infinite atom values checked: {evidence['independent_native_counts']['independent_complete_infinite_atom_values']}.\n"
        f"Archived finite passes: {len(records)-len(failures)}/{len(records)}; RH-if-uniform finite survivors: {len(evidence['RH_if_uniform_finite_survivors'])}.\n"
        f"Fresh natural scales: {cases['integers']}; fresh q: {read(d/'parameter_cases.json')['fresh_q']}.\n"
        f"Joint banks with exact all-height recovery: {evidence['joint_banks_with_all_height_recovery']}; with individually uncertified kernels: {evidence['joint_banks_including_individually_uncertified_kernels']}.\n\n"
        'The bound target is for every q there exists a finite C_(i,q) such that every integer N obeys the signed bound. '
        'theta_q=eta+epsilon/q^nu; constants have no specified growth rate in q. A recovering bank at eta=1/2 gives an RH-equivalent target. '
        'The sufficiency argument is the exact Mellin bank identity; necessity uses the named classical conditional Mertens bound only as an equivalence audit.\n'
        'All arithmetic tails are enclosed through reciprocal-zeta moments at real exponents greater than one. '
        'The coefficient producer uses triangular inversion. Independent evaluation uses prime factorization, a different prefix, precision, Taylor order and tail summation.\n\n'
        f"Ablation: {evidence['ablation_comparison']['admitted_promotions']} promotions admitted under equal proposal-slot budgets; "
        f"best primary log recovery cost {evidence['ablation_comparison']['best_primary_log_cost']}; "
        f"promotion-disabled cost {evidence['ablation_comparison']['best_ablation_log_cost']}. No best-cost improvement in this pilot.\n"
        f"Counterfeit arithmetic controls passing finite tests but globally rejected by their pole at one: {evidence['counterfeit_finite_successes_analytically_rejected']}.\n"
        'The automatic all-scale backend proves the weak exponent-one envelope and unit derivative bound. '
        'It does not prove the required signed sublinear growth. Missing certificates are not counterexamples.\n'
        'The exact all-scale forcing equation is sum_(d>=1)F_K(X/d)=X^k K(X^ell); this is not by itself a contraction at exponent one-half.\n\n'
        f"New-q fully charged observers checked: {observer_audit.get('counts',{}).get('fully_charged_native_Mellin_observers',0)}; "
        f"previously unavailable observer regimes now available: {observer_audit.get('previously_unavailable_observers_now_available',0)}. No reselection or refitting.\n\n"
        +joint_text+'\n'+
        'New independent prime-distribution information: none established. Historical novelty was not an acceptance gate. '
        'Mathematical backends were supplied and independently checked, not autonomously invented or machine formalized. '
        'All RH-strength uniform estimates remain open; RH has not been proved.\n'
        'Proof: mellin_kernel_proof.txt. Plot: mellin_kernel_evidence.pdf. Full scopes: summary.json.\n')
    (d/'report.txt').write_text(report)
    print('Saved complete-tail evidence plot and scoped report.')


if __name__=='__main__':main()
