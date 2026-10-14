#!/usr/bin/env python3
"""Analytical cofinal-root tests of unchanged actual signed-gap candidates."""
import argparse,subprocess,sys
from fractions import Fraction as Q
from pathlib import Path
from stable_scale_search import BASE,read,write,sha,digest
from signed_gap_profile_report import summary
from signed_gap_profile_grammar import ceil_power,epsilon

CODE=['signed_gap_cofinal_audit.py','check_signed_gap_cofinal.py','signed_gap_cofinal_report.py','signed_gap_cofinal_proof.txt','test_signed_gap_cofinal_contracts.py']


def bounded_constant(program):
    c=program['constant_law'];k=c['kind']
    if k=='constant':return Q(program['fitted_coefficient'])
    if k in ['power','denominator_power'] and Q(c['power'])==0:return Q(program['fitted_coefficient'])*(2 if k=='power' else 1)
    return None


def plateau_threshold(schedule,X):
    d0=X.bit_length();k=schedule['kind']
    if X<2 or k=='fixed':return None
    if k in ['power','exponential']:
        a=Q(schedule['power'])
        if a<=0:return None
        return d0**a.denominator
    if k=='factorial':return d0
    return None


def endpoint(program,row):
    X=row['X'];C=bounded_constant(program)
    if C is None or plateau_threshold(program['exponent_schedule'],X)is None:return None
    L=ceil_power(X.bit_length(),Q(program['log_power']));D=2*C*X*L;delta=row['signed_defect'];Qn=row['squarefree_count_through_4X']
    return {'X':X,'C_endpoint':str(C),'log_ceiling':L,'D_endpoint':str(D),'actual_signed_defect':delta,'Q_4X':Qn,
        'half_gap_margin':str(D*Qn/2-delta),'nullspace_PSD_margin':str(D*Qn-delta),'fully_charged_bound_margin':str(4*X*D-delta),
        'parameter_threshold':plateau_threshold(program['exponent_schedule'],X),'all_parameters_beyond_threshold_covered':True,'root_ceiling_at_every_parameter_beyond_threshold':2,
        'actual_counterexample_is_not_RH_counterexample':True}


def audit(source,d):
    source=Path(source).resolve();summary(source);queue=read(source/'proof_queue.json');data=[]
    for name,key in [('candidate_batch.json','training_arithmetic'),('validation.json','arithmetic'),('final_evaluation.json','arithmetic')]:data.extend(read(source/name)[key]['rows'])
    # Dyadic cases alone suffice for the source global claim. Other source
    # scales remain integrity-checked but cannot serve as this RH witness.
    dyadic=[r for r in data if not r['X']&(r['X']-1)];d=Path(d).resolve();d.mkdir(exist_ok=False)
    spec={'source_run':str(source),'source_sha256':{n:sha(source/n) for n in ['protocol.json','seal.json','proof_queue.json','candidate_batch.json','validation.json','final_evaluation.json','verification.json','analytical_review.json','analytical_verification.json']},
        'code_sha256':{n:sha(BASE/n) for n in CODE},'uses_original_frozen_cases_for_analytic_counterexamples':True,'original_candidates_and_fits_unchanged':True,'new_holdout_or_discovery_claimed':False,
        'proof_quantifier':'one fixed dyadic scale fails for every parameter beyond an explicit finite threshold','RH_proved':False};write(d/'protocol.json',spec);(d/'frozen_source').mkdir()
    for n in CODE:(d/'frozen_source'/n).write_bytes((BASE/n).read_bytes())
    attempts=[]
    for row in queue['queue']:
        p=row['exact_program'];entries=[v for r in dyadic if (v:=endpoint(p,r))is not None];half=[v for v in entries if Q(v['half_gap_margin'])<0];null=[v for v in entries if Q(v['nullspace_PSD_margin'])<0];charged=[v for v in entries if Q(v['fully_charged_bound_margin'])<0]
        chosen=min(half,key=lambda v:(Q(v['half_gap_margin']),v['X'])) if half else None
        if chosen:
            threshold=chosen['parameter_threshold'];levels=[threshold,threshold+1,2*threshold];checks=[]
            for q in levels:
                e=epsilon(p['exponent_schedule'],q);root=ceil_power(chosen['X'],e)
                checks.append({'level':q,'epsilon':str(e),'exact_root_ceiling':root,'parameters_are_only_illustrative':True})
        else:checks=[]
        attempts.append({'program_id':row['program_id'],'exact_program_sha256':digest(p),'source_global_claim':row['global_claim'],'proof_status':'disproved_uniform_actual_half_gap' if half else 'unresolved_uniform_actual_half_gap',
            'bounded_constant_endpoint_available':bool(entries),'endpoint_cases':entries,'persistent_half_gap_witness':chosen,'persistent_nullspace_witness':min(null,key=lambda v:Q(v['nullspace_PSD_margin'])) if null else None,
            'persistent_fully_charged_witness':min(charged,key=lambda v:Q(v['fully_charged_bound_margin'])) if charged else None,'illustrative_native_plateau_checks':checks,
            'original_formula_and_fitted_constants_changed':False,'global_actual_signed_bound_proved':False,'RH_proved':False})
    result={'protocol_sha256':digest(spec),'source_queue_sha256':sha(source/'proof_queue.json'),'attempts':attempts,'counterexamples_use_actual_complete_inverse':True,
        'q0_cannot_remove_persistent_witnesses':True,'fixed_parameter_failure_not_automatically_global_disproof':True,'unbounded_or_unspecified_constants_not_inferred_from_finite_fits':True,
        'global_actual_critical_signed_gap_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False};write(d/'audit.json',result)
    subprocess.run([sys.executable,str(BASE/'check_signed_gap_cofinal.py'),'--audit-dir',str(d)],cwd=BASE,check=True)
    from signed_gap_cofinal_report import summary as report,text_report
    s=report(d);write(d/'summary.json',s);(d/'report.txt').write_text(text_report(s));write(BASE/'signed-gap-profile-results/latest-cofinal-audit.json',{'audit_directory':str(d)})


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',type=Path,required=True);p.add_argument('--audit-dir',type=Path,required=True);args=p.parse_args();audit(args.source,args.audit_dir)
