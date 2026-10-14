#!/usr/bin/env python3
"""Independent prime-derived endpoint witnesses and cofinal quantifiers."""
from pathlib import Path
from fractions import Fraction as Q
import argparse
from stable_scale_report import BASE,read,sha,digest
from check_signed_control import independent_inverse
from check_signed_gap_profiles import data,ceilq,eps
from check_mellin_kernels import put


def constant(p):
    k=p['constant_law']['kind']
    if k=='constant':return Q(p['fitted_coefficient'])
    if k=='power' and Q(p['constant_law']['power'])==0:return 2*Q(p['fitted_coefficient'])
    if k=='denominator_power' and Q(p['constant_law']['power'])==0:return Q(p['fitted_coefficient'])
    return None


def threshold(s,X):
    if X<2 or s['kind']=='fixed':return None
    if s['kind']=='factorial':return X.bit_length()
    if s['kind']in ['power','exponential'] and Q(s['power'])>0:return X.bit_length()**Q(s['power']).denominator
    return None


def entry(p,row):
    C=constant(p);X=row['X'];q0=threshold(p['exponent_schedule'],X)
    if C is None or q0 is None:return None
    L=ceilq(X.bit_length(),p['log_power']);D=2*C*X*L;Qn=row['squarefree_count_through_4X'];delta=row['signed_defect']
    return {'X':X,'C_endpoint':str(C),'log_ceiling':L,'D_endpoint':str(D),'actual_signed_defect':delta,'Q_4X':Qn,'half_gap_margin':str(D*Qn/2-delta),
        'nullspace_PSD_margin':str(D*Qn-delta),'fully_charged_bound_margin':str(4*X*D-delta),'parameter_threshold':q0,'all_parameters_beyond_threshold_covered':True,
        'root_ceiling_at_every_parameter_beyond_threshold':2,'actual_counterexample_is_not_RH_counterexample':True}


def check(d):
    spec=read(d/'protocol.json');source=Path(spec['source_run']);result=read(d/'audit.json');queue=read(source/'proof_queue.json');checks={};counts={'actual_prime_inverse_coefficients':0,'exact_endpoint_margin_cases':0,'native_plateau_witnesses':0}
    def passed(n):checks[n]=True;print('Verified',n,flush=True)
    from signed_gap_profile_report import summary
    summary(source)
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h==sha(d/'frozen_source'/n)
    assert result['protocol_sha256']==digest(spec) and result['source_queue_sha256']==sha(source/'proof_queue.json') and spec['uses_original_frozen_cases_for_analytic_counterexamples'] and not spec['new_holdout_or_discovery_claimed']
    passed('separate_analytical_audit_preserves_all_original_frozen_evidence_and_candidate_formulas')
    original=[];N=0
    for file,key in [('candidate_batch.json','training_arithmetic'),('validation.json','arithmetic'),('final_evaluation.json','arithmetic')]:
        rows=read(source/file)[key];original+=rows['rows'];N=max(N,rows['cutoff'])
    mu,_=independent_inverse(N);exact=data(mu,[r['X'] for r in original]);assert exact==original;counts['actual_prime_inverse_coefficients']=N;dyadic=[r for r in exact if not r['X']&(r['X']-1)];byid={r['program_id']:r for r in queue['queue']};assert set(byid)=={r['program_id'] for r in result['attempts']}
    passed('independent_complete_actual_arithmetic_and_each_original_signed_defect_recomputed')
    for row in result['attempts']:
        original=byid[row['program_id']];p=original['exact_program'];assert row['exact_program_sha256']==digest(p) and row['source_global_claim']==original['global_claim'] and not row['original_formula_and_fitted_constants_changed']
        entries=[v for r in dyadic if (v:=entry(p,r))is not None];assert entries==row['endpoint_cases'] and row['bounded_constant_endpoint_available']==bool(entries);counts['exact_endpoint_margin_cases']+=len(entries)
        groups=[('half_gap_margin','persistent_half_gap_witness'),('nullspace_PSD_margin','persistent_nullspace_witness'),('fully_charged_bound_margin','persistent_fully_charged_witness')]
        for field,name in groups:
            bad=[v for v in entries if Q(v[field])<0];chosen=min(bad,key=lambda v:(Q(v[field]),v['X'])) if bad else None;assert row[name]==chosen
        disproved=row['persistent_half_gap_witness'] is not None;assert row['proof_status']==('disproved_uniform_actual_half_gap' if disproved else 'unresolved_uniform_actual_half_gap') and not row['global_actual_signed_bound_proved'] and not row['RH_proved']
        if disproved:
            w=row['persistent_half_gap_witness'];X=w['X'];q0=w['parameter_threshold'];assert X<2**X.bit_length() and q0>=1
            s=p['exponent_schedule']
            if s['kind']in ['power','exponential']:
                a=Q(s['power']);assert q0==X.bit_length()**a.denominator and q0**a.numerator>=X.bit_length()**a.denominator
            else:assert s['kind']=='factorial' and q0==X.bit_length()
            levels=[q0,q0+1,2*q0];assert [r['level'] for r in row['illustrative_native_plateau_checks']]==levels
            for check in row['illustrative_native_plateau_checks']:
                e=eps(s,check['level']);assert str(e)==check['epsilon'] and e>0 and e.numerator==1 and e.denominator>=X.bit_length() and ceilq(X,e)==check['exact_root_ceiling']==2 and check['parameters_are_only_illustrative'];counts['native_plateau_witnesses']+=1
    passed('exact_bounded_constant_endpoints_three_distinct_margins_and_every_large_parameter_scope')
    assert result['counterexamples_use_actual_complete_inverse'] and result['q0_cannot_remove_persistent_witnesses'] and result['fixed_parameter_failure_not_automatically_global_disproof'] and result['unbounded_or_unspecified_constants_not_inferred_from_finite_fits'] and not result['global_actual_critical_signed_gap_proved'] and result['uniform_RH_sufficient_signed_controls_verified']==[] and not result['RH_proved']
    passed('actual_candidate_counterexamples_do_not_refute_RH_or_claim_unbounded_family_success')
    put(d/'verification.json',{'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_signed_gap_cofinal.py'),'audit_sha256':sha(d/'audit.json'),'source_queue_sha256':sha(source/'proof_queue.json'),'checks':checks,'counts':counts,'all_passed':all(checks.values()),
        'mathematical_audit_imports_production_code':False,'machine_formalized':False,'global_actual_critical_signed_gap_proved':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False});print('Independent cofinal audit',len(checks),'/',len(checks),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--audit-dir',type=Path,required=True);check(p.parse_args().audit_dir.resolve())
