"""Strict signed-gap predictions and separate analytical proof outcomes."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    d=Path(directory).resolve();spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');queue=read(d/'proof_queue.json');seal=read(d/'seal.json');cases=read(d/'final_cases.json');final=read(d/'final_evaluation.json');v=read(d/'verification.json');a=read(d/'analytical_review.json');av=read(d/'analytical_verification.json')
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    assert digest(spec)==seal['protocol_sha256']==batch['protocol_sha256']==queue['protocol_sha256']==v['protocol_sha256']==final['protocol_sha256'] and all(batch['access_denials'].values()) and seal['selection_closed'] and not seal['final_cases_exist'] and not arc['final_data_used'] and cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json') and final['cases_sha256']==digest(cases)
    assert v['all_passed'] and all(v['checks'].values()) and v['checker_sha256']==sha(BASE/'check_signed_gap_profiles.py') and v['final_sha256']==sha(d/'final_evaluation.json') and v['queue_sha256']==sha(d/'proof_queue.json') and v['replay_sha256']==seal['files'] and not v['mathematical_audit_imports_production_code']
    assert av['all_passed'] and all(av['checks'].values()) and av['checker_sha256']==sha(BASE/'check_signed_gap_profile_analytic.py') and av['review_sha256']==sha(d/'analytical_review.json') and av['queue_sha256']==sha(d/'proof_queue.json') and not av['mathematical_audit_imports_production_code'] and a['source_queue_sha256']==sha(d/'proof_queue.json') and a['source_final_sha256']==sha(d/'final_evaluation.json') and a['source_detector_verification_sha256']==sha(d/'verification.json')
    from divisor_dual_report import summary as parent
    from divisor_dual_analytic_report import summary as analytic
    parent(spec['source_run']);analytic(spec['source_analytical_review'])
    for n,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/n)==h
    for n,h in spec['source_analytical_sha256'].items():assert sha(Path(spec['source_analytical_review'])/n)==h
    for f in spec['retained_failed_runs_are_development']:
        p=Path(f['run_directory']);assert sha(p/'failure.json')==f['failure_sha256']
        for n,h in f['files_sha256'].items():assert sha(p/n)==h
        for n,h in read(p/'protocol.json')['code_sha256'].items():
            if n in spec['this_stage_source_files']:assert sha(p/'frozen_source'/n)==h
        assert not set(cases['scales'])&set(f['excluded_final_scales'])
    assert spec['uniform_RH_sufficient_signed_controls_verified']==arc['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==a['uniform_RH_sufficient_signed_controls_verified']==av['uniform_RH_sufficient_signed_controls_verified']==[] and not final['RH_proved'] and not a['all_scale_critical_signed_bound_proved']
    actual=[r for p in final['program_results'] for r in p['observations']];fake=[r for p in final['program_results'] for r in p['counterfeit_observations']];new=[r for r in actual if r['level']in cases['new_levels']];pos=sum(r['signed_defect']>0 for r in final['arithmetic']['rows']);missing=sum(r['parameters']['missing'] for r in actual)
    return {'status':'verified_independent_constant_profiles_actual_signed_gaps_and_separate_analytical_attempts','run_directory':str(d),'program_count':len(batch['programs']),'exponent_schedule_count':len(spec['exponent_schedules']),'constant_law_count':len(spec['constant_laws']),'log_powers':spec['log_powers'],
        'existential_per_level_constants_supported':True,'unseen_level_constants_are_missing_not_fitted_predictions':True,'exponent_and_constant_growth_decoupled':True,'proof_queue_candidates':len(queue['queue']),
        'fresh_scales':cases['scales'],'fresh_dyadic_scales':cases['dyadic_scales'],'fresh_new_levels':cases['new_levels'],'fresh_actual_coefficient_cutoff':final['arithmetic']['cutoff'],'fresh_positive_actual_defects':pos,
        'fresh_actual_observations':len(actual),'fresh_half_gap_passes':sum(r.get('finite_half_gap_pass',False) for r in actual),'fresh_missing_constants':missing,'fresh_new_level_observations':len(new),'fresh_new_level_passes':sum(r.get('finite_half_gap_pass',False) for r in new),
        'delayed_counterfeit_half_gap_failures':sum(not r['parameters']['missing'] and not r['finite_half_gap_pass'] for r in fake),'counterfeit_shared_prefix_through':final['counterfeit_arithmetic']['shared_actual_prefix_through'],
        'anonymous_minimum_bound_terms':a['minimum_lead']['terms'],'anonymous_sparse_fits_retained':len(batch['minimum_inference']['retained_fits']),'global_binary_prefix_minimum_bound_proved':a['minimum_proof_certificate']['global_binary_prefix_minimum_bound_proved'],
        'quantitative_tail_obstruction_has_no_position_assumption':True,'critical_tail_omission_power_ceiling':'1/2','new_independent_prime_distribution_estimate':False,
        'unresolved_global_actual_signed_gap_candidates':len(a['candidate_attempts']),'conditional_simplicity_restricting_candidates':sum(r['conditional_constant_growth_consequences']['would_force_simple_critical_zeros_if_global_bound_proved'] for r in a['candidate_attempts']),
        'positive_r_can_still_impose_critical_zero_simplicity':True,'critical_multiplicity_scope_is_conditional':True,'global_generic_energy_power':'3','global_actual_critical_signed_gap_proved':False,
        'verified_checks':len(v['checks']),'analytical_verified_checks':len(av['checks']),'independent_native_counts':v['counts'],'independent_analytical_counts':av['counts'],'verification_sha256':sha(d/'verification.json'),'analytical_verification_sha256':sha(d/'analytical_verification.json'),
        'guided_target_features_and_proof_methods_supplied':True,'semantic_denominator_cap':False,'machine_formalized':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    p=BASE/'signed-gap-profile-results/latest.json';return summary(read(p)['run_directory']) if p.exists() else {'status':'not_run'}


def text_report(s):
    return '\n'.join(['Signed arithmetic gap: exponent schedules and constant laws are independent',
        f"Frozen profiles: {s['program_count']}; exponent schedules: {s['exponent_schedule_count']}; constant laws: {s['constant_law_count']}; logarithmic powers: {s['log_powers']}; proof queue: {s['proof_queue_candidates']}.",
        'Target: Delta(X)<=D(X,q)*Q(4X)/2 for actual mu, at every dyadic scale. Only the training constants are fitted; new constants in the existential per-level family are unknown.',
        f"Fresh scales: {s['fresh_scales']}; new q: {s['fresh_new_levels']}; independently checked actual coefficient cutoff: {s['fresh_actual_coefficient_cutoff']}; positive actual defects: {s['fresh_positive_actual_defects']}.",
        f"Fresh finite half-gap passes: {s['fresh_half_gap_passes']}/{s['fresh_actual_observations']}; missing constants: {s['fresh_missing_constants']}; new-level passes: {s['fresh_new_level_passes']}/{s['fresh_new_level_observations']}.",
        f"A delayed positive tail shares every development coefficient through {s['counterfeit_shared_prefix_through']}. Its cubic defect produces {s['delayed_counterfeit_half_gap_failures']} finite false-model failures and refutes global extrapolation to arbitrary bounded sequences.",
        f"Anonymous minimum relation: {s['anonymous_minimum_bound_terms']}; generic symbolic difference and exchange proof admitted: {s['global_binary_prefix_minimum_bound_proved']}.",
        'The learned global combinatorial estimate gives the necessary PSD condition P(J)<=D*J for J omitted tail rows, irrespective of their positions or the Gram weight. Cofinal critical diagonal growth therefore cannot omit substantially more than square-root many tail rows.',
        f"Analytical signed-gap attempts unresolved: {s['unresolved_global_actual_signed_gap_candidates']}; templates that would additionally force simple critical zeros: {s['conditional_simplicity_restricting_candidates']}.",
        'For epsilon=1/q and no log loss, even positive polynomial constant powers r<1 force zero simplicity if proved. Unbounded constants alone do not remove this restriction. The unrestricted cofinal criterion remains the primary RH target.',
        f"Independent detector audit groups: {s['verified_checks']}; analytical audit groups: {s['analytical_verified_checks']}; exact arithmetic counts: {s['independent_native_counts']}.",
        'The universal binary-prefix estimate is proved; the actual all-scale critical signed inequality and any new prime-distribution estimate remain unproved. Ordinary generic calibration has energy power three.',
        'Uniform RH-sufficient signed controls verified: 0. RH proved: false.',''])
