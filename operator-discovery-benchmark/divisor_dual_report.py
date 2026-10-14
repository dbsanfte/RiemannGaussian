"""Strict report for detector-selected full-defect leads and a frozen proof queue."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    d=Path(directory).resolve();spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');queue=read(d/'proof_queue.json');seal=read(d/'seal.json');cases=read(d/'final_cases.json');final=read(d/'final_evaluation.json');v=read(d/'verification.json')
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    assert digest(spec)==seal['protocol_sha256']==batch['protocol_sha256']==queue['protocol_sha256']==v['protocol_sha256'] and seal['selection_closed'] and not seal['final_cases_exist'] and arc['selection_closed'] and not arc['final_data_used']
    assert all(batch['access_denials'].values()) and cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json') and final['cases_sha256']==digest(cases)
    assert v['all_passed'] and all(v['checks'].values()) and v['checker_sha256']==sha(BASE/'check_divisor_dual.py') and v['final_sha256']==sha(d/'final_evaluation.json') and v['proof_queue_sha256']==sha(d/'proof_queue.json') and v['replay_sha256']==seal['files'] and not v['mathematical_audit_imports_production_code']
    from critical_defect_report import summary as parent
    parent(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/n)==h
    for f in spec['retained_failed_runs_are_development']:
        p=Path(f['run_directory']);assert sha(p/'failure.json')==f['failure_sha256']
        for n,h in f['files_sha256'].items():assert sha(p/n)==h
        for n,h in read(p/'protocol.json')['code_sha256'].items():
            if n in spec['this_stage_source_files']:assert sha(p/'frozen_source'/n)==h
        assert not set(cases['scales'])&set(f['excluded_final_scales'])
    assert spec['uniform_RH_sufficient_signed_controls_verified']==arc['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==v['uniform_RH_sufficient_signed_controls_verified']==[] and not final['RH_proved'] and not final['global_critical_matrix_PSD_proved']
    evaluations=final['matrix_certificates'];selected={r['program_id'] for r in arc['matrix_leads']};assert selected=={r['program_id'] for r in queue['queue']} and not queue['final_data_used_for_selection']
    return {'status':'verified_finite_divisor_dual_candidates_frozen_for_separate_analytical_review','run_directory':str(d),'program_count':len(batch['programs']),
        'anonymous_kernel_exact_admission':batch['kernel_exact_admission'],'learned_zero_forcing_masks':[r['mask'] for r in batch['promotions']],
        'adaptive_mask_promotion_exercised':bool(batch['promotions']),'equal_slot_ablation_preserved':True,'ablation_comparison':arc['ablation_comparison'],
        'proof_queue_candidates':len(queue['queue']),'proof_queue_frozen_before_final':True,'analytical_results_must_not_change_frozen_candidates':True,
        'fully_charged_whole_signed_defect_retained':True,'actual_prime_inverse_arithmetic_independently_checked':True,'fresh_scales':cases['scales'],'fresh_levels':cases['levels'],
        'fresh_matrix_cases':len(evaluations),'fresh_positive_matrices':sum(r['certificate'].get('finite_matrix_PSD',False) for r in evaluations),
        'fresh_negative_matrix_directions':sum(bool(r['certificate'].get('counterexample')) for r in evaluations),'fresh_missing_certificates':sum(r['certificate'].get('missing',False) for r in evaluations),
        'global_generic_energy_power':'3','global_critical_matrix_PSD_proved':False,'global_full_defect_bound_proved':False,'negative_matrix_witnesses_are_not_RH_counterexamples':True,
        'finite_dual_can_reexpress_existing_finite_signed_bound':True,'new_independent_prime_distribution_estimate':False,'arbitrary_rational_exponents_have_semantics':True,'semantic_denominator_cap':False,
        'guided_features_and_certificate_methods_supplied':True,'negative_controls':final['controls']['negative_controls'],'independent_native_counts':v['counts'],'verified_checks':len(v['checks']),
        'verification_sha256':sha(d/'verification.json'),'proof_queue_sha256':sha(d/'proof_queue.json'),'mathematical_audit_imports_production_code':False,'machine_formalized':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    p=BASE/'divisor-dual-results/latest.json';return summary(read(p)['run_directory']) if p.exists() else {'status':'not_run'}


def text_report(s):
    return '\n'.join(['Detector-to-proof queue: exact full-defect divisor-Gram candidates',
        f"Frozen programs: {s['program_count']}; selected exact proof-queue templates: {s['proof_queue_candidates']}.",
        f"Anonymous floor/lcm kernel recovery admitted: {s['anonymous_kernel_exact_admission']}; zero-forcing mask promotions: {s['learned_zero_forcing_masks']}; equal-slot random-mask ablation retained.",
        'Every lead keeps the full signed energy defect. The cost is 4*X*D+Y*w(1); the unit-row forcing term is never omitted.',
        'The proof queue is sealed before fresh evaluation. Separate analytical attempts must use the exact selected formulas and record proved, disproved or unresolved dispositions without editing those candidates.',
        f"Fresh X: {s['fresh_scales']}; q: {s['fresh_levels']}; positive matrices: {s['fresh_positive_matrices']}/{s['fresh_matrix_cases']}; exact negative directions: {s['fresh_negative_matrix_directions']}; missing certificates: {s['fresh_missing_certificates']}.",
        'Finite matrix positivity is independently proved by exact integer Sylvester minors. Negative quadratic directions reject matrix candidates, not RH.',
        'The nonunit divisor Gram annihilates the complete actual Mobius inverse at every finite cutoff. This identity alone supplies no critical bound: positivity still requires control of the signed defect on its nullspace.',
        'The unconditional q=1 row-norm calibration proves energy power THREE. A cofinal-q all-scale critical comparison remains unproved.',
        'Fixed-prime row constraints admit counterfeit bounded sequences with a positive linear mean and cubic energy. Generic divisor inverses need not have the Mobius amplitude bound.',
        f"Independent audit groups: {s['verified_checks']}; exact counts: {s['independent_native_counts']}.",
        'Features and certificate methods were supplied; no new independent prime-distribution estimate has been established.',
        'Uniform RH-sufficient signed controls verified: 0. RH proved: false.',''])
