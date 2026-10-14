"""Strict scope for proved energy components and the unresolved RH inequality."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    d=Path(directory).resolve();spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');seal=read(d/'seal.json');cases=read(d/'final_cases.json');final=read(d/'final_evaluation.json');v=read(d/'verification.json')
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist'] and arc['selection_closed'] and not arc['final_data_used']
    assert cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json') and final['cases_sha256']==digest(cases) and all(batch['access_denials'].values())
    assert v['all_passed'] and all(v['checks'].values()) and v['checker_sha256']==sha(BASE/'check_critical_defects.py') and v['final_sha256']==sha(d/'final_evaluation.json') and v['protocol_sha256']==digest(spec) and v['replay_sha256']==seal['files']
    assert not v['mathematical_audit_imports_production_code'] and not final['global_full_signed_defect_proved'] and not v['full_signed_defect_bound_proved'] and not final['RH_proved']
    from branch_center_report import summary as parent
    parent(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/n)==h
    for f in spec['retained_failed_runs_are_development']:
        p=Path(f['run_directory']);assert sha(p/'failure.json')==f['failure_sha256']
        for n,h in f['files_sha256'].items():assert sha(p/n)==h
        for n,h in read(p/'protocol.json')['code_sha256'].items():
            if n in spec['this_stage_source_files']:assert sha(p/'frozen_source'/n)==h
        assert not set(cases['scales'])&set(f['excluded_final_scales'])
    assert spec['uniform_RH_sufficient_signed_controls_verified']==arc['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==v['uniform_RH_sufficient_signed_controls_verified']==[]
    selected=next(p for p in batch['candidates'] if p['id']==arc['selected_component_candidate_id'])
    return {'status':'verified_critical_energy_defect_components_dense_signed_residual_unproved','run_directory':str(d),
        'RH_target':spec['target'],'cofinal_positive_epsilon_recovery_proved':True,'all_heights_and_offcritical_multiplicities_covered':True,'critical_zero_simplicity_required':False,
        'target_actual_mertens_recovering_calibration':True,'actual_mobius_arithmetic_retained':True,'ordinary_zeta_erased':False,
        'uniform_diagonal_defect_power':'3/2','uniform_primitive_common_factor_component_proved':True,'cutoff_program_count':len(batch['candidates']),
        'selected_cutoff_power':arc['selected_cutoff_power'],'selected_component_power':selected['certificate']['component_power'],'selected_component_log_loss':'2','same_cutoff_in_both_scales_required':True,
        'dense_signed_residual_explicitly_retained':True,'full_defect_proof_status':arc['full_defect_proof_status'],'full_defect_bound_proved':False,'full_absolute_envelope_power':'3',
        'fresh_scales':cases['scales'],'archived_finite_residual_estimates':len(final['residual_estimate_evaluations']),'fresh_finite_residual_passes':sum(r['finite_pass'] for r in final['residual_estimate_evaluations']),
        'controlled_projection_false_full_defect_controls':len(final['positive_coefficient_controls']),'delayed_counterfeit_controls':len(final['delayed_tail_controls']),
        'negative_controls':final['negative_controls'],'new_independent_prime_distribution_estimate':False,'arbitrary_rational_exponents_have_semantics':True,'semantic_denominator_cap':False,
        'guided_mathematical_audit_not_anonymous_operator_invention':True,'adaptive_promotion_claimed':False,'independent_native_counts':v['counts'],'verified_checks':len(v['checks']),
        'verification_sha256':sha(d/'verification.json'),'mathematical_audit_imports_production_code':False,'machine_formalized':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    p=BASE/'critical-defect-results/latest.json'
    return summary(read(p)['run_directory']) if p.exists() else {'status':'not_run'}


def text_report(s):
    return '\n'.join(['Critical signed energy defect: proved components, unresolved dense remainder',
        'Target: '+s['RH_target'],
        'Cofinal positive epsilons suffice for RH with the exact ordinary-zeta identity. Constants may depend on epsilon, never on scale. A single fixed critical recurrence for unfiltered M would additionally imply simple critical zeros; that extra claim is not assumed.',
        'The full diagonal defect is bounded at EVERY real scale by C*X^(3/2), using elementary squarefree density and cancellation of its leading X^2 term.',
        f"Rational cutoff programs: {s['cutoff_program_count']}; automatically selected primitive cutoff B=floor(X^({s['selected_cutoff_power']})).",
        f"Common-factor pairs with max(n,m)/gcd(n,m)<=B have a proved defect bound C*X^(3/2)*B^(3/2)*(1+log B)^2. The selected component has power {s['selected_component_power']} and logarithmic loss two. The SAME B is used at both scales.",
        'Every pair outside that projection remains in an exact dense signed residual. Its needed uniform upper bound is UNPROVED. The full absolute pair envelope still has power THREE.',
        f"Fresh dyadic scales: {s['fresh_scales']}; archived finite residual fits: {s['archived_finite_residual_estimates']}; fresh finite passes: {s['fresh_finite_residual_passes']}.",
        'A positive-coefficient control has a bounded sparse projection but full signed defect (28*X^3-X)/3. A delayed positive tail agrees with every development coefficient and still has eventual cubic growth. Neither is actual prime arithmetic.',
        f"Independent audit groups: {s['verified_checks']}; counts: {s['independent_native_counts']}.",
        'The common-factor construction and proof methods were supplied. This is a guided mathematical decomposition audit, not anonymous invention, historical novelty, a new prime-distribution estimate or an RH proof.',
        'Uniform RH-sufficient signed controls verified: 0. RH proved: false.',''])
