"""Strict loader for correctly centered fractional signed arithmetic families."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    d=Path(directory).resolve();spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');seal=read(d/'seal.json');cases=read(d/'final_cases.json');final=read(d/'final_evaluation.json');v=read(d/'verification.json')
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist'] and cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json')
    assert cases['x_generated_after_constants'] and cases['calibration_sha256']==sha(d/'final_constants.json') and final['cases_sha256']==digest(cases)
    assert arc['selection_closed'] and not arc['final_data_used'] and v['all_passed'] and all(v['checks'].values())
    assert v['checker_sha256']==sha(BASE/'check_branch_centers.py') and v['final_sha256']==sha(d/'final_evaluation.json') and v['replay_sha256']==seal['files'] and v['protocol_sha256']==digest(spec) and not v['mathematical_audit_imports_production_code']
    from divisor_preconditioner_report import summary as parent
    parent(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/n)==h
    for failed in spec['retained_failed_runs_are_development']:
        p=Path(failed['run_directory']);assert sha(p/'failure.json')==failed['failure_sha256']
        for n,h in failed['files_sha256'].items():assert sha(p/n)==h
        for n,h in read(p/'protocol.json')['code_sha256'].items():
            if n in spec['this_stage_source_files']:assert sha(p/'frozen_source'/n)==h
    assert spec['uniform_RH_sufficient_signed_controls_verified']==v['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[] and not final['RH_proved']
    assert not spec['semantic_denominator_cap'] and not spec['new_prime_distribution_estimate_imported'] and not spec['historical_priority_is_acceptance_gate']
    programs=batch['programs'];critical=[r for r in final['estimate_evaluations'] if r['RH_if_uniform'] and r['finite_pass']];promids={r['child_id'] for r in batch['promotions']};groups={p['id']:p for p in programs}
    return {'status':'verified_complete_fractional_centers_and_cofinal_signed_parameter_recovery','run_directory':str(d),'base_roots':spec['base_roots'],'evaluated_root_pool':spec['evaluation_root_pool'],
        'all_rational_roots_in_open_unit_interval_supported':True,'semantic_denominator_cap':False,'program_count':len(programs),'anonymous_learned_combinations':sum(r['weights'] is not None for r in batch['anonymous_inferences']),
        'parameter_moment_promotions':len(batch['promotions']),'nonzero_cofinal_recovery_certificates':sum(p['recovery_certificate']['admitted'] for p in programs),
        'zero_sum_weight_recovering_families':sum(p['recovery_certificate'].get('sum_weights_zero',False) for p in programs),'maximum_first_nonzero_moment_order':max(p['recovery_certificate'].get('first_nonzero_moment_order',0) for p in programs),
        'complete_fractional_branch_center_proved':True,'entire_exponent_parameter_recovery_proved':True,'all_ordinary_heights_and_multiplicities_covered':True,
        'actual_mobius_arithmetic_retained':True,'ordinary_zeta_erased':False,'all_real_scale_weak_bounds_proved':True,'verified_ordinary_power':'1','verified_log_loss':'1','RH_strength':False,
        'growth_hypotheses':len(read(d/'validation.json')['estimates']),'archived_estimates':len(arc['estimates']),'fresh_RH_if_uniform_finite_passes':len(critical),
        'fresh_RH_if_uniform_programs':len({r['program_id'] for r in critical}),'finite_critical_promotion_passes':sum(r['program_id'] in promids for r in critical),
        'fresh_finite_critical_estimate_records':critical,'ablation_comparison':arc['ablation_comparison'],'final_levels':cases['levels'],'final_scales':cases['integers'],
        'leading_only_branch_obstructions':len(final['leading_only_controls']),'negative_controls':final['type_controls'],'new_independent_prime_distribution_estimate':False,
        'normalization_full_center_and_interpolation_costs_charged':True,'independent_native_counts':v['counts'],'verified_checks':len(v['checks']),'verification_sha256':sha(d/'verification.json'),
        'mathematical_audit_imports_production_code':False,'machine_formalized':False,'not_autonomous_proof_invention':True,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    p=BASE/'branch-center-results/latest.json'
    return summary(read(p)['run_directory']) if p.exists() else {'status':'not_run'}


def text_report(s):
    lines=['Complete fractional centers and signed cofinal parameter families',
        f"Base roots: {s['base_roots']}; evaluated pool: {s['evaluated_root_pool']}. All rational roots in (0,1) have semantics without a denominator cap.",
        f"Programs: {s['program_count']}; anonymous learned combinations: {s['anonymous_learned_combinations']}; parameter-moment promotions: {s['parameter_moment_promotions']}.",
        f"All-height conditional recovery certificates: {s['nonzero_cofinal_recovery_certificates']}, including {s['zero_sum_weight_recovering_families']} zero-sum families; maximum initial moment order {s['maximum_first_nonzero_moment_order']}.",
        'The full fractional branch at s=1 is centered by a real-cut integral. Actual Mobius coefficients and possible ordinary nonreal zero poles remain. The exponent parameter is entire at fixed nonreal s.',
        'A cofinal critical signed estimate would imply RH, including for finite signed parameter filters with zero small-parameter limit. Eventual parameter-moment dominance and the actual zeta pole at one prove recovery.',
        'True all-real-scale bounds: ordinary power 1, logarithmic loss 1, free parameter-level constants. No RH-strength signed premise has been proved.',
        f"Growth hypotheses: {s['growth_hypotheses']}; archived estimates: {s['archived_estimates']}; fresh finite critical passes: {s['fresh_RH_if_uniform_finite_passes']} across {s['fresh_RH_if_uniform_programs']} programs.",
        f"Fresh levels: {s['final_levels']}; fresh ordinary scales: {s['final_scales']}. New-level constants were frozen before those scales were generated.",
        f"Incomplete leading-only centers rejected by nonzero branches: {s['leading_only_branch_obstructions']}. A finite fit cannot override that analytic obstruction.",
        'All normalization, whole continued numerators, full centers, interpolation and Mellin-gap costs are charged. The independent observer uses fractional integrals of whole zeta, not the producer Euler-Maclaurin code.',
        f"Independent audit groups: {s['verified_checks']}. Exact isolated learning, promotion and equal-slot ablation replay passed.",
        'Features, the branch center, moment promotion and analytic proof methods were supplied. No historical novelty, autonomous proof invention, new independent prime-distribution theorem or RH proof is claimed.',
        'Uniform RH-sufficient signed controls verified: 0. RH proved: false.','']
    for r in s['ablation_comparison']:lines.append(f"{r['mode']}: finite validated programs={r['finite_validated_programs']}, best charged conditional observer cost={r['best_finite_validated_charged_cost']}.")
    return '\n'.join(lines)+'\n'
