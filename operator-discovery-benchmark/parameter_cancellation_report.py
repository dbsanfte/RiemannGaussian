"""Strict read-only scope for signed parameter limits and uniform envelopes."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    d=Path(directory).resolve();spec=read(d/'protocol.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');seal=read(d/'seal.json');cases=read(d/'final_cases.json');final=read(d/'final_evaluation.json');v=read(d/'verification.json')
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist'] and cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json')
    assert batch['candidate_batch_frozen_before_validation'] and not batch['final_cases_used'] and all(batch['access_denials'].values())
    assert arc['selection_closed'] and not arc['final_data_used'] and final['cases_sha256']==digest(cases) and final['protocol_sha256']==digest(spec)
    assert v['all_passed'] and all(v['checks'].values()) and v['protocol_sha256']==digest(spec) and v['checker_sha256']==sha(BASE/'check_parameter_cancellation.py') and v['final_sha256']==sha(d/'final_evaluation.json')
    assert v['replay_sha256']==seal['files'] and not v['mathematical_audit_imports_production_code']
    from branch_center_report import summary as parent
    parent(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(Path(spec['source_run'])/n)==h
    for failed in spec['retained_failed_runs_are_development']:
        p=Path(failed['run_directory']);assert sha(p/'failure.json')==failed['failure_sha256']
        for n,h in failed['files_sha256'].items():assert sha(p/n)==h
        for n,h in read(p/'protocol.json')['code_sha256'].items():
            if n in spec['this_stage_source_files']:assert sha(p/'frozen_source'/n)==h
        assert not set(cases['integers'])&set(failed['excluded_final_scales'])
    assert spec['uniform_RH_sufficient_signed_controls_verified']==v['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==arc['uniform_RH_sufficient_signed_controls_verified']==[] and not final['RH_proved']
    assert not spec['semantic_denominator_cap'] and not spec['new_prime_distribution_estimate_imported'] and not spec['historical_priority_is_acceptance_gate']
    critical=final['critical_estimate_evaluations'];radii={r['id']:r for r in batch['radius_programs']};prom=batch['limit_promotions'];orders=[r['family_certificate']['moment'] for r in batch['programs']]
    return {'status':'verified_uniform_parameter_cancellation_and_behavioral_jet_limit_search','run_directory':str(d),
        'program_count':len(batch['programs']),'maximum_first_nonzero_parameter_moment':max(orders),'moment_inference_admissions':sum(r['moment_admitted'] for r in batch['limit_inferences']),
        'limit_inference_admissions':sum(r['limit_certificate']['admitted'] for r in batch['limit_inferences']),'limit_grammar_promotions':prom,'compiled_jet_indices':arc['compiled_jet_indices'],
        'limit_ablation_comparison':arc['limit_ablation_comparison'],'radius_program_count':len(batch['radius_programs']),'radius_grammar_promotions':len(batch['radius_promotions']),
        'radius_ablation_comparison':arc['radius_ablation_comparison'],'selected_radius':radii[arc['best_radius_by_mode']['primary']]['radius'],
        'actual_mobius_arithmetic_retained':True,'ordinary_zeta_erased':False,'uniform_parameter_level_center_guards_proved':True,'cancellation_before_absolute_envelope_proved':True,
        'all_real_scale_signed_envelopes_proved':True,'verified_ordinary_power':'1','verified_log_losses':'scale-adaptive parameter Cauchy envelope; reciprocal-linear radii give iterated-log powers',
        'parameter_limit_is_uniform_on_compact_x_only':True,'infinite_scale_limit_exchange_claimed':False,'individual_positive_jet_RH_recovery_proved':False,
        'all_integer_tail_conditional_RH_recovery_proved':True,'finite_or_cofinal_subset_is_full_integer_tail':False,'RH_strength':False,
        'all_rational_exponents_supported':True,'semantic_denominator_cap':False,'fresh_levels':cases['levels'],'fresh_scales':cases['integers'],'fresh_envelope_coordinates':cases['envelope_coordinates'],
        'envelope_coordinates_are_proved_bound_optimization_not_huge_prime_samples':True,'critical_estimate_records':len(critical),'fresh_critical_finite_passes':sum(r['fresh_finite_pass'] for r in critical),
        'critical_estimates_have_global_proof':False,'full_jet_factorial_center_interpolation_and_mellin_costs_charged':True,'RH_bound_strategy':spec['RH_bound_strategy'],
        'negative_controls':final['negative_controls'],'new_independent_prime_distribution_estimate':False,'independent_native_counts':v['counts'],'verified_checks':len(v['checks']),
        'verification_sha256':sha(d/'verification.json'),'mathematical_audit_imports_production_code':False,'machine_formalized':False,'not_autonomous_proof_invention':True,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    p=BASE/'parameter-cancellation-results/latest.json'
    return summary(read(p)['run_directory']) if p.exists() else {'status':'not_run'}


def text_report(s):
    lines=['Uniform parameter cancellation, learned logarithmic jets and certified radius search',
        f"Actual families: {s['program_count']}; largest first nonzero parameter moment: {s['maximum_first_nonzero_parameter_moment']}.",
        f"Anonymous scaling admissions: {s['moment_inference_admissions']}; exact compact-limit admissions: {s['limit_inference_admissions']}; compiled indices: {s['compiled_jet_indices']}.",
        'The numerical learner fits raw coefficient responses and a broad declared feature dictionary. Exact admission follows the fit; it does not supply an expected weight or factorial to the learner.',
        'Signed parameter moments are cancelled before the absolute envelope. The actual arithmetic and full positive-real cut center remain; center guards are uniform in q.',
        'Compiled operators are mu*[1_(n>1)*(log log n)^m/m!]. They are limits on compact x, not the original fixed-q programs. Their critical bounds are not inherited.',
        f"Radius candidates: {s['radius_program_count']}; learned promotions: {s['radius_grammar_promotions']}; selected radius: {s['selected_radius']}.",
        'Every admitted positive radius is capped within its Cauchy domain, giving a proved all-real-scale bound. Reciprocal-linear radii yield iterated-log losses. The ordinary x power remains ONE.',
        'Large envelope coordinates optimize a proved inequality; they are not measurements of actual primes at astronomical x.',
        'An entire tail of integer jet orders with uniform-in-x critical estimates would imply RH. Finite banks, cofinal subsets, and a single positive-order jet do not supply that premise.',
        f"Fresh q levels: {s['fresh_levels']}; fresh arithmetic scales: {s['fresh_scales']}.",
        f"Archived critical estimates: {s['critical_estimate_records']}; fresh finite passes: {s['fresh_critical_finite_passes']}. None has a global critical proof.",
        'Whole continued numerators are independently checked by logarithmic integrals of zeta, separate from the producer continuation and parameter differences. Taylor factorials, full centers, real interpolation and Mellin gaps are charged.',
        f"Independent audit groups: {s['verified_checks']}; exact isolated behavioral inference, promotion and equal-slot ablation replay passed.",
        'RH bounds strategy: find and prove signed cross-term control or a closed scale inequality. The existing recovering energy target is A_2(2X)-4*A_2(X)<=B*X^2 at every dyadic X. Its diagonal bound is proved; its signed off-diagonal bound is open.',
        'Feature dictionaries and analytic proof methods were supplied. No autonomous proof invention, new prime-distribution theorem or RH proof is claimed.',
        'Uniform RH-sufficient signed controls verified: 0. RH proved: false.','']
    for r in s['radius_ablation_comparison']:lines.append(f"{r['mode']}: mean log certified envelope={r['mean_log_certified_bound']}; extra slots={r['extra_radius_slots']}.")
    lines.append('Limit promotion ablation: '+str(s['limit_ablation_comparison']))
    return '\n'.join(lines)+'\n'
