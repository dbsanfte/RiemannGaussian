"""Strict evidence loader for root arithmetic and signed proof synthesis."""
from pathlib import Path
from fractions import Fraction as Q
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    d=Path(directory).resolve();spec=read(d/'protocol.json');seal=read(d/'seal.json');pc=read(d/'parameter_cases.json');cal=read(d/'parameter_calibration.json');cs=read(d/'calibration_seal.json');cases=read(d/'final_cases.json');checked=read(d/'verification.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');final=read(d/'final_evaluation.json')
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for dep in spec['named_calibration_dependencies']:assert sha(dep['path'])==dep['sha256']
    for n,h in seal['files'].items():assert sha(d/n)==h
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist_at_seal'] and not seal['parameter_cases_exist_at_seal']
    assert arc['selection_closed'] and not arc['final_data_used'] and pc['seal_sha256']==sha(d/'seal.json') and pc['generated_after_archive_seal'] and pc['no_final_scale_information_present']
    assert cal['parameters_sha256']==digest(pc) and cal['training_only'] and not cal['final_scales_used']
    for key,n in [('archive_seal_sha256','seal.json'),('parameter_cases_sha256','parameter_cases.json'),('parameter_calibration_sha256','parameter_calibration.json')]:assert cs[key]==sha(d/n)
    assert not cs['final_cases_exist_at_calibration_seal'] and cases['calibration_seal_sha256']==digest(cs) and cases['generated_after_calibration_seal']
    assert checked['all_passed'] and all(checked['checks'].values()) and checked['protocol_sha256']==digest(spec) and checked['checker_sha256']==sha(BASE/'check_root_lattices.py')
    assert checked['final_sha256']==sha(d/'final_evaluation.json') and checked['replay_sha256']==seal['files'] and not checked['mathematical_audit_imports_production_code']
    assert final['cases_sha256']==digest(cases) and final['calibration_seal_sha256']==digest(cs) and final['seal_sha256']==digest(seal) and final['protocol_sha256']==digest(spec)
    source=Path(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    from lattice_synthesis_report import summary as parent
    parent(source)
    assert spec['uniform_RH_sufficient_signed_controls_verified']==checked['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[]
    assert not spec['RH_proved'] and not checked['RH_proved'] and not final['RH_proved'] and not spec['new_prime_distribution_bound_imported'] and not spec['historical_priority_is_acceptance_gate']
    for failed in spec['retained_failed_runs_are_development']:
        f=Path(failed['run_directory']);assert sha(f/'failure.json')==failed['failure_sha256']
        for n,h in failed['retained_files_sha256'].items():assert sha(f/n)==h
        for n,h in failed['original_code_sha256'].items():
            if n in spec['this_stage_source_files']:assert sha(f/'frozen_source'/n)==h
    ps={p['id']:p for p in batch['programs']};outcomes={o['candidate_id']:o for o in final['outcomes']};records=[]
    for c in arc['archive']:
        p=ps[c['program_id']];o=outcomes[c['id']];assert not c['same_fitted_constants_proved'] and not o['same_fitted_constants_proved_global']
        assert not (c['uniform_frontier_has_proved_constant_witness'] and c['RH_sufficient_if_uniform'])
        records.append({'candidate':c,'program':p,'final_outcome':o})
    recovering=[r for r in records if r['candidate']['RH_sufficient_if_uniform']];calibration=[r for r in records if Q(r['program']['parameters'][2])==1]
    learned=[p for p in ps.values() if 'learned_actual_centered_response' in p['origins']]
    relations=batch['moment_relations'];certified=[r for r in relations if r['universal_certificate_admitted']]
    actual_certified=[r for r in certified if r['decoded_model_after_fit']=='inverse']
    assert all(Q(read(d/'discovery_data.json')['tables'][r['parameter_id']]['parameters'][2])==1 for r in certified)
    ab=arc['ablation_comparison'];before,after=ab['best_ablation_log_cost'],ab['best_primary_log_cost']
    return {'status':'verified_normalized_root_arithmetic_and_signed_profile_learning','run_directory':str(d),
        'program_count':len(ps),'semantic_operator_count':len({p['semantic_operator_id'] for p in ps.values()}),
        'growth_hypotheses':sum(c['program_id'] in ps for c in batch['candidates']),'primary_and_ablation_hypotheses':len(batch['candidates']),
        'parameter_contexts':len(spec['parameters']),'arithmetic_dilation_factors':sorted({p['parameters'][2] for p in ps.values()},key=Q),
        'arithmetic_root_orders':sorted({str(1/Q(p['parameters'][2])) for p in ps.values() if Q(p['parameters'][2])<1},key=Q),
        'smoothing_root_orders':sorted({str(1/Q(p['parameters'][1])) for p in ps.values()},key=Q),
        'recovering_root_programs':sum(p['zero_bridge']['RH_sufficient_if_uniform'] for p in ps.values()),
        'finite_division_escape_bridges':sum(p['zero_bridge']['kind']=='finite_division_escape' for p in ps.values()),
        'zero_erasing_signed_programs':sum(p['zero_bridge']['kind']=='exact_arithmetic_zero_erasure' for p in ps.values()),
        'learned_actual_response_programs':len(learned),'learned_actual_response_records':[r for r in records if r['program'] in learned],
        'anonymous_moment_relation_records':len(relations),'finite_validated_moment_relations':sum(r['relation'].get('training_passed',False) and r['relation'].get('validation_passed',False) for r in relations),
        'universal_moment_relations':len(certified),'universal_actual_moment_relations':len(actual_certified),
        'universal_relations_are_known_zero_erasing_calibration':True,'moment_relation_records':relations,
        'compiled_actual_arithmetic_promotions':len(batch['arithmetic_promotions']),
        'proved_signed_actual_rapid_estimates':sum(c['global_premise_proved'] for p in ps.values() for c in p['rapid_certificates'].values()),
        'proved_actual_rapid_estimates_retain_ordinary_zeta_information':False,
        'records':records,'recovering_records':recovering,'signed_calibration_records':calibration,
        'RH_if_uniform_finite_survivors':[r for r in recovering if r['final_outcome']['finite_points_passed']],
        'signed_calibration_finite_passes':sum(r['final_outcome']['finite_points_passed'] for r in calibration),
        'late_tail_controls':final['late_tail_controls'],'late_tail_finite_passes':sum(r['finite_points_passed'] for r in final['late_tail_controls']),
        'zero_erasure_controls':final['zero_erasure_controls'],'false_RH_inferences_rejected':len(final['zero_erasure_controls']),
        'signed_rapid_fresh_witness_records':len(final['signed_rapid_witnesses']),
        'ablation_comparison':ab,'promotion_improved_best_charged_recovery':before is not None and after is not None and after<before-1e-10,
        'independent_native_counts':checked['counts'],'verified_checks':len(checked['checks']),
        'all_infinite_actual_arithmetic_positions_included':True,'arbitrary_positive_rational_arithmetic_dilations_supported':True,'arbitrary_positive_rational_smoothing_orders_supported':True,
        'semantic_denominator_cap':False,'scale_variable':'ordinary arithmetic index M; X=M^r','actual_weak_ordinary_zeta_exponent':'1',
        'actual_target_ordinary_zeta_exponent':'1/2+epsilon/q^nu','cofinal_constants_free_for_every_q':True,'finite_q_grid_suffices':False,
        'known_signed_collapse_is_calibration_only':True,'counterfeit_tails_are_actual_counterexamples':False,
        'new_independent_prime_distribution_estimate':False,'verification_sha256':sha(d/'verification.json'),
        'named_calibration_dependencies':spec['named_calibration_dependencies'],'machine_formalized':False,'not_autonomous_proof_invention':True,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    p=BASE/'root-lattice-results/latest.json'
    return summary(read(p)['run_directory']) if p.exists() else {'status':'not_run'}


def text_report(s):
    ab=s['ablation_comparison'];lines=[
        'Normalized root arithmetic and anonymous signed-profile learning',
        f"Primary programs: {s['program_count']}; semantic operators: {s['semantic_operator_count']}; hypotheses: {s['growth_hypotheses']}; with ablation: {s['primary_and_ablation_hypotheses']}.",
        f"Arithmetic dilations: {s['arithmetic_dilation_factors']}; arithmetic root orders: {s['arithmetic_root_orders']}; smoothing root orders: {s['smoothing_root_orders']}.",
        'All positive rational dilation and smoothing parameters have exact semantics. This pilot samples a frozen bounded set; it does not exhaust the grammar.',
        'Every scale is measured by ordinary arithmetic index M, with X=M^r and peak normalization R=K/ell. Reduced displayed powers caused by rescaling do not count as stronger zeta control.',
        f"Independent verification: {s['verified_checks']} check groups, complete infinite moments, a separately evaluated arithmetic rectangle plus full tail, and exact isolated replay.",
        f"Anonymous moment relations: {s['anonymous_moment_relation_records']} records; {s['finite_validated_moment_relations']} finite validations; {s['universal_moment_relations']} admitted universal relations ({s['universal_actual_moment_relations']} actual).",
        f"Exact arithmetic compilation promotions: {s['compiled_actual_arithmetic_promotions']}. Universal relations recover the known signed mu*1 collapse; this is zero-erasing calibration, not new ordinary-zero control.",
        f"True signed actual all-scale rapid-decay estimates: {s['proved_signed_actual_rapid_estimates']}. Their factor ledger cancels ordinary zeta identically; RH consequences: none.",
        f"Learned actual-centered response programs: {s['learned_actual_response_programs']}. The learner receives numeric response columns without pole locations or named solutions.",
        f"Recovering root programs: {s['recovering_root_programs']}; exact finite-division RH bridges: {s['finite_division_escape_bridges']}; archived RH-if-uniform finite survivors: {len(s['RH_if_uniform_finite_survivors'])}.",
        'For 0<r<1, numerator cancellation at a hypothetical right-half zero forces repeated beta/r until Re>1. The all-height kernel certificate is separately mandatory. The critical uniform signed premise remains unproved.',
        'Actual weak normalized exponent: 1. RH target: for every q exists free finite C_q, for every real M>=1, |V_r(M)|<=C_q*M^(1/2+epsilon/q^nu)*log(e+M)^d.',
        f"Late-tail controls: {len(s['late_tail_controls'])}; finite passes: {s['late_tail_finite_passes']}. Their full invisible tail creates an uncancelled ordinary pole at 1, which disproves their critical global targets without disproving actual arithmetic estimates.",
        f"False RH inferences rejected despite true signed rapid control: {s['false_RH_inferences_rejected']}.",
        f"Equal proposal budgets: {ab['admitted_shape_promotions']}/{ab['proposal_slots']} derivative promotions; primary programs {ab['primary_programs']}, ablation {ab['ablation_programs']}; conditional best log costs {ab['best_primary_log_cost']} / {ab['best_ablation_log_cost']}; improvement={s['promotion_improved_best_charged_recovery']}.",
        'Proof backends, kernel grammar, numerical budgets and cost criteria were supplied. No new prime-distribution estimate, historical novelty, or RH proof is claimed.',
        'Uniform RH-sufficient signed controls proved: 0. RH proved: false.','',
        'Selected hypotheses (fitted constants are never universal certificates):']
    for row in s['records']:
        c,p,o=row['candidate'],row['program'],row['final_outcome'];f=c['frontier']
        lines.append(f"{c['id'][:12]} K,ell,r={p['parameters']} shape={p['shape']['terms']} eta={f['limit']} nu={f['approach_power']} d={f['log_power']} RH_if_uniform={c['RH_sufficient_if_uniform']} global_witness={c['uniform_frontier_has_proved_constant_witness']} fresh_pass={o['finite_points_passed']} ratio={o['maximum_ratio']:.6g}")
    return '\n'.join(lines)+'\n'
