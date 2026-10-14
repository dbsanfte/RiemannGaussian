"""Strict report loader: typed arithmetic, global estimates and open RH bounds."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    directory=Path(directory).resolve();spec=read(directory/'protocol.json');seal=read(directory/'seal.json');pc=read(directory/'parameter_cases.json');cal=read(directory/'parameter_calibration.json');cs=read(directory/'calibration_seal.json');cases=read(directory/'final_cases.json');checked=read(directory/'verification.json');batch=read(directory/'candidate_batch.json');arc=read(directory/'archive.json');final=read(directory/'final_evaluation.json')
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(directory/'frozen_source'/n)==spec['code_sha256'][n]
    for dep in spec['named_calibration_dependencies']:assert sha(dep['path'])==dep['sha256']
    for n,h in seal['files'].items():assert sha(directory/n)==h
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist_at_seal'] and not seal['parameter_cases_exist_at_seal']
    assert arc['selection_closed'] and not arc['final_data_used'] and pc['seal_sha256']==sha(directory/'seal.json') and pc['generated_after_archive_seal'] and pc['no_final_scale_information_present']
    assert cal['parameters_sha256']==digest(pc) and cal['training_only'] and not cal['final_scales_used']
    for key,n in [('archive_seal_sha256','seal.json'),('parameter_cases_sha256','parameter_cases.json'),('parameter_calibration_sha256','parameter_calibration.json')]:assert cs[key]==sha(directory/n)
    assert not cs['final_cases_exist_at_calibration_seal'] and cases['calibration_seal_sha256']==digest(cs) and cases['generated_after_calibration_seal']
    assert checked['all_passed'] and all(checked['checks'].values()) and checked['protocol_sha256']==digest(spec) and checked['checker_sha256']==sha(BASE/'check_lattice_synthesis.py')
    assert checked['final_sha256']==sha(directory/'final_evaluation.json') and checked['replay_sha256']==seal['files'] and not checked['mathematical_audit_imports_production_code']
    assert final['cases_sha256']==digest(cases) and final['calibration_seal_sha256']==digest(cs) and final['seal_sha256']==digest(seal)
    source=Path(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    from kernel_correlation_report import summary as parent
    parent(source)
    assert spec['uniform_RH_sufficient_signed_controls_verified']==checked['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[]
    assert not final['RH_proved'] and not spec['RH_proved'] and not spec['new_prime_distribution_estimate_imported'] and not spec['historical_priority_is_acceptance_gate']
    ps={p['id']:p for p in batch['programs']};outcomes={o['candidate_id']:o for o in final['outcomes']};records=[]
    for c in arc['archive']:
        o=outcomes[c['id']];assert not o['uniform_signed_premise_proved'];records.append({'candidate':c,'program':ps[c['program_id']],'final_outcome':o})
    bank_outcomes={o['bank_id']:o for o in final['bank_outcomes']};bank_records=[{'bank':b,'final_outcome':bank_outcomes[b['id']]} for b in arc['banks']]
    references=[{'program':ps[i],'fresh_outcomes':[o for o in final['reference_bound_outcomes'] if o['program_id']==i]} for i in arc['reference_program_ids']]
    primary_candidates=[c for c in batch['candidates'] if c['program_id'] in ps]
    return {'status':'verified_typed_lattice_global_synthesis_and_fractional_banks','run_directory':str(directory),
        'program_count':len(ps),'growth_hypotheses':len(primary_candidates),'primary_and_ablation_hypotheses':len(batch['candidates']),
        'fractional_dilation_factors':spec['r_enumeration']['selected'],'parameter_contexts':len(spec['parameters']),
        'operator_zero_preserving_programs':sum(p['zero_bridge']['all_right_half_ordinary_zeros_preserved'] for p in ps.values()),
        'real_root_operator_programs':sum(p['zero_bridge']['kind']=='exact_all_real_polynomial_roots' for p in ps.values()),
        'native_complex_operator_root_programs':sum(p['zero_bridge']['kind']=='certified_finite_operator_root_exclusion' for p in ps.values()),
        'learned_anonymous_programs':sum(any(o['family']=='learned_anonymous_unit' for o in p['origins']) for p in ps.values()),
        'learned_exact_two_pole_annihilators':sum(any(o['family']=='learned_anonymous_unit' for o in p['origins']) and p['residues']['both_reference_residues_vanish'] for p in ps.values()),
        'proved_reference_global_estimates':sum(len(p['reference_decay_certificates']) for p in ps.values()),
        'actual_support_sign_loss_barriers':sum(p['sign_loss_barrier']['status']=='certified_absolute_rewrite_barrier' for p in ps.values()),
        'records':records,'bank_records':bank_records,'reference_records':references,
        'RH_if_uniform_finite_survivors':[r for r in records if r['candidate']['RH_sufficient_if_uniform'] and r['final_outcome']['finite_points_passed']],
        'quasi_RH_if_uniform_finite_survivors':[r for r in records if r['candidate']['critical_zero_constraint_if_uniform'] and not r['candidate']['RH_sufficient_if_uniform'] and r['final_outcome']['finite_points_passed']],
        'complementary_RH_banks':len(bank_records),'complementary_RH_banks_finite_passes':sum(r['final_outcome']['finite_points_passed'] for r in bank_records),
        'negative_controls':final['negative_controls'],'typed_arithmetic_aliases_rejected':sum(c['typed_alias_rejected'] for c in final['negative_controls']),
        'ablation_comparison':arc['ablation_comparison'],'independent_native_counts':checked['counts'],'verified_checks':len(checked['checks']),
        'all_infinite_actual_arithmetic_positions_included':True,'arbitrary_positive_rational_root_orders_supported':True,'arbitrary_rational_arithmetic_dilation_above_one_supported':True,
        'actual_weak_density_exponent':'1/r','actual_weak_ordinary_zeta_exponent':'1','actual_target_density_exponent':'(1/2+epsilon/q^nu)/r',
        'unit_reference_negative_powers_proved_globally':True,'actual_inverse_negative_powers_proved':False,
        'post_rewrite_absolute_norm_cannot_reach_RH_strength':True,'barrier_is_counterexample_to_actual_growth':False,
        'cofinal_constants_free_for_every_q_and_member':True,'finite_q_grid_suffices':False,
        'new_independent_prime_distribution_estimate':False,'verification_sha256':sha(directory/'verification.json'),
        'named_calibration_dependencies':spec['named_calibration_dependencies'],'machine_formalized':False,'not_autonomous_proof_invention':True,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    pointer=BASE/'lattice-synthesis-results/latest.json'
    return summary(read(pointer)['run_directory']) if pointer.exists() else {'status':'not_run'}


def text_report(s):
    ac=s['ablation_comparison'];lines=[
        'Typed lattice global estimate synthesis and complementary fractional dilations',
        f"Primary programs: {s['program_count']}; hypotheses: {s['growth_hypotheses']}; including ablation: {s['primary_and_ablation_hypotheses']}.",
        f"Dilation factors, chosen before data: {s['fractional_dilation_factors']}. Parameter contexts: {s['parameter_contexts']}.",
        f"Independent verification: {s['verified_checks']} checks, complete infinite tails, exact deterministic isolated replay.",
        f"Anonymous response learning: {s['learned_anonymous_programs']} programs; {s['learned_exact_two_pole_annihilators']} exactly annihilate both reference poles without receiving their locations in the learner.",
        f"True all-scale unit-reference negative-power estimates synthesized: {s['proved_reference_global_estimates']}. These have arithmetic profile zeta(s)*zeta(r*s) and no RH consequence.",
        'Actual arithmetic profile: zeta(s)/zeta(r*s). Its true all-scale weak density exponent is 1/r, corresponding to ordinary-zeta exponent 1. A smaller displayed power obtained by increasing r is not a stronger ordinary-zeta result.',
        f"Actual squarefree-support sign-loss barriers certified: {s['actual_support_sign_loss_barriers']}. They rule out a supplied absolute-norm proof method below 1/r, not the signed arithmetic estimate itself.",
        f"All-height operator zero preservation: {s['operator_zero_preserving_programs']} programs, including {s['real_root_operator_programs']} real-root and {s['native_complex_operator_root_programs']} complete native complex-root certificates.",
        'RH target: for every q exists a free finite C_q, for every N>=1, |Z_mu,r(N)|<=C_q*N^((1/2+epsilon/q^nu)/r)*log(e+N)^d. Critical uniform signed estimates are unproved.',
        'For r<2, the bound confines any possible right-half zero to E_r={r^j/2:r^j<2}; complementary exact empty intersections imply RH if every member estimate is uniform. All heights and multiplicities are included.',
        f"Automatically assembled complementary banks: {s['complementary_RH_banks']}; fresh finite passes: {s['complementary_RH_banks_finite_passes']}. Individual RH-if-uniform finite survivors: {len(s['RH_if_uniform_finite_survivors'])}; quasi-RH survivors: {len(s['quasi_RH_if_uniform_finite_survivors'])}.",
        f"True reference certificates rejected when relabelled as actual inverse proofs: {s['typed_arithmetic_aliases_rejected']}.",
        f"Promotions admitted: {ac['admitted_promotions']}/{ac['proposal_slots']}. Equal-slot conditional log costs: primary={ac['best_primary_log_cost']}, ablation={ac['best_ablation_log_cost']}.",
        'The search chooses formulas and estimates, but its proof methods and resource grammar were supplied. Historical novelty is not a gate. No new prime-distribution estimate or RH-strength uniform control is proved.',
        'Uniform RH-sufficient signed controls proved: 0. RH proved: false.','',
        'Selected actual-arithmetic hypotheses (finite passes use fitted constants):']
    for r in s['records']:
        c,p,o=r['candidate'],r['program'],r['final_outcome'];f=c['frontier']
        lines.append(f"{c['id'][:12]} K,ell,r={p['parameters']} c={p['shape']['terms']} ordinary_eta={f['ordinary_limit']} nu={f['approach_power']} d={f['log_power']} RH_if_uniform={c['RH_sufficient_if_uniform']} fresh_pass={o['finite_points_passed']} max_ratio={o['maximum_ratio']:.6g}")
    lines += ['', 'Complementary fractional banks:']
    for r in s['bank_records']:
        b,o=r['bank'],r['final_outcome'];lines.append(f"{b['id'][:12]} members={[i[:12] for i in b['member_candidate_ids']]} intersection={b['certificate']['remaining_real_parts']} fresh_pass={o['finite_points_passed']} uniform_proved=False")
    return '\n'.join(lines)+'\n'
