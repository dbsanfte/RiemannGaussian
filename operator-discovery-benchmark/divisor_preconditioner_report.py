"""Strictly scoped actual-prime coupling and fractional-sign evidence."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    d=Path(directory).resolve();spec=read(d/'protocol.json');seal=read(d/'seal.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');final=read(d/'final_evaluation.json');cases=read(d/'final_cases.json');v=read(d/'verification.json')
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(d/n)==h
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist'] and cases['generated_after_seal'] and cases['seal_sha256']==sha(d/'seal.json')
    assert arc['selection_closed'] and not arc['final_data_used'] and v['all_passed'] and all(v['checks'].values())
    assert v['checker_sha256']==sha(BASE/'check_divisor_preconditioners.py') and v['final_sha256']==sha(d/'final_evaluation.json') and v['replay_sha256']==seal['files'] and v['protocol_sha256']==digest(spec)
    assert final['cases_sha256']==digest(cases) and not v['mathematical_audit_imports_production_code']
    source=Path(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    from root_lattice_report import summary as parent
    parent(source)
    for f in spec['retained_failed_runs_are_development']:
        p=Path(f['run_directory']);assert sha(p/'failure.json')==f['failure_sha256']
        for n,h in f['files_sha256'].items():assert sha(p/n)==h
        for n,h in read(p/'protocol.json')['code_sha256'].items():
            if n in spec['this_stage_source_files']:assert sha(p/'frozen_source'/n)==h
    assert spec['uniform_RH_sufficient_signed_controls_verified']==v['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[]
    assert not spec['RH_proved'] and not final['RH_proved'] and not spec['new_prime_distribution_estimate_imported'] and not spec['historical_priority_is_acceptance_gate']
    certs=batch['completed_preconditioners'];return {'status':'verified_divisor_preconditioning_with_retained_signed_arithmetic','run_directory':str(d),
        'logarithmic_orders':spec['orders'],'all_positive_rational_log_orders_supported':True,'semantic_denominator_cap':False,
        'integer_global_signed_certificates':len(certs),'global_signed_certificate_records':certs,
        'anonymous_learned_preconditioner_proposals':len(batch['learned_preconditioners']),
        'completed_new_candidate_promotions':sum(p['admitted'] for p in batch['completion_promotions']),
        'learned_universal_bell_relations':sum(p['universal_admitted'] for p in batch['learned_bell_relations'].values()),
        'bell_relation_records':batch['learned_bell_relations'],'all_index_fractional_and_integer_sign_certificates':len(batch['sign_certificates']),
        'anonymous_universal_sign_signatures':sum(p['universal_signature_admitted'] for p in batch['anonymous_sign_fits']),
        'sign_signature_records':batch['anonymous_sign_fits'],'ablation_comparison':arc['ablation_comparison'],
        'completed_log_loss_improvements':sum(p['primary_completed_log_loss']<p['best_ablation_log_loss'] for p in arc['ablation_comparison']),
        'actual_mobius_remainder_retained':True,'ordinary_zeta_erased':False,'all_real_scales_integer_signed_bounds_proved':True,
        'verified_ordinary_power':'1','verified_integer_log_loss':'0','RH_strength':False,
        'first_jet_zero_recovery_proved':True,'higher_jet_zero_recovery_unproved':True,'fractional_critical_centers_and_zero_recovery_unproved':True,
        'actual_prime_factor_support_information_for_every_integer':True,'new_independent_prime_distribution_estimate':False,
        'known_Selberg_and_generalized_von_Mangoldt_is_calibration':True,'known_signed_collapse_used_only_on_preconditioned_component':True,
        'negative_controls':final['controls'],'independent_native_counts':v['counts'],'verified_checks':len(v['checks']),
        'verification_sha256':sha(d/'verification.json'),'machine_formalized':False,'not_autonomous_proof_invention':True,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    p=BASE/'divisor-preconditioner-results/latest.json'
    return summary(read(p)['run_directory']) if p.exists() else {'status':'not_run'}


def text_report(s):
    lines=['Divisor preconditioning with retained signed arithmetic',
        f"Logarithmic arithmetic orders: {s['logarithmic_orders']}. All positive rational orders have semantics; sampling and certificate resources are finite.",
        f"Anonymous approximate divisor-preconditioner proposals: {s['anonymous_learned_preconditioner_proposals']}; completed new candidate promotions: {s['completed_new_candidate_promotions']}.",
        f"Learned universal convolution relations: {s['learned_universal_bell_relations']}; learned universal sign signatures: {s['anonymous_universal_sign_signatures']}.",
        f"True all-real-scale signed certificates: {s['integer_global_signed_certificates']}, each |T_k(x)-h_k(x)|<=C_k*x. Ordinary exponent 1, log loss 0; RH strength false.",
        'The inverse collapses only the divisor-preconditioned component. The actual signed remainder sum mu(d)*R_k(x/d) is retained; ordinary zeta is not erased.',
        'Weighted actual prime powers and prime-power convolutions are recovered from the anonymous coefficient behavior. Integer generalized Mangoldt/Selberg identities are known calibration.',
        'Fractional logarithmic roots have exact all-index sign laws. Their signs alternate beyond the fractional-order threshold across arbitrarily many distinct primes. They have no finite almost-prime support cap.',
        'First-jet cofinal critical signed control would imply RH. Its true supplied global power is 1. Higher derivatives can mask ordinary zeros; fractional branches need a full center and a separate recovery proof.',
        f"Equal-slot completion improves the proved logarithmic loss in {s['completed_log_loss_improvements']} integer contexts, compared with the same fitted proposals plus random slots. Both methods remain at ordinary power 1.",
        f"Independent check groups: {s['verified_checks']}; factorized prime differences, Cauchy-contour harmonic constants, full retained arithmetic remainders, and exact isolated replay.",
        'Proof grammar, polynomial features, signature classes and finite resources were supplied. No historical novelty, new independent prime-distribution estimate or RH proof is claimed.',
        'Uniform RH-sufficient signed controls proved: 0. RH proved: false.','']
    for k,c in s['global_signed_certificate_records'].items():lines.append(f"k={k} P={c['polynomial_coefficients']} b={c['constant_term']} all-scale error constant={c['signed_error_constant']} first-jet ordinary-zero recovery={c['first_derivative_recovers_every_ordinary_zero']}")
    for row in s['ablation_comparison']:lines.append(f"Completion ablation k={row['order']}: log losses {row['primary_completed_log_loss']} / {row['best_ablation_log_loss']}; common ordinary power 1.")
    return '\n'.join(lines)+'\n'
