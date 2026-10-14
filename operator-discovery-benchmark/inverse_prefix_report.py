"""Strict scopes for inverse-prefix identities and unresolved signed estimates."""
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def digest(v):
    return hashlib.sha256(json.dumps(v, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def summary(d):
    d = Path(d).resolve()
    spec, seal, queue, final, v, a, av = map(read, [d / n for n in
        ['protocol.json', 'seal.json', 'proof_queue.json', 'final_evaluation.json', 'verification.json',
         'analytical_review.json', 'analytical_verification.json']])
    for n, h in spec['code_sha256'].items():
        assert sha(BASE / n) == h == sha(d / 'frozen_source' / n)
    for n, h in spec['source_sha256'].items():
        assert sha(n) == h
    for n, h in seal['files'].items():
        assert sha(d / n) == h
    assert seal['protocol_sha256'] == queue['protocol_sha256'] == final['protocol_sha256'] == a['protocol_sha256'] == digest(spec)
    assert v['all_passed'] and all(v['audit_groups'].values()) and av['all_passed'] and all(av['checks'].values())
    assert not v['producer_math_imported_by_independent_checker'] and not av['mathematical_audit_imports_production_code']
    assert v['protocol_sha256'] == digest(spec) and v['final_evaluation_sha256'] == sha(d / 'final_evaluation.json') and v['seal_sha256'] == sha(d / 'seal.json')
    assert all(r['exact_file_hash_match'] for r in v['isolated_replay']['files'].values())
    assert not a['RH_proved'] and a['numerical_fits_do_not_establish_all_scale_estimates'] is True
    for n, h in av['input_sha256'].items():
        assert sha(d / n) == h
    assert av['checker_sha256'] == sha(BASE / 'check_inverse_prefix_analytic.py')
    assert a['source_queue_sha256'] == sha(d / 'proof_queue.json')
    assert not a['actual_full_signed_innovation_bound_proved'] and not final['RH_proved']
    model = queue['reconstruction_inference']
    actual = final['actual_profile']['rows']
    reconstruction = final['reconstruction_observations']; ablation = final['promotion_disabled_observations']
    potentials = final['potential_results']
    return {'status': 'verified_response_inferred_inverse_prefix_identity_and_unresolved_signed_potentials',
        'run_directory': str(d), 'source_review_round': spec['source_review_round'],
        'training_arities': spec['reconstruction_arities'], 'learned_coefficient_rows': model['coefficient_table'],
        'selected_recurrence': model['selected_recurrence'], 'retained_recurrence_fits': len(model['retained_recurrence_fits']),
        'support_fits_checked': sum(model['arity_supports_checked'].values()),
        'global_all_integer_arity_reconstruction_proved': a['reconstruction_certificate']['global_reconstruction_proved'],
        'strict_cutoff_condition': 'x<(u+1)^k', 'integer_arity_semantic_cap': False,
        'rational_normalizer_semantic_denominator_cap': False,
        'generic_final_reconstruction_cases': len(reconstruction),
        'generic_final_reconstruction_passes': sum(r.get('finite_pass', False) for r in reconstruction),
        'promotion_disabled_unseen_arity_cases_missing': sum(r.get('missing', False) for r in ablation),
        'actual_full_block_reconstruction_cases': len(actual),
        'actual_full_block_reconstruction_passes': sum(r.get('all_coefficients_recovered_exactly', False) for r in actual),
        'actual_reference_coefficient_cutoff': final['actual_profile']['cutoff'],
        'inverse_prefix_cutoffs_at_fresh_scales': [{'X': r['X'], 'arity': r['arity'], 'cutoff': r['cutoff']}
            for r in actual if r['X'] in read(d / 'final_cases.json')['actual_scales']],
        'potential_programs': len(read(d / 'candidate_batch.json')['potential_programs']),
        'potential_queue_candidates': len(queue['potential_queue']),
        'fresh_potential_finite_cases': sum(r['finite_cases'] for r in potentials),
        'fresh_potential_finite_passes': sum(r['finite_passes'] for r in potentials),
        'unseen_parameter_constants_missing': sum(r['missing_cases'] for r in potentials),
        'potential_nonnegativity_and_conditional_RH_bridges_proved': sum(r['certificate']['admitted'] for r in a['potential_attempts']),
        'actual_nonnegative_component_envelope_proved': all(r['native_certificate']['admitted'] for r in av['potential_comparisons']),
        'component_envelope_is_supplied_norm_method': True,
        'representation_coefficient_l1_charge': '2^k-1',
        'high_arity_unsigned_cost_is_not_RH_gain': True,
        'actual_coefficient_overlap_with_previous_development': True,
        'new_actual_prime_coefficient_holdout_claimed': False,
        'generic_weights_inferred_without_expected_answer': True,
        'proof_backend_is_separate_from_numeric_selection': True,
        'final_scale_design_visible_to_worker_but_responses_withheld': spec['final_scale_design_visible_to_worker_but_responses_withheld'],
        'search_resource_missingness_not_generalized_beyond_native_pilot_budget': spec['search_resource_missingness_not_generalized_beyond_native_pilot_budget'],
        'verified_checks': len(v['audit_groups']), 'analytical_verified_checks': len(av['checks']),
        'independent_counts': v.get('counts', {}), 'verification_sha256': sha(d / 'verification.json'),
        'analytical_verification_sha256': sha(d / 'analytical_verification.json'),
        'machine_formalized': False, 'global_actual_signed_innovation_bound_proved': False,
        'uniform_RH_sufficient_signed_controls_verified': [], 'RH_proved': False}


def load_latest():
    p = BASE / 'inverse-prefix-results/latest.json'
    return summary(read(p)['run_directory']) if p.exists() else {'status': 'not_run'}


def text_report(s):
    return '\n'.join([
        'Response-inferred inverse-prefix compression and signed potential search',
        f"Anonymous learned rows: {s['learned_coefficient_rows']}; selected recurrence: {s['selected_recurrence']}.",
        f"Exact sparse supports checked: {s['support_fits_checked']}; global all-integer-arity identity proved: {s['global_all_integer_arity_reconstruction_proved']}.",
        'For any unit reference h and inverse a, the learned polynomial reconstructs every prefix through x from a(n) for n<=u whenever x<(u+1)^k. Its exact error is (a-a_u)^k*h^(k-1). The strict endpoint matters.',
        f"Generic final passes with learned-rule promotion: {s['generic_final_reconstruction_passes']}/{s['generic_final_reconstruction_cases']}; unseen-arity cases missing with promotion disabled: {s['promotion_disabled_unseen_arity_cases_missing']}.",
        f"Actual full signed block reconstruction: {s['actual_full_block_reconstruction_passes']}/{s['actual_full_block_reconstruction_cases']}; complete independent actual coefficient cutoff: {s['actual_reference_coefficient_cutoff']}.",
        'The lower inverse prefix carries exact actual arithmetic information. Full reference/divisibility data, tuple weights and computation costs remain charged. Coefficient L1 cost is 2^k-1; growing arity does not produce an RH estimate through input compression.',
        f"Sparse nonnegative potential programs: {s['potential_programs']}; frozen proof-queue leads: {s['potential_queue_candidates']}; fresh finite passes: {s['fresh_potential_finite_passes']}/{s['fresh_potential_finite_cases']}; unseen constants missing: {s['unseen_parameter_constants_missing']}.",
        'A generic error-polynomial proof establishes the learned identity for every arity. A supplied harmonic tuple norm method gives component square energy <=4X^3(1+log(2X))^(4r-4). Neither controls the full actual signed innovation.',
        'If the fixed nonnegative potential satisfies E(2X)+V(2X)-E(X)-V(X)<=C_q ceil(X^(1/q)) at every dyadic X and every sufficiently large q, telescoping and ordinary unfiltered Mellin recovery imply RH. That actual arithmetic inequality remains unproved.',
        'Final scale design is visible to the worker; final response values and seed-derived generic references are withheld until the queue seal. Actual coefficients overlap earlier development; no new prime-coefficient holdout claim. Delayed false-inverse tails and high-arity unsigned costs are separate controls.',
        'Exact arbitrary rational powers have resource-aware evaluators. This native pilot stays inside its declared budget; search-level resource missingness outside that budget remains an extension task.',
        f"Independent numeric groups: {s['verified_checks']}; analytical groups: {s['analytical_verified_checks']}. Counts: {s['independent_counts']}.",
        'Uniform RH-sufficient signed controls verified: 0. RH proved: false.', ''])
