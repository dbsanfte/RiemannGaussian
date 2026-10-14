#!/usr/bin/env python3
"""Preserve exact milestones while integrating reconstruction and signed leads."""
import hashlib
import importlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    previous_path = BASE / 'candidate-review-results/sol-6.1-round-001/integration_verification.json'
    previous = read(previous_path)
    loaded, records = {}, []
    for old in previous['strict_loaders_checked']:
        name = old['loader']
        s = importlib.import_module(name).load_latest()
        assert s['status'] != 'not_run' and not s.get('RH_proved', False)
        loaded[name] = s
        checks = s.get('checks')
        flat = bool(checks) and all(type(v) is bool for v in checks.values())
        if flat:
            assert all(checks.values())
        records.append({'loader': name, 'status': s['status'],
                        'verification_sha256': s.get('verification_sha256'),
                        'checks_passed': sum(checks.values()) if flat else s.get('verified_checks'),
                        'checks_total': len(checks) if flat else s.get('verified_checks')})
    assert len(records) == 28
    from divisor_dual_analytic_report import load_latest as prior_analytic
    from signed_gap_cofinal_report import load_latest as prior_cofinal
    from candidate_review_report import load_latest as prior_parallel
    from inverse_prefix_report import load_latest
    from inverse_prefix_review_report import load_latest as current_reviews
    analytic, cofinal, parallel = prior_analytic(), prior_cofinal(), prior_parallel()
    s, review = load_latest(), current_reviews()
    d, rd = Path(s['run_directory']), Path(review['review_directory'])
    p, v, av = read(d / 'protocol.json'), read(d / 'verification.json'), read(d / 'analytical_verification.json')
    rp, rv = read(rd / 'review_protocol.json'), read(rd / 'verification.json')
    registry = read(BASE / 'root-results/candidate_registry.json')
    assert registry['response_inferred_inverse_prefix_operators_and_signed_scale_potentials'] == s
    assert registry['parallel_Sol_6_1_inverse_prefix_bounds_and_stored_fit_refutations'] == review
    assert registry['parallel_Sol_6_1_analytical_candidate_reviews'] == parallel
    assert registry['cofinal_actual_arithmetic_counterexamples_to_fitted_gap_candidates'] == cofinal
    assert registry['separate_analytical_review_of_detector_candidates'] == analytic
    assert review['source_run'] == str(d) and s['source_review_round'] == parallel['round_directory']
    assert s['global_all_integer_arity_reconstruction_proved']
    assert s['generic_final_reconstruction_cases'] == s['generic_final_reconstruction_passes'] == 84
    assert s['promotion_disabled_unseen_arity_cases_missing'] == 56
    assert s['actual_full_block_reconstruction_cases'] == s['actual_full_block_reconstruction_passes'] == 32
    assert s['actual_reference_coefficient_cutoff'] == 32768
    assert s['potential_programs'] == 2776 and s['potential_queue_candidates'] == 3
    assert s['fresh_potential_finite_cases'] == 24 and s['fresh_potential_finite_passes'] == 6
    assert s['unseen_parameter_constants_missing'] == 24
    assert v['all_passed'] and all(v['audit_groups'].values())
    assert av['all_passed'] and all(av['checks'].values())
    assert rv['all_passed'] and all(rv['checks'].values())
    assert all(x['exact_file_hash_match'] for x in v['isolated_replay']['files'].values())
    assert not v['producer_math_imported_by_independent_checker']
    assert not av['mathematical_audit_imports_production_code']
    assert not rv['mathematical_audit_imports_producer_code']
    assert review['requested_reviewer_model'] == 'gpt-6.1-sol' and review['parallel_reviewers'] == 3
    assert review['reviewed_candidates'] == review['globally_bounded_potentials_verified'] == 3
    assert review['stored_level_inequalities_refuted'] == 12
    assert review['original_existential_cofinal_claims_unresolved'] == 3
    assert review['free_constant_baseline_equivalence_proved']
    assert review['original_fresh_potential_finite_passes'] == s['fresh_potential_finite_passes']
    assert review['original_fresh_potential_finite_cases'] == s['fresh_potential_finite_cases']
    assert not review['reviewer_prose_fully_certified'] and review['development_arithmetic_not_fresh_validation']
    for summary in (s, review):
        assert not summary['RH_proved'] and summary['uniform_RH_sufficient_signed_controls_verified'] == []
    assert not s['global_actual_signed_innovation_bound_proved']
    assert not review['actual_all_scale_signed_bound_proved']
    assert len(p['retained_failed_runs']) == 1
    assert (BASE / 'inverse-prefix-results/pilot-001/failure.json').exists()
    assert not (BASE / 'inverse-prefix-results/pilot-001/candidate_batch.json').exists()
    assert len(rp['retained_failed_review_records']) == 1
    assert registry['verified_arithmetic_consequence_count'] == 20
    assert registry['full_coefficient_origin_native_zeta_comparison_groups'] == 150
    assert (BASE / 'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified'] == registry['uniform_sublinear_signed_controls_verified'] == []
    report = (BASE / 'root-results/report.txt').read_text()
    docs = (BASE / 'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    driver = (BASE / 'run_expanded_probe.py').read_text()
    assert 'RESPONSE-INFERRED INVERSE PREFIX OPERATORS AND SIGNED SCALE POTENTIALS' in report
    assert 'PARALLEL SOL 6.1 REVIEWS OF INVERSE PREFIX POTENTIALS' in report
    assert 'Learned inverse compression feeds a separate signed potential search' in docs
    assert '--inverse-prefix-only' in driver
    milestones = []
    paths = [Path(r['path']) for r in previous['prior_integration_milestones_and_snapshots']] + [previous_path]
    for path in paths:
        old, snapshot = read(path), path.parent / 'integration_snapshot'
        checkers = list(snapshot.glob('verify_*_integration.py'))
        assert len(checkers) == 1
        for key, name in [('driver_sha256', 'run_expanded_probe.py'),
                          ('registry_sha256', 'root-results/candidate_registry.json'),
                          ('report_sha256', 'root-results/report.txt'),
                          ('documentation_sha256', 'SIGNED_ARITHMETIC_CONTROL.md')]:
            assert sha(snapshot / name) == old[key]
        assert sha(checkers[0]) == old['integration_checker_sha256']
        milestones.append({'path': str(path), 'sha256': sha(path),
                           'exact_five_file_snapshot_preserved': True})
    plot = read(d / 'plot_verification.json')
    assert plot['source_verification_sha256'] == sha(d / 'verification.json')
    for name, h in plot['files_sha256'].items():
        assert sha(d / name) == h
    records.append({'loader': 'inverse_prefix_report', 'status': s['status'],
                    'verification_sha256': s['verification_sha256'],
                    'checks_passed': s['verified_checks'], 'checks_total': s['verified_checks']})
    result = {'status': 'integration_verified_research_goal_still_active',
              'objective': registry['objective'],
              'driver_sha256': sha(BASE / 'run_expanded_probe.py'),
              'registry_sha256': sha(BASE / 'root-results/candidate_registry.json'),
              'report_sha256': sha(BASE / 'root-results/report.txt'),
              'documentation_sha256': sha(BASE / 'SIGNED_ARITHMETIC_CONTROL.md'),
              'integration_checker_sha256': sha(BASE / 'verify_inverse_prefix_integration.py'),
              'strict_loaders_checked': records,
              'preserved_extensions': [{'loader': name, 'status': value['status'],
                  'verification_sha256': value['verification_sha256']} for name, value in
                  [('divisor_dual_analytic_report', analytic), ('signed_gap_cofinal_report', cofinal),
                   ('candidate_review_report', parallel)]],
              'separate_inverse_prefix_review_extension': {'loader': 'inverse_prefix_review_report',
                  'status': review['status'], 'verification_sha256': review['verification_sha256'],
                  'checks_passed': review['verified_checks'], 'checks_total': review['verified_checks']},
              'legacy_catalogue_scoped_counts': {'families': 10, 'consequences': 20, 'native_groups': 150},
              'legacy_catalogue_sha256': sha(BASE / 'operator_candidates.txt'),
              'prior_integration_milestones_and_snapshots': milestones,
              'this_extension_frozen_source_sha256': p['code_sha256'],
              'separate_review_frozen_source_sha256': rp['code_sha256'],
              'native_independent_counts': v['counts'],
              'native_analytical_groups': len(av['checks']),
              'separate_review_native_groups': len(rv['checks']),
              'public_contract_checks': {'cases': 12, 'source_sha256': sha(BASE / 'test_inverse_prefix_contracts.py')},
              'scoped_report_sha256': sha(d / 'report.txt'),
              'separate_review_report_sha256': sha(rd / 'report.txt'),
              'original_finite_outcomes_and_formulas_unchanged': True,
              'failed_runs_retained': True, 'original_producer_reruns_for_integration': False,
              'machine_formalized': False, 'uniform_RH_sufficient_signed_controls_verified': [],
              'RH_proved': False,
              'completion_audit': 'Not achieved: universal signed inverse-prefix reconstruction and selected bounded potentials are proved. Fresh fitted inequalities mostly fail; independent actual witnesses refute all twelve stored-level fits. The full actual cofinal all-scale signed innovation upper bound remains unproved.'}
    destination = d / 'integration_verification.json'
    if destination.exists():
        raise FileExistsError('Retain the successful integration milestone')
    destination.write_text(json.dumps(result, indent=2) + '\n')
    snapshot = d / 'integration_snapshot'
    snapshot.mkdir(exist_ok=False)
    for n in ['run_expanded_probe.py', 'root-results/candidate_registry.json',
              'root-results/report.txt', 'SIGNED_ARITHMETIC_CONTROL.md',
              'verify_inverse_prefix_integration.py']:
        target = snapshot / n
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((BASE / n).read_bytes())
    print('29 scoped stages and four separate analytical extensions integrated; all exact historical snapshots retained.')
    print('Signed reconstruction and bounded component proofs verified; critical actual signed inequality remains unproved. RH goal active.')


if __name__ == '__main__':
    main()
