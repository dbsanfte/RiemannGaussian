#!/usr/bin/env python3
"""Preserve earlier milestones while integrating checked parallel proof attempts."""
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
    previous_path = BASE / 'signed-gap-profile-results/pilot-001/cofinal-audit-001/integration_verification.json'
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
    from candidate_review_report import load_latest
    analytic, cofinal, review = prior_analytic(), prior_cofinal(), load_latest()
    d = Path(review['round_directory'])
    protocol, verification, dispatch = map(read,
        [d / 'review_protocol.json', d / 'verification.json', d / 'dispatch.json'])
    registry = read(BASE / 'root-results/candidate_registry.json')
    assert registry['parallel_Sol_6_1_analytical_candidate_reviews'] == review
    assert registry['cofinal_actual_arithmetic_counterexamples_to_fitted_gap_candidates'] == cofinal
    assert registry['independent_constant_profiles_and_actual_signed_nullspace_gap'] == loaded['signed_gap_profile_report']
    assert registry['separate_analytical_review_of_detector_candidates'] == analytic
    assert review['requested_reviewer_model'] == 'gpt-6.1-sol'
    assert review['reviewer_batches'] == len(dispatch['agents']) == 3
    assert review['source_run'] == cofinal['source_run'] == loaded['signed_gap_profile_report']['run_directory']
    assert review['reviewed_candidate_count'] == cofinal['unresolved_actual_half_gap_candidates']
    assert review['original_queue_candidate_count'] == cofinal['candidate_count']
    assert set(review['all_refuted_candidate_ids']) == set(cofinal['refuted_candidate_ids']) | set(review['new_refuted_candidate_ids'])
    assert len(review['all_refuted_candidate_ids']) + review['remaining_uniform_half_gap_claims'] == review['original_queue_candidate_count']
    assert review['verified_new_global_refutations'] == len(verification['verified_witnesses'])
    assert review['original_fresh_half_gap_passes'] == loaded['signed_gap_profile_report']['fresh_half_gap_passes']
    assert review['original_formulas_fits_and_finite_passes_unchanged']
    assert verification['all_passed'] and all(verification['checks'].values())
    assert not review['reviewer_proof_text_certified'] and not verification['mathematical_audit_imports_production_code']
    assert not review['other_reviewer_development_arithmetic_independently_verified']
    assert review['new_global_actual_signed_upper_bounds_proved'] == 0 and not review['machine_formalized']
    for n, h in protocol['input_sha256'].items():
        assert sha(d / n) == h
    for n, h in protocol['code_sha256'].items():
        assert sha(BASE / n) == h == sha(d / 'frozen_source' / n)
    assert registry['verified_arithmetic_consequence_count'] == 20
    assert registry['full_coefficient_origin_native_zeta_comparison_groups'] == 150
    assert (BASE / 'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified'] == registry['uniform_sublinear_signed_controls_verified'] == []
    assert not registry['historical_priority_is_acceptance_gate']
    report = (BASE / 'root-results/report.txt').read_text()
    docs = (BASE / 'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    driver = (BASE / 'run_expanded_probe.py').read_text()
    assert 'PARALLEL SOL 6.1 ANALYTICAL REVIEWS OF EXACT SIGNED-GAP CANDIDATES' in report
    assert f"current half-gap claims unresolved: {review['remaining_uniform_half_gap_claims']}" in report
    assert 'Parallel analytical reviews preserve exact claims and require independent checks' in docs
    assert '--candidate-reviews-only' in driver and 'candidate_review_workflow.py' in driver
    milestones = []
    paths = [Path(r['path']) for r in previous['prior_integration_milestones_and_snapshots']] + [previous_path]
    for p in paths:
        old, snapshot = read(p), p.parent / 'integration_snapshot'
        checkers = list(snapshot.glob('verify_*_integration.py'))
        assert len(checkers) == 1
        for key, name in [('driver_sha256', 'run_expanded_probe.py'),
                          ('registry_sha256', 'root-results/candidate_registry.json'),
                          ('report_sha256', 'root-results/report.txt'),
                          ('documentation_sha256', 'SIGNED_ARITHMETIC_CONTROL.md')]:
            assert sha(snapshot / name) == old[key]
        assert sha(checkers[0]) == old['integration_checker_sha256']
        milestones.append({'path': str(p), 'sha256': sha(p),
                           'exact_five_file_snapshot_preserved': True})
    result = {'status': 'integration_verified_research_goal_still_active',
              'objective': registry['objective'],
              'driver_sha256': sha(BASE / 'run_expanded_probe.py'),
              'registry_sha256': sha(BASE / 'root-results/candidate_registry.json'),
              'report_sha256': sha(BASE / 'root-results/report.txt'),
              'documentation_sha256': sha(BASE / 'SIGNED_ARITHMETIC_CONTROL.md'),
              'integration_checker_sha256': sha(BASE / 'verify_candidate_review_integration.py'),
              'strict_loaders_checked': records,
              'preserved_prior_analytical_extension': {'loader': 'divisor_dual_analytic_report',
                  'status': analytic['status'], 'verification_sha256': analytic['verification_sha256']},
              'preserved_cofinal_extension': {'loader': 'signed_gap_cofinal_report',
                  'status': cofinal['status'], 'verification_sha256': cofinal['verification_sha256']},
              'separate_parallel_review_extension': {'loader': 'candidate_review_report',
                  'status': review['status'], 'verification_sha256': review['verification_sha256'],
                  'checks_passed': review['verified_checks'], 'checks_total': review['verified_checks']},
              'legacy_catalogue_scoped_counts': {'families': 10, 'consequences': 20, 'native_groups': 150},
              'legacy_catalogue_sha256': sha(BASE / 'operator_candidates.txt'),
              'prior_integration_milestones_and_snapshots': milestones,
              'parallel_analytical_review_dispositions': {k: review[k] for k in
                  ['requested_reviewer_model', 'reviewer_batches', 'reviewed_candidate_count',
                   'verified_new_global_refutations', 'all_refuted_candidate_ids',
                   'remaining_uniform_half_gap_claims']},
              'this_extension_frozen_source_sha256': protocol['code_sha256'],
              'public_contract_checks': {'cases': 8, 'source_sha256': sha(BASE / 'test_candidate_review_contracts.py')},
              'scoped_report_sha256': sha(d / 'report.txt'),
              'original_finite_outcomes_and_formulas_unchanged': True,
              'reviewer_prose_and_other_development_arithmetic_not_promoted': True,
              'original_producer_reruns_for_integration': False,
              'uniform_RH_sufficient_signed_controls_verified': [], 'RH_proved': False,
              'completion_audit': 'Not achieved: parallel Sol 6.1 attempts refute five more exact formulas by an independently checked actual small dyadic witness. Forty cofinal all-scale half-gap claims remain unresolved. No RH-strength signed arithmetic upper bound was proved.'}
    destination = d / 'integration_verification.json'
    if destination.exists():
        raise FileExistsError('Retain the integration milestone')
    destination.write_text(json.dumps(result, indent=2) + '\n')
    snapshot = d / 'integration_snapshot'
    snapshot.mkdir(exist_ok=False)
    for n in ['run_expanded_probe.py', 'root-results/candidate_registry.json',
              'root-results/report.txt', 'SIGNED_ARITHMETIC_CONTROL.md',
              'verify_candidate_review_integration.py']:
        target = snapshot / n
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((BASE / n).read_bytes())
    print('28 scoped stages, prior analytical/cofinal extensions and parallel Sol 6.1 reviews integrated.')
    print('Exact historical snapshots retained; five new half-gap refutations checked; 40 claims unresolved. RH goal active.')


if __name__ == '__main__':
    main()
