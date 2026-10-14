#!/usr/bin/env python3
"""Retain research milestones while admitting narrow workflow audit results."""
import hashlib
import importlib
import json
from pathlib import Path
from detector_workflow_guard import require_verified_runtime

BASE = Path(__file__).resolve().parent


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    require_verified_runtime()
    previous_path = BASE / 'inverse-prefix-results/pilot-002/integration_verification.json'
    previous = read(previous_path)
    records = []
    for old in previous['strict_loaders_checked']:
        s = importlib.import_module(old['loader']).load_latest()
        require(s['status'] != 'not_run' and not s.get('RH_proved', False), 'Prior scoped stage unavailable or overclaimed')
        records.append({'loader': old['loader'], 'status': s['status'],
                        'verification_sha256': s.get('verification_sha256'),
                        'checks_passed': old['checks_passed'], 'checks_total': old['checks_total']})
    require(len(records) == 29, 'Prior stage count changed')
    from divisor_dual_analytic_report import load_latest as a1
    from signed_gap_cofinal_report import load_latest as a2
    from candidate_review_report import load_latest as a3
    from inverse_prefix_review_report import load_latest as a4
    from workflow_audit_report import load_latest
    extension_loaders = [('divisor_dual_analytic_report', a1()), ('signed_gap_cofinal_report', a2()),
                         ('candidate_review_report', a3()), ('inverse_prefix_review_report', a4())]
    s = load_latest(); d = Path(s['audit_directory'])
    p, v = read(d / 'audit_protocol.json'), read(d / 'audit_verification.json')
    registry = read(BASE / 'root-results/candidate_registry.json')
    require(registry['workflow_reliability_and_generic_signed_bound_discovery_audit'] == s, 'Root audit scope differs')
    require(v['all_passed'] and s['contract_test_cases'] == 36, 'Audit tests not checked')
    require(s['generic_signed_bound_certificates'] == s['unseen_signed_generator_instances'] == 4, 'Generic calibration count differs')
    require(s['delayed_finite_passing_control_candidates_rejected'] == 4, 'False control coverage differs')
    require(not s['actual_all_scale_signed_bound_proved'] and not s['RH_proved'], 'Audit claims actual RH control')
    require(not s['RH_discovery_probability_established'], 'Unsupported RH success probability')
    require(not s['general_purpose_estimate_discovery_demonstrated'], 'Generic calibration overstated')
    require(s['witness_derived_exclusions']['remaining_uniform_half_gap_claims'] == 40, 'Legacy exclusions changed')
    require(registry['uniform_RH_sufficient_signed_controls_verified'] == [] and registry['uniform_sublinear_signed_controls_verified'] == [], 'RH registry changed')
    require(registry['verified_arithmetic_consequence_count'] == 20 and registry['full_coefficient_origin_native_zeta_comparison_groups'] == 150, 'Legacy counts changed')
    require((BASE / 'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES'), 'Legacy family catalogue changed')
    report = (BASE / 'root-results/report.txt').read_text()
    docs = (BASE / 'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    driver = (BASE / 'run_expanded_probe.py').read_text()
    require('WORKFLOW RELIABILITY AND GENERIC SIGNED BOUND DISCOVERY AUDIT' in report, 'Root report lacks scoped audit')
    require('Workflow audit adds safety boundaries and a signed-bound calibration' in docs, 'Documentation lacks audit limits')
    require('require_verified_runtime()' in driver and 'witness_derived_refutations' in driver, 'Root entry lacks safety boundary')
    milestones = []
    paths = [Path(r['path']) for r in previous['prior_integration_milestones_and_snapshots']] + [previous_path]
    for path in paths:
        old, snapshot = read(path), path.parent / 'integration_snapshot'
        checkers = list(snapshot.glob('verify_*_integration.py'))
        require(len(checkers) == 1, 'Historical checker snapshot missing')
        for key, name in [('driver_sha256', 'run_expanded_probe.py'),
                          ('registry_sha256', 'root-results/candidate_registry.json'),
                          ('report_sha256', 'root-results/report.txt'),
                          ('documentation_sha256', 'SIGNED_ARITHMETIC_CONTROL.md')]:
            require(sha(snapshot / name) == old[key], 'Historical exact snapshot changed')
        require(sha(checkers[0]) == old['integration_checker_sha256'], 'Historical checker changed')
        milestones.append({'path': str(path), 'sha256': sha(path), 'exact_five_file_snapshot_preserved': True})
    records.append({'loader': 'workflow_audit_report', 'status': s['status'],
                    'verification_sha256': s['verification_sha256'], 'checks_passed': 36, 'checks_total': 36})
    result = {'status': 'integration_verified_research_goal_still_active', 'objective': registry['objective'],
              'driver_sha256': sha(BASE / 'run_expanded_probe.py'),
              'registry_sha256': sha(BASE / 'root-results/candidate_registry.json'),
              'report_sha256': sha(BASE / 'root-results/report.txt'),
              'documentation_sha256': sha(BASE / 'SIGNED_ARITHMETIC_CONTROL.md'),
              'integration_checker_sha256': sha(BASE / 'verify_workflow_audit_integration.py'),
              'strict_loaders_checked': records,
              'preserved_extensions': [{'loader': name, 'status': value['status'],
                  'verification_sha256': value['verification_sha256']} for name, value in extension_loaders],
              'legacy_catalogue_scoped_counts': {'families': 10, 'consequences': 20, 'native_groups': 150},
              'legacy_catalogue_sha256': sha(BASE / 'operator_candidates.txt'),
              'prior_integration_milestones_and_snapshots': milestones,
              'this_extension_frozen_source_sha256': p['code_sha256'],
              'contract_cases': 36, 'generic_all_integer_signed_bounds': 4,
              'scoped_report_sha256': sha(d / 'report.txt'), 'original_producer_reruns_for_integration': False,
              'original_finite_outcomes_and_formulas_unchanged': True, 'machine_formalized': False,
              'uniform_RH_sufficient_signed_controls_verified': [], 'RH_proved': False,
              'completion_audit': 'Not achieved: workflow contract faults are addressed through tested safety boundaries, and unseen generic signed moment laws admit all-integer bounds. No probability of discovering RH or full actual Mobius/prime signed estimate is established.'}
    destination = d / 'integration_verification.json'
    if destination.exists():
        raise FileExistsError('Retain the successful milestone')
    snapshot = d / 'integration_snapshot'
    snapshot.mkdir(exist_ok=False)
    for n in ['run_expanded_probe.py', 'root-results/candidate_registry.json',
              'root-results/report.txt', 'SIGNED_ARITHMETIC_CONTROL.md',
              'verify_workflow_audit_integration.py']:
        target = snapshot / n; target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((BASE / n).read_bytes())
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print('30 scoped stages and four analytical extensions integrated; all 15 historical exact snapshots preserved.')
    print('36 workflow contracts pass; four generic all-integer signed bounds calibrated; actual RH inequality remains unproved.')


if __name__ == '__main__':
    main()
