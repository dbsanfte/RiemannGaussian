#!/usr/bin/env python3
"""Freeze and run workflow contracts; retain calibrated proof/discovery limits."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from detector_workflow_guard import require_verified_runtime, witness_derived_refutations

BASE = Path(__file__).resolve().parent
MODULES = ['test_detector_safe_evaluation', 'test_detector_safe_inference',
           'test_detector_review_planner', 'test_detector_workflow_guard',
           'test_detector_bound_diagnostics', 'test_signed_bound_calibration']
CODE = ['detector_safe_evaluation.py', 'detector_safe_inference.py',
        'detector_review_planner.py', 'detector_workflow_guard.py',
        'detector_bound_diagnostics.py', 'signed_bound_calibration.py',
        'run_detector_workflow_audit.py', 'workflow_audit_report.py'] + [n + '.py' for n in MODULES]


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def write_new(p, value):
    with Path(p).open('x') as output:
        output.write(json.dumps(value, indent=2) + '\n')


def verify_calibration(d):
    p, v = read(d / 'protocol.json'), read(d / 'verification.json')
    for n, h in p['code_sha256'].items():
        if sha(BASE / n) != h or sha(d / 'frozen_source' / n) != h:
            raise ValueError('Calibration frozen source changed')
    for n, h in v['input_sha256'].items():
        if sha(d / n) != h:
            raise ValueError('Calibration input changed')
    seal, instance, cases = read(d / 'seal.json'), read(d / 'instance_seal.json'), read(d / 'holdout_cases.json')
    if seal['protocol_sha256'] != sha(d / 'protocol.json') or seal['model_sha256'] != sha(d / 'model.json') or seal['training_sha256'] != sha(d / 'training_candidates.json'):
        raise ValueError('Calibration global seal mismatch')
    if instance['parent_seal_sha256'] != sha(d / 'seal.json') or instance['instance_candidates_sha256'] != sha(d / 'instance_candidates.json'):
        raise ValueError('Calibration instance seal mismatch')
    if cases['global_seal_sha256'] != sha(d / 'seal.json') or cases['instance_seal_sha256'] != sha(d / 'instance_seal.json'):
        raise ValueError('Calibration final cases not bound to both seals')
    if not v['all_passed'] or not all(v['checks'].values()) or v['RH_proved'] or v['actual_global_prime_signed_bound_proved']:
        raise ValueError('Calibration scope or native checks invalid')
    from signed_bound_calibration import coefficient
    for witness in v['holdout_generator_novelty_witnesses']:
        new = cases['withheld_generators'][witness['holdout_instance']]['generator']
        old = p['training_generators'][witness['training_instance']]['generator']
        x, y = coefficient(new, witness['index']), coefficient(old, witness['index'])
        if x != witness['new_value'] or y != witness['old_value'] or x == y:
            raise ValueError('Generator disjointness witness invalid')
    return v


def run(directory):
    require_verified_runtime()
    d = Path(directory).resolve()
    calibration = d / 'signed-bound-calibration'
    cv = verify_calibration(calibration)
    source_files = [BASE / 'DETECTOR_INDEPENDENCE_HANDOFF.md',
                    BASE / 'inverse-prefix-results/pilot-002/integration_verification.json']
    source_files += [p for p in sorted(d.iterdir()) if p.is_file() and p.suffix in ('.txt', '.json')]
    source_files += [p for p in sorted(calibration.iterdir()) if p.is_file()]
    protocol = {'code_sha256': {n: sha(BASE / n) for n in CODE},
                'input_sha256': {str(p): sha(p) for p in source_files},
                'contract_test_modules': MODULES,
                'known_regressions_not_fresh_holdout': True,
                'generic_calibration_has_its_own_two_seals': True,
                'calibration_blindness_is_function_data_flow_not_OS_isolation': True,
                'actual_RH_solution_probability_estimated': False,
                'actual_all_scale_signed_bound_proved': False, 'RH_proved': False}
    write_new(d / 'audit_protocol.json', protocol)
    (d / 'frozen_source').mkdir(exist_ok=False)
    for n in CODE:
        (d / 'frozen_source' / n).write_bytes((BASE / n).read_bytes())
    try:
        result = subprocess.run([sys.executable, '-m', 'unittest', '-v', *MODULES],
                                cwd=BASE, capture_output=True, text=True)
        log = result.stdout + result.stderr
        (d / 'contract_tests.txt').write_text(log)
        if result.returncode:
            raise RuntimeError('Workflow contract tests failed; retain failed audit')
        count = re.search(r'Ran (\d+) tests?', log)
        if not count:
            raise RuntimeError('Contract test count unavailable')
        exclusions = witness_derived_refutations(BASE / 'candidate-review-results/sol-6.1-round-001')
        native = {'all_passed': True, 'contract_test_cases': int(count.group(1)),
                  'test_log_sha256': sha(d / 'contract_tests.txt'),
                  'witness_derived_exclusions': exclusions,
                  'generic_calibration_signed_certificates': cv['generic_global_signed_bound_certificates'],
                  'generic_calibration_unseen_signed_instances': cv['signed_instances_with_admitted_bound'],
                  'generic_calibration_delayed_fakes_rejected': cv['delayed_control_candidates_with_finite_probe_fit'],
                  'generic_calibration_input_sha256': sha(calibration / 'verification.json'),
                  'proven_on_actual_primes': False,
                  'RH_discovery_probability_established': False,
                  'actual_all_scale_signed_bound_proved': False, 'RH_proved': False}
        write_new(d / 'audit_verification.json', native)
        from workflow_audit_report import summary, text_report
        s = summary(d)
        write_new(d / 'summary.json', s)
        (d / 'report.txt').write_text(text_report(s))
        pointer = BASE / 'workflow-audit-results/latest.json'
        pointer.write_text(json.dumps({'audit_directory': str(d)}, indent=2) + '\n')
        print(f"Workflow audit passed: {s['contract_test_cases']} contract cases; "
              f"{s['generic_signed_bound_certificates']} generic all-scale signed certificates. Actual RH estimate remains missing.")
    except Exception as exc:
        write_new(d / 'failure.json', {'error': str(exc), 'completed_files_sha256': {
            str(p.relative_to(d)): sha(p) for p in d.rglob('*') if p.is_file()},
            'audit_regressions_are_development_evidence': True})
        raise


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit-dir', type=Path, required=True)
    args = parser.parse_args()
    run(args.audit_dir)
