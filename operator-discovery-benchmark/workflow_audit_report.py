"""Strict scope for workflow reliability and bounded signed-discovery evidence."""
import hashlib
import json
from pathlib import Path
from detector_workflow_guard import require_verified_runtime

BASE = Path(__file__).resolve().parent


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def summary(d):
    require_verified_runtime()
    d = Path(d).resolve()
    p, v = read(d / 'audit_protocol.json'), read(d / 'audit_verification.json')
    for n, h in p['code_sha256'].items():
        if sha(BASE / n) != h or sha(d / 'frozen_source' / n) != h:
            raise ValueError('Workflow frozen code changed')
    for n, h in p['input_sha256'].items():
        if sha(n) != h:
            raise ValueError('Workflow audit input changed')
    if sha(d / 'contract_tests.txt') != v['test_log_sha256'] or not v['all_passed']:
        raise ValueError('Workflow contract test evidence mismatch')
    from run_detector_workflow_audit import verify_calibration
    cv = verify_calibration(d / 'signed-bound-calibration')
    if sha(d / 'signed-bound-calibration/verification.json') != v['generic_calibration_input_sha256']:
        raise ValueError('Calibration verification changed')
    if any(v[n] for n in ('proven_on_actual_primes', 'RH_discovery_probability_established',
                          'actual_all_scale_signed_bound_proved', 'RH_proved')):
        raise ValueError('Workflow audit overstates RH readiness')
    return {'status': 'verified_workflow_contracts_and_generic_signed_bound_calibration',
            'audit_directory': str(d), 'contract_test_cases': v['contract_test_cases'],
            'generic_signed_bound_certificates': cv['generic_global_signed_bound_certificates'],
            'unseen_signed_generator_instances': cv['signed_instances_with_admitted_bound'],
            'delayed_finite_passing_control_candidates_rejected': cv['delayed_control_candidates_with_finite_probe_fit'],
            'calibration_withheld_dimensions': cv['withheld_dimensions'],
            'witness_derived_exclusions': v['witness_derived_exclusions'],
            'new_safety_wrappers_preserve_frozen_native_experiments': True,
            'safe_wrappers_required_outside_declared_native_pilot': True,
            'new_planner_requires_external_collaboration_dispatch': True,
            'runtime_model_identity_independently_authenticated': False,
            'single_process_calibration_not_adversarial_sandbox': True,
            'calibration_generator_class_and_proof_method_supplied': True,
            'general_purpose_estimate_discovery_demonstrated': False,
            'actual_all_scale_signed_bound_proved': False,
            'RH_discovery_probability_established': False,
            'machine_formalized': False,
            'uniform_RH_sufficient_signed_controls_verified': [],
            'verification_sha256': sha(d / 'audit_verification.json'), 'RH_proved': False}


def load_latest():
    p = BASE / 'workflow-audit-results/latest.json'
    return summary(read(p)['audit_directory']) if p.exists() else {'status': 'not_run'}


def text_report(s):
    return '\n'.join(['Workflow reliability and RH-discovery readiness audit',
        f"Contract cases passed: {s['contract_test_cases']}.",
        'Reproduced and addressed: unavailable normalizer silently becoming an unnormalized energy; projection of a degenerate finite fit; optimizer-disabled checks; count-preserving refutation-ID swaps; incomplete review collection; sealed-worker overwrite through the supported entry.',
        'Safe evaluation/inference wrappers retain missing, invalid and unsupported outcomes. Native frozen source and old experiments remain unchanged. Raw legacy helpers are unsupported under optimization or outside their declared native budgets.',
        'Generic planning freezes exact formulas and claims, validates complete independent task coverage and collects atomically. Dispatch uses collaboration tools externally; receipt metadata does not authenticate runtime model identity. Proof adjudication remains a separate domain checker.',
        f"Blind calibration: {s['generic_signed_bound_certificates']} all-integer signed-bound certificates on {s['unseen_signed_generator_instances']} genuinely unseen base5/6 instances, transferred from bases2/3/4 without moment refitting. Dimensions: {s['calibration_withheld_dimensions']}.",
        f"Delayed control candidates passing finite probes and rejected globally: {s['delayed_finite_passing_control_candidates_rejected']}. Positive controls and fully unsigned methods fail the signed linear-energy criterion.",
        'The calibration supplies digit-recursive generators, a residue/moment dictionary and a block-cancellation proof method. Blindness is function/data-flow separation, not adversarial OS isolation. This does not demonstrate general-purpose theorem discovery or independence from model-chosen representations.',
        'All three current actual-zeta potential leads trained on negative-only innovations. Their small boundary scales were omitted from fitting, and the chosen bounded/vanishing corrections leave the asymptotic signed problem unchanged. Diagnostics preserve the leads without treating this weakness as a global disproof.',
        'Supported next workflow: use explicit typed evaluation; fit on a predeclared range including early dyadic boundaries and diverse signed regimes; freeze all candidates; dispatch Sol6.1 reviews; retain new proposed formulas separately; admit only independently checked domain certificates; evaluate fresh scales and parameters; preserve all outcomes.',
        'RH relevance requires an ordinary-zero bridge AND genuinely proved actual arithmetic control at all scales. A useful next candidate should identify a new tractable signed-correlation or cancellation lemma; another bounded correction is insufficient evidence of such a mechanism.',
        'This is a tested research workflow with a tractable signed-estimate calibration. Its chance of solving RH cannot be inferred from these tests. The full actual-prime/Mobius signed estimate remains unproved; verified RH-sufficient controls: 0.', ''])
