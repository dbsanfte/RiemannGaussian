"""Strict summary of independently checked parallel analytical review leads."""
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def summary(directory):
    directory = Path(directory).resolve()
    p = read(directory / 'review_protocol.json')
    v = read(directory / 'verification.json')
    m = read(directory / 'manifest.json')
    for n, h in p['input_sha256'].items():
        assert sha(directory / n) == h
    for n, h in p['code_sha256'].items():
        assert sha(BASE / n) == h == sha(directory / 'frozen_source' / n)
    for n, h in m['source_hashes'].items():
        assert sha(n) == h
    assert v['protocol_sha256'] == sha(directory / 'review_protocol.json')
    assert v['checker_sha256'] == sha(BASE / 'check_candidate_reviews.py')
    assert v['all_passed'] and all(v['checks'].values())
    assert not v['reviewer_proof_text_certified'] and not v['mathematical_audit_imports_production_code']
    assert v['reviewed_candidate_count'] == m['candidate_count']
    assert v['verified_new_global_refutations'] == len(v['verified_witnesses'])
    assert v['remaining_uniform_half_gap_claims'] + len(v['all_refuted_candidate_ids']) == v['original_queue_candidate_count']
    assert not v['RH_proved'] and v['uniform_RH_sufficient_signed_controls_verified'] == []
    return {'status': 'verified_parallel_analytical_reviews_and_persistent_actual_counterexamples',
            'round_directory': str(directory), 'source_run': m['source_run'],
            'requested_reviewer_model': m['requested_reviewer_model'], 'reviewer_batches': m['batch_count'],
            'reviewed_candidate_count': v['reviewed_candidate_count'],
            'verified_new_global_refutations': v['verified_new_global_refutations'],
            'new_refuted_candidate_ids': v['new_refuted_candidate_ids'],
            'all_refuted_candidate_ids': v['all_refuted_candidate_ids'],
            'original_queue_candidate_count': v['original_queue_candidate_count'],
            'remaining_uniform_half_gap_claims': v['remaining_uniform_half_gap_claims'],
            'original_fresh_half_gap_passes': v['original_fresh_half_gap_passes'],
            'finite_development_observations_independently_checked': v['finite_development_observations_independently_checked'],
            'original_formulas_fits_and_finite_passes_unchanged': True,
            'reviewer_proof_text_certified': False,
            'other_reviewer_development_arithmetic_independently_verified': False,
            'verified_checks': len(v['checks']), 'verification_sha256': sha(directory / 'verification.json'),
            'machine_formalized': False, 'new_global_actual_signed_upper_bounds_proved': 0,
            'uniform_RH_sufficient_signed_controls_verified': [], 'RH_proved': False}


def load_latest():
    p = BASE / 'candidate-review-results/latest.json'
    return summary(read(p)['round_directory']) if p.exists() else {'status': 'not_run'}


def text_report(s):
    return '\n'.join([
        'Parallel Sol 6.1 analytical review of frozen actual signed-gap candidates',
        f"Model requested: {s['requested_reviewer_model']}; batches: {s['reviewer_batches']}; exact candidates reviewed: {s['reviewed_candidate_count']}.",
        f"Independently verified new global refutations: {s['verified_new_global_refutations']}; original source claims refuted in total: {len(s['all_refuted_candidate_ids'])}; unresolved: {s['remaining_uniform_half_gap_claims']}.",
        'At actual dyadic X=2: mu(1..8)=(1,-1,-1,0,-1,1,-1,0), A(2)=1, A(4)=10, Delta=6, Q(8)=6. Every declared positive reciprocal denominator has ceil(2^epsilon)=2. An exact constant C<1/2 with L=0 violates the half-gap for EVERY parameter q>=1. These are counterexamples to fitted formulas, not RH.',
        'Assignments preserve the complete source formulas and evidence. Stable-id round-robin allocation does not nominate a numerical winner. Returned attempts are frozen before an independent certificate audit.',
        'The audit verifies provenance and typed exact counterexamples. It does not certify unresolved prose, conditional proof routes, reviewer opinions or the auxiliary large development sieve. No actual signed upper bound was proved.',
        f"Original available fresh half-gap passes remain {s['original_fresh_half_gap_passes']}; no new protected numerical holdout or operator discovery claimed.",
        f"Independent audit groups: {s['verified_checks']}; exact finite development observations checked: {s['finite_development_observations_independently_checked']}.",
        'Next proof attempts require actual signed scale forcing. Full divisor-Gram positivity already needs that signed gap on the Mobius nullspace. Conditional recurrence and zero multiplicity constraints do not supply it.',
        'Uniform RH-sufficient signed controls verified: 0. RH proved: false.', ''])
