"""Strict scope for the separate Sol 6.1 inverse-prefix candidate reviews."""
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
    from inverse_prefix_report import summary as source_summary
    d = Path(d).resolve()
    protocol, v = read(d / 'review_protocol.json'), read(d / 'verification.json')
    parent = source_summary(protocol['source_run'])
    for n, h in protocol['code_sha256'].items():
        assert sha(BASE / n) == h == sha(d / 'frozen_source' / n)
    for n, h in protocol['input_sha256'].items():
        assert sha(n) == h
    for row in protocol['assignments']:
        assert sha(row['path']) == sha(d / 'reviewer_attempts' / Path(row['path']).name)
    assert v['review_protocol_sha256'] == digest(protocol)
    assert v['analytical_candidates_sha256'] == sha(d / 'analytical_candidates.json')
    assert v['all_passed'] and all(v['checks'].values())
    assert not v['mathematical_audit_imports_producer_code'] and not v['RH_proved']
    assert not v['actual_all_scale_signed_bound_proved'] and not v['reviewer_prose_fully_certified']
    return {'status': 'verified_bounded_components_and_stored_fit_refutations',
            'review_directory': str(d), 'source_run': protocol['source_run'],
            'requested_reviewer_model': 'gpt-6.1-sol', 'parallel_reviewers': len(protocol['assignments']),
            'reviewed_candidates': len(v['actual_witnesses']),
            'globally_bounded_potentials_verified': len(v['native_certificates']),
            'actual_signed_witnesses': v['actual_witnesses'],
            'stored_level_inequalities_refuted': len(v['stored_level_counterexamples']),
            'original_existential_cofinal_claims_unresolved': len(v['actual_witnesses']),
            'free_constant_baseline_equivalence_proved': True,
            'development_arithmetic_not_fresh_validation': True,
            'original_finite_outcomes_unchanged': True,
            'original_fresh_potential_finite_passes': parent['fresh_potential_finite_passes'],
            'original_fresh_potential_finite_cases': parent['fresh_potential_finite_cases'],
            'verified_checks': len(v['checks']), 'verification_sha256': sha(d / 'verification.json'),
            'reviewer_prose_fully_certified': False, 'machine_formalized': False,
            'uniform_RH_sufficient_signed_controls_verified': [],
            'actual_all_scale_signed_bound_proved': False, 'RH_proved': False}


def load_latest():
    p = BASE / 'inverse-prefix-results/review-latest.json'
    return summary(read(p)['review_directory']) if p.exists() else {'status': 'not_run'}


def text_report(s):
    return '\n'.join(['Separate Sol 6.1 analytical reviews of exact inverse-prefix potential leads',
        f"Parallel reviewers: {s['parallel_reviewers']}; exact sealed leads: {s['reviewed_candidates']}.",
        'For slot one, B_(k,1)(X)=X M(floor((4X-1)^(1/k)))^2 at every integer X>=1, k>=2.',
        'Normalizing power p>=1+2/k gives a globally bounded nonnegative feature. All selected potentials are bounded; the nonempty ones tend to zero.',
        'Their free-constant cofinal innovation claims are equivalent to the baseline signed-defect claim up to additive constants. This proves no actual critical signed estimate.',
        f"Exact actual witnesses: {[(r['X'], r['innovation']) for r in s['actual_signed_witnesses']]}; stored-level inequalities refuted: {s['stored_level_inequalities_refuted']}.",
        'The hypothetical common constant 2^-64 at all large q is also refuted. Later constants in the ORIGINAL existential family are unknown, so its three global claims remain unresolved.',
        f"Original fresh finite passes remain {s['original_fresh_potential_finite_passes']}/{s['original_fresh_potential_finite_cases']}. Review arithmetic is development evidence, not fresh validation.",
        f"Independent audit groups: {s['verified_checks']}. Only the typed bounds and witnesses are admitted; full reviewer prose is not certified or machine formalized.",
        'The full actual all-scale signed innovation inequality remains unproved. RH proved: false.', ''])
