#!/usr/bin/env python3
"""Check frozen analytical review provenance and actual persistent counterexamples.

No producer mathematical routines or reviewer computation are imported.
Free-form prose and unresolved bounds are not certified by passing this audit.
"""
import argparse
import hashlib
import json
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path

BASE = Path(__file__).resolve().parent


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()


def ceil_power(n, power):
    p = F(power)
    if n < 1 or p < 0:
        raise ValueError('Positive base and nonnegative rational exponent required')
    if p == 0:
        return 1
    target = n ** p.numerator
    low, high = 0, 1
    while high ** p.denominator < target:
        high *= 2
    while high - low > 1:
        mid = (low + high) // 2
        if mid ** p.denominator < target:
            low = mid
        else:
            high = mid
    return high


def actual_arithmetic(X):
    # Trial prime factorization is structurally distinct from both the inverse
    # recurrence detector and the reviewer's linear sieve.
    mu = [0]
    for n in range(1, 4 * X + 1):
        rest, value, prime = n, 1, 2
        while prime * prime <= rest:
            if rest % prime == 0:
                rest //= prime
                value = -value
                if rest % prime == 0:
                    value = 0
                    break
            prime += 1
        if value and rest > 1:
            value = -value
        mu.append(value)
    M = [0]
    for value in mu[1:]:
        M.append(M[-1] + value)
    a = sum(M[n] ** 2 for n in range(X, 2 * X))
    b = sum(M[n] ** 2 for n in range(2 * X, 4 * X))
    return {'A_X': a, 'A_2X': b, 'Delta': b - 4 * a,
            'Q_4X': sum(v * v for v in mu), 'mu': mu, 'M': M}


def endpoint_certificate(program, certificate):
    assert certificate['kind'] == 'fixed_dyadic_constant_endpoint'
    X = certificate['X']
    assert type(X) is int and X >= 2 and X & (X - 1) == 0
    assert program['arithmetic_model'] == 'inverse_one'
    assert program['constant_law']['kind'] == 'constant'
    s = program['exponent_schedule']
    assert s['kind'] in ['power', 'exponential', 'factorial']
    if s['kind'] != 'factorial':
        assert F(s['power']) > 0
    # At X=2 every 0<epsilon<=1 has ceiling exactly 2, including epsilon=1.
    # Otherwise d(q)>=bit_length(X) suffices, uniformly for every later q.
    safe = 1 if X == 2 else (X.bit_length() if s['kind'] == 'factorial'
                            else X.bit_length() ** F(s['power']).denominator)
    assert type(certificate['parameter_threshold']) is int and certificate['parameter_threshold'] >= safe
    arithmetic = actual_arithmetic(X)
    for field in ['A_X', 'A_2X', 'Delta', 'Q_4X']:
        assert certificate[field] == arithmetic[field]
    C = F(program['fitted_coefficient'])
    L = ceil_power(X.bit_length(), program['log_power'])
    margin = C * X * L * arithmetic['Q_4X'] - arithmetic['Delta']
    assert F(certificate['constant_endpoint']) == C
    assert certificate['root_ceiling'] == 2 and certificate['log_ceiling'] == L
    assert F(certificate['half_gap_margin']) == margin and margin < 0
    return {'kind': certificate['kind'], 'X': X,
            'parameter_threshold': certificate['parameter_threshold'],
            'C': str(C), 'log_ceiling': L, 'half_gap_margin': str(margin),
            'A_X': arithmetic['A_X'], 'A_2X': arithmetic['A_2X'],
            'Delta': arithmetic['Delta'], 'Q_4X': arithmetic['Q_4X'],
            'covers_every_later_parameter': True,
            'actual_coefficient_count': 4 * X}


def find_certificate(review):
    if 'certificate' in review:
        return review['certificate']
    matches = [r for r in review.get('evidence', []) if isinstance(r, dict)
               and r.get('kind') == 'fixed_dyadic_constant_endpoint']
    assert len(matches) == 1
    return matches[0]


def check(directory):
    directory = Path(directory).resolve()
    protocol = read(directory / 'review_protocol.json')
    for name, h in protocol['input_sha256'].items():
        assert sha(directory / name) == h
    for name, h in protocol['code_sha256'].items():
        assert sha(BASE / name) == h == sha(directory / 'frozen_source' / name)
    assert protocol['reviews_frozen_before_independent_check']
    assert protocol['reviewer_text_is_not_a_mathematical_certificate']
    assert not protocol['new_holdout_or_detector_discovery_claimed']
    assert protocol['development_arithmetic_is_not_fresh_validation']
    assert not protocol['RH_proved']
    manifest, dispatch = map(read, [directory / 'manifest.json', directory / 'dispatch.json'])
    for name, h in manifest['source_hashes'].items():
        assert sha(name) == h
    source, cofinal = Path(manifest['source_run']), Path(manifest['cofinal_audit'])
    # These imports are read-only integrity loaders, not producer mathematics.
    from signed_gap_profile_report import summary as source_summary
    from signed_gap_cofinal_report import summary as cofinal_summary
    original = source_summary(source)
    old = cofinal_summary(cofinal)
    assert old['source_run'] == str(source)
    excluded = set(old['refuted_candidate_ids'])
    if 'prior_verified_review_round' in manifest:
        from candidate_review_report import summary
        prior = summary(manifest['prior_verified_review_round'])
        assert prior['source_run'] == str(source)
        excluded.update(prior['all_refuted_candidate_ids'])
    queue = read(source / 'proof_queue.json')['queue']
    expected = sorted((r for r in queue if r['program_id'] not in excluded),
                      key=lambda r: r['program_id'])
    count = manifest['batch_count']
    assert type(count) is int and 1 <= count <= len(expected)
    assert manifest['candidate_count'] == len(expected)
    assert manifest['requested_reviewer_model'] == dispatch['requested_reviewer_model'] == 'gpt-6.1-sol'
    assert manifest['reviewer_conclusions_require_independent_verification']
    assert not manifest['global_RH_control_proved']
    assert dispatch['manifest_sha256'] == sha(directory / 'manifest.json')
    assert dispatch['exact_formulas_frozen_before_dispatch']
    assert dispatch['reviews_are_unverified_leads_until_independently_checked']
    assert len(dispatch['agents']) == count
    checks = {'frozen_sources_and_unchanged_original_finite_results': True}
    attempts, ids, witnesses = [], set(), []
    finite_observations_checked = 0
    for i in range(1, count + 1):
        name = f'batch-{i:02d}.json'
        batch, result = read(directory / name), read(directory / f'batch-{i:02d}-review.json')
        assigned = expected[i - 1::count]
        assert batch['candidates'] == assigned and batch['batch'] == result['batch'] == i
        assert batch['manifest_sha256'] == result['input_manifest_sha256'] == sha(directory / 'manifest.json')
        assert result['input_batch_sha256'] == sha(directory / name)
        assert batch['source_run'] == str(source) and batch['original_formulas_must_not_change']
        assert batch['finite_failures_are_not_automatically_global_disproofs']
        assert result['model_requested'] == 'gpt-6.1-sol'
        dispatched = dispatch['agents'][i - 1]
        assert dispatched['batch'] == i and dispatched['input'] == name
        assert dispatched['input_sha256'] == sha(directory / name)
        assert dispatched['output'] == f'batch-{i:02d}-review.json'
        if 'development_arithmetic' in result:
            development = result['development_arithmetic']
            assert sha(BASE / development['source']) == development['sha256']
        byid = {r['program_id']: r for r in result['reviews']}
        assert len(byid) == len(result['reviews']) == len(assigned)
        assert set(byid) == {r['program_id'] for r in assigned}
        for row in assigned:
            identifier, p = row['program_id'], row['exact_program']
            review = byid[identifier]
            assert identifier not in ids
            ids.add(identifier)
            assert review['exact_program_sha256'] == digest(p) == identifier
            assert not review['original_formula_changed'] and not review['independently_verified']
            assert review['precise_claim'] and review['proof_attempt'] and review['evidence']
            disposition = review['disposition']
            # A new global proof needs its own independent mathematical backend.
            # This audit never promotes an unconstrained text claim to a theorem.
            assert disposition in ['disproved_global', 'unresolved', 'finite_counterexample']
            if disposition == 'disproved_global':
                witness = endpoint_certificate(p, find_certificate(review))
                witnesses.append(dict(witness, program_id=identifier))
                verified = 'disproved_global'
            else:
                assert review['missing_lemma']
                verified = 'unresolved'
            attempts.append({'program_id': identifier, 'batch': i,
                             'reviewer_disposition': disposition,
                             'verified_uniform_claim_disposition': verified,
                             'free_form_proof_text_certified': False,
                             'exact_formula_unchanged': True})
            # Independently check the explicit X=2 finite diagnostics in batch01.
            # A finite q failure is not promoted to a cofinal global refutation.
            for evidence in review['evidence']:
                for case in evidence.get('development_endpoint_checks', []) if isinstance(evidence, dict) else []:
                    q = case['q']
                    assert type(q) is int and q >= 1
                    s = p['exponent_schedule']
                    d = (factorial(q) if s['kind'] == 'factorial' else
                         ceil_power(q, s['power']) if s['kind'] == 'power' else
                         2 ** ceil_power(q, s['power']))
                    law = p['constant_law']
                    if law['kind'] == 'free_per_level':
                        C = F(p['fitted_constants'][str(q)]) if str(q) in p['fitted_constants'] else None
                    else:
                        k = law['kind']
                        multiplier = (1 if k == 'constant' else
                                      1 + ceil_power(q, law['power']) if k == 'power' else
                                      factorial(q) if k == 'factorial' else
                                      2 ** ceil_power(q, law['power']) if k == 'exponential' else
                                      ceil_power(d, law['power']))
                        C = F(p['fitted_coefficient']) * multiplier
                    if C is None:
                        assert case.get('missing', False)
                    else:
                        margin = 12 * C * ceil_power(3, p['log_power']) - 6
                        assert F(case['C']) == C and F(case['half_gap_margin_at_X_2']) == margin
                        if 'D' in case:
                            assert F(case['D']) == 4 * C * ceil_power(3, p['log_power'])
                        assert case.get('X', 2) == 2 and case.get('level', q) == q
                        assert case['failure'] == (margin < 0)
                        assert not case['global_disproof_from_this_fixed_q']
                    finite_observations_checked += 1
    assert len(ids) == len(expected)
    checks['deterministic_complete_partition_and_review_exact_formula_hashes'] = True
    checks['independent_prime_factorization_and_every_parameter_counterexample_certificates'] = True
    checks['finite_level_failures_unresolved_arguments_and_no_text_only_theorem_promotion'] = True
    all_refuted = sorted(excluded | {w['program_id'] for w in witnesses})
    outcome = {'schema': 1, 'protocol_sha256': sha(directory / 'review_protocol.json'),
               'checker_sha256': sha(BASE / 'check_candidate_reviews.py'),
               'checks': checks, 'all_passed': all(checks.values()),
               'source_run': str(source), 'reviewed_candidate_count': len(ids),
               'verified_new_global_refutations': len(witnesses),
               'new_refuted_candidate_ids': sorted(w['program_id'] for w in witnesses),
               'all_refuted_candidate_ids': all_refuted,
               'original_queue_candidate_count': len(queue),
               'remaining_uniform_half_gap_claims': len(queue) - len(all_refuted),
               'original_fresh_half_gap_passes': original['fresh_half_gap_passes'],
               'attempts': attempts, 'verified_witnesses': witnesses,
               'finite_development_observations_independently_checked': finite_observations_checked,
               'other_reviewer_development_arithmetic_independently_verified': False,
               'reviewer_proof_text_certified': False,
               'mathematical_audit_imports_production_code': False,
               'machine_formalized': False,
               'new_global_actual_signed_upper_bounds_proved': 0,
               'uniform_RH_sufficient_signed_controls_verified': [], 'RH_proved': False}
    path = directory / 'verification.json'
    if path.exists():
        raise FileExistsError('Keep the independent review verification immutable')
    path.write_text(json.dumps(outcome, indent=2) + '\n')
    print(f'Checked {len(ids)} frozen reviews; {len(witnesses)} new global refutations; '
          f"{outcome['remaining_uniform_half_gap_claims']} source claims unresolved.")
    return outcome


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--round-dir', type=Path, required=True)
    check(parser.parse_args().round_dir)
