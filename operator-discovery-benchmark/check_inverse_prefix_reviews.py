#!/usr/bin/env python3
"""Independent typed bounds and actual witnesses; no producer math imports."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from check_inverse_prefix_math import prime_mu, prefix, safe_cutoff, convolution

BASE = Path(__file__).resolve().parent


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def digest(v):
    return hashlib.sha256(json.dumps(v, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def bounded_slot_certificate(program):
    total = Q(0)
    for term in program['terms']:
        f, weight = term['feature'], Q(term['weight'])
        k, r, p = f['arity'], f['slot'], Q(f['normalizing_power'])
        if type(k) is not int or k < 2 or r != 1 or weight < 0 or p < 1 + Q(2, k):
            raise ValueError('Slot-one bounded certificate premises fail')
        total += weight
    return {'global_nonnegative_potential_upper_bound': str(4 * total),
            'all_scale_bounded_potential_proved': True,
            'free_constant_innovation_equivalent_to_baseline': True,
            'actual_signed_innovation_bound_proved': False}


def root_ceil(X, q):
    if type(X) is not int or X < 1 or type(q) is not int or q < 1:
        raise ValueError('Positive integer base and order required')
    if X == 1:
        return 1
    if q >= X.bit_length() - 1 and X & (X - 1) == 0:
        return 2
    lo, hi = 0, X
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** q >= X:
            hi = mid
        else:
            lo = mid
    return hi


def witness(program, X):
    if type(X) is not int or X < 1 or X & (X - 1):
        raise ValueError('Actual witness must use a positive dyadic X')
    a = prime_mu(8 * X)
    inverse_rows = convolution(a, [0] + [1] * (8 * X), 8 * X)
    if any(inverse_rows[n] != int(n == 1) for n in range(1, 8 * X + 1)):
        raise AssertionError('Complete actual divisor inversion failed')
    M = prefix(a)
    def V(Y):
        value = Q(0)
        for term in program['terms']:
            f, weight = term['feature'], Q(term['weight'])
            p = Q(f['normalizing_power'])
            # Current selected witness certificates use integer powers. The
            # global envelope above permits any rational satisfying its premise.
            if p.denominator != 1:
                raise ValueError('Noninteger witness normalizer needs a separate exact evaluator')
            u = safe_cutoff(Y, f['arity'])
            if u > Y:
                raise AssertionError('Slot-one cutoff exceeds block start')
            value += weight * Q(Y * M[u] ** 2, Y ** p.numerator)
        return value
    A = int(sum(M[n] ** 2 for n in range(X, 2 * X)))
    child = int(sum(M[n] ** 2 for n in range(2 * X, 4 * X)))
    vx, vc = V(X), V(2 * X)
    innovation = Q(child, 4 * X * X) - Q(A, X * X) + vc - vx
    failures = []
    for q, c in program['fitted_constants'].items():
        bound = Q(c) * root_ceil(X, int(q))
        if innovation <= bound:
            raise AssertionError('Claimed stored constant counterexample does not fail')
        failures.append({'level': int(q), 'bound': str(bound),
                         'margin': str(bound - innovation)})
    constants = set(program['fitted_constants'].values())
    if len(constants) != 1 or innovation <= X * Q(next(iter(constants))):
        raise AssertionError('Hypothetical common-constant extension not persistently refuted')
    return {'program_id': digest(program), 'X': X, 'energy': A, 'child_energy': child,
            'V_X': str(vx), 'V_2X': str(vc), 'innovation': str(innovation),
            'bounded_slot_one_envelope_admitted': True,
            'exact_stored_constants_fail_at_witness': True,
            'unknown_cofinal_constant_claim_disposition': 'unresolved',
            'actual_all_scale_signed_bound_proved': False}, failures


def audit(directory):
    directory = Path(directory).resolve()
    protocol = read(directory / 'review_protocol.json')
    source = Path(protocol['source_run'])
    queue, seal = read(source / 'proof_queue.json'), read(source / 'seal.json')
    source_protocol = read(source / 'protocol.json')
    for p, h in source_protocol['code_sha256'].items():
        if sha(BASE / p) != h or sha(source / 'frozen_source' / p) != h:
            raise AssertionError('Parent arithmetic or proof source changed')
    candidate = read(directory / 'analytical_candidates.json')
    for p, h in protocol['input_sha256'].items():
        if sha(p) != h:
            raise AssertionError('Review input changed')
    for p, h in protocol['code_sha256'].items():
        if sha(BASE / p) != h or sha(directory / 'frozen_source' / p) != h:
            raise AssertionError('Review frozen source changed')
    for p, h in seal['files'].items():
        if sha(source / p) != h:
            raise AssertionError('Original detector seal changed')
    if candidate['review_protocol_sha256'] != digest(protocol):
        raise AssertionError('Review protocol mismatch')
    if candidate['RH_proved'] or candidate['full_reviewer_prose_certified']:
        raise AssertionError('Review backend overstates proof scope')
    if protocol['selection_used_review_results'] or not protocol['development_witnesses_not_fresh_validation']:
        raise AssertionError('Post-selection review masquerades as fresh discovery')
    records, native, failures = [], [], []
    for item in protocol['assignments']:
        pid, program = item['program_id'], item['exact_program']
        sealed = next(r for r in queue['potential_queue'] if r['program_id'] == pid)
        if program != sealed['exact_program'] or digest(program) != pid:
            raise AssertionError('Review candidate differs from exact sealed program')
        attempt_path = Path(item['path'])
        if sha(attempt_path) != sha(directory / 'reviewer_attempts' / attempt_path.name):
            raise AssertionError('Frozen reviewer attempt differs')
        attempt = read(attempt_path)
        qp = attempt.get('source_queue_sha256', attempt.get('queue_sha256'))
        sp = attempt.get('source_seal_sha256', attempt.get('seal_sha256'))
        if qp != sha(source / 'proof_queue.json') or sp != sha(source / 'seal.json'):
            raise AssertionError('Reviewer did not bind the source queue and seal')
        actual_program = attempt.get('exact_program', attempt.get('exact_candidate', {}).get('exact_program'))
        if actual_program != program or attempt['program_id'] != pid:
            raise AssertionError('Reviewer exact candidate mismatch')
        if any(attempt.get(n) for n in ['RH_proved', 'actual_all_scale_signed_bound_proved',
                                        'actual_global_signed_bound_proved',
                                        'global_actual_signed_innovation_bound_proved']):
            raise AssertionError('Reviewer reports an unproved actual bound')
        observed, rows = witness(program, item['witness_X'])
        claimed = attempt.get('certificate', attempt.get('positive_witness',
                    attempt.get('witness', attempt.get('actual_tiny_constant_counterexample'))))
        if claimed:
            v = claimed.get('innovation', claimed.get('signed_innovation'))
            if v is not None and Q(v) != Q(observed['innovation']):
                raise AssertionError('Reviewer witness innovation differs')
        records.append(observed)
        native.append({'program_id': pid, **bounded_slot_certificate(program),
                       'necessary_constant_for_all_large_q': str(Q(observed['innovation']) / 2),
                       'hypothetical_constant_extension_refuted': True,
                       'extension_is_not_original_unknown_constant_claim': True})
        failures.extend({'program_id': pid, **row} for row in rows)
    if candidate['certificates'] != records:
        raise AssertionError('Backend witness certificate differs from independent actual arithmetic')
    if {r['program_id'] for r in records} != {r['program_id'] for r in queue['potential_queue']}:
        raise AssertionError('Review coverage differs from the full frozen queue')
    checks = {'frozen_code_inputs_and_attempts': True, 'sealed_candidate_equality': True,
              'independent_actual_primes_and_complete_divisor_inversion': True,
              'independent_signed_witnesses_and_constant_failures': True,
              'global_bounded_slot_one_certificate': True,
              'unknown_cofinal_constants_not_disproved': True}
    return {'all_passed': True, 'checks': checks, 'review_protocol_sha256': digest(protocol),
            'analytical_candidates_sha256': sha(directory / 'analytical_candidates.json'),
            'native_certificates': native, 'actual_witnesses': records,
            'stored_level_counterexamples': failures,
            'reviewer_prose_fully_certified': False,
            'mathematical_audit_imports_producer_code': False,
            'actual_all_scale_signed_bound_proved': False, 'RH_proved': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--review-dir', type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.review_dir)
    with (args.review_dir / 'verification.json').open('x') as output:
        output.write(json.dumps(result, indent=2) + '\n')
    print(f"Independent review passed: {len(result['actual_witnesses'])} actual witnesses, "
          f"{len(result['stored_level_counterexamples'])} stored-constant counterexamples; "
          'unknown cofinal signed bounds remain unresolved.')
