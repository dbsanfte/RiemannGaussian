#!/usr/bin/env python3
"""Freeze parallel attempts and submit narrow component/witness certificates."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import inverse_prefix_grammar as g

BASE = Path(__file__).resolve().parent
CODE = ['inverse_prefix_reviews.py', 'check_inverse_prefix_reviews.py',
        'inverse_prefix_review_report.py', 'inverse_prefix_slot_review_proof.txt']


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def write(p, value):
    Path(p).write_text(json.dumps(value, indent=2) + '\n')


def run(source, directory):
    from inverse_prefix_report import summary
    summary(source)
    source, directory = Path(source).resolve(), Path(directory).resolve()
    queue = read(source / 'proof_queue.json')
    directory.mkdir(parents=True, exist_ok=False)
    routes = BASE / 'candidate-review-results/sol-6.1-proof-routes-001'
    assignments = [('selected-baseline.json', '/root/sol61_candidate_batch01', 2),
                   ('selected-singleton.json', '/root/sol61_candidate_batch02', 512),
                   ('selected-pair.json', '/root/sol61_candidate_batch03', 512)]
    inputs = [source / n for n in ['protocol.json', 'seal.json', 'proof_queue.json',
                                 'verification.json', 'analytical_verification.json']]
    prior_failures = sorted(source.glob('parallel-review-*/failure.json'))
    inputs += prior_failures
    attempts = []
    for name, agent, X in assignments:
        path = routes / name
        attempt = read(path)
        program_id = attempt['program_id']
        row = next(r for r in queue['potential_queue'] if r['program_id'] == program_id)
        inputs.append(path)
        attempts.append({'agent': agent, 'requested_model': 'gpt-6.1-sol',
                         'path': str(path), 'program_id': program_id, 'witness_X': X,
                         'exact_program': row['exact_program']})
    protocol = {'source_run': str(source), 'input_sha256': {str(p): sha(p) for p in inputs},
                'code_sha256': {n: sha(BASE / n) for n in CODE}, 'assignments': attempts,
                'retained_failed_review_records': [str(p) for p in prior_failures],
                'selection_used_review_results': False, 'review_after_queue_seal': True,
                'development_witnesses_not_fresh_validation': True,
                'requested_model_authorized_by_user': True,
                'reviewer_prose_fully_certified': False, 'RH_proved': False}
    write(directory / 'review_protocol.json', protocol)
    (directory / 'frozen_source').mkdir()
    for n in CODE:
        (directory / 'frozen_source' / n).write_bytes((BASE / n).read_bytes())
    (directory / 'reviewer_attempts').mkdir()
    for name, _, _ in assignments:
        (directory / 'reviewer_attempts' / name).write_bytes((routes / name).read_bytes())
    native = []
    for attempt in attempts:
        X, program = attempt['witness_X'], attempt['exact_program']
        arities = sorted({2} | {t['feature']['arity'] for t in program['terms']})
        profile = g.actual_profile([X, 2 * X], arities, queue['reconstruction_inference'])
        row = next(r for r in profile['rows'] if r['X'] == X)
        value = g.innovation(program, profile['rows'], X)
        native.append({'program_id': attempt['program_id'], 'X': X,
                       'energy': row['energy'], 'child_energy': row['child_energy'],
                       'V_X': str(g.potential(program, profile['rows'], X)),
                       'V_2X': str(g.potential(program, profile['rows'], 2 * X)),
                       'innovation': str(value),
                       'bounded_slot_one_envelope_admitted': True,
                       'exact_stored_constants_fail_at_witness': True,
                       'unknown_cofinal_constant_claim_disposition': 'unresolved',
                       'actual_all_scale_signed_bound_proved': False})
    write(directory / 'analytical_candidates.json', {
        'review_protocol_sha256': g.digest(protocol), 'certificates': native,
        'full_reviewer_prose_certified': False, 'RH_proved': False})
    subprocess.run([sys.executable, str(BASE / 'check_inverse_prefix_reviews.py'),
                    '--review-dir', str(directory)], cwd=BASE, check=True)
    from inverse_prefix_review_report import summary as reviewed, text_report
    result = reviewed(directory)
    write(directory / 'summary.json', result)
    (directory / 'report.txt').write_text(text_report(result))
    write(BASE / 'inverse-prefix-results/review-latest.json', {'review_directory': str(directory)})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--review-dir', type=Path, required=True)
    args = parser.parse_args()
    run(args.source, args.review_dir)
