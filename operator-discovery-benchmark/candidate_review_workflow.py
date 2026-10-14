#!/usr/bin/env python3
"""Freeze parallel analytical assignments, then independently check returned leads."""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent
CODE = ['candidate_review_workflow.py', 'check_candidate_reviews.py',
        'candidate_review_report.py', 'candidate_review_proof.txt',
        'test_candidate_review_contracts.py']


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def write(p, value):
    Path(p).write_text(json.dumps(value, indent=2) + '\n')


def plan(source, cofinal, destination, workers=3, prior=None):
    from signed_gap_profile_report import summary as source_summary
    from signed_gap_cofinal_report import summary as cofinal_summary
    source, cofinal, destination = map(lambda p: Path(p).resolve(),
                                      [source, cofinal, destination])
    source_summary(source)
    previous = cofinal_summary(cofinal)
    assert previous['source_run'] == str(source)
    excluded = set(previous['refuted_candidate_ids'])
    hashes = {str(source / name): sha(source / name) for name in
              ['proof_queue.json', 'final_evaluation.json', 'verification.json']}
    hashes.update({str(cofinal / name): sha(cofinal / name) for name in
                   ['audit.json', 'verification.json']})
    if prior is not None:
        from candidate_review_report import summary
        prior = Path(prior).resolve()
        old = summary(prior)
        assert old['source_run'] == str(source)
        excluded.update(old['all_refuted_candidate_ids'])
        hashes[str(prior / 'verification.json')] = sha(prior / 'verification.json')
    rows = sorted((r for r in read(source / 'proof_queue.json')['queue']
                   if r['program_id'] not in excluded), key=lambda r: r['program_id'])
    if not rows or workers < 1:
        raise ValueError('At least one unresolved candidate and reviewer required')
    count = min(workers, len(rows))
    destination.mkdir(parents=True, exist_ok=False)
    manifest = {'schema': 1, 'source_run': str(source), 'cofinal_audit': str(cofinal),
                'source_hashes': hashes, 'requested_reviewer_model': 'gpt-6.1-sol',
                'candidate_count': len(rows), 'batch_count': count,
                'allocation': 'sort stable ids, round-robin without numerical winner selection',
                'reviewer_conclusions_require_independent_verification': True,
                'global_RH_control_proved': False}
    if prior is not None:
        manifest['prior_verified_review_round'] = str(prior)
    write(destination / 'manifest.json', manifest)
    for i in range(count):
        write(destination / f'batch-{i + 1:02d}.json',
              {'batch': i + 1, 'manifest_sha256': sha(destination / 'manifest.json'),
               'source_run': str(source), 'candidates': rows[i::count],
               'original_formulas_must_not_change': True,
               'finite_failures_are_not_automatically_global_disproofs': True,
               'review_rubric': ['check small dyadic domain boundaries as well as large scales',
                                 'attempt an exact proof or persistent cofinal counterexample',
                                 'identify circular arithmetic assumptions and missing lemmas',
                                 'keep changed formulas as separate proposals'],
               'requested_output': str(destination / f'batch-{i + 1:02d}-review.json')})
    print(f'Frozen {len(rows)} exact candidates in {count} batches for gpt-6.1-sol.')
    print('Dispatch agents through the collaboration tools; this command does not call a model.')


def finalize(directory):
    directory = Path(directory).resolve()
    manifest = read(directory / 'manifest.json')
    names = ['manifest.json', 'dispatch.json']
    for i in range(1, manifest['batch_count'] + 1):
        names += [f'batch-{i:02d}.json', f'batch-{i:02d}-review.json']
    # All attempts, including auxiliary development work, are retained unchanged.
    names += [str(p.relative_to(directory)) for p in sorted(directory.glob('work-batch-*/**/*'))
              if p.is_file()]
    protocol = {'schema': 1, 'input_sha256': {n: sha(directory / n) for n in names},
                'code_sha256': {n: sha(BASE / n) for n in CODE},
                'reviews_frozen_before_independent_check': True,
                'reviewer_text_is_not_a_mathematical_certificate': True,
                'development_arithmetic_is_not_fresh_validation': True,
                'new_holdout_or_detector_discovery_claimed': False,
                'RH_proved': False}
    if (directory / 'review_protocol.json').exists():
        raise FileExistsError('Retain the completed review round; use a fresh directory')
    write(directory / 'review_protocol.json', protocol)
    frozen = directory / 'frozen_source'
    frozen.mkdir(exist_ok=False)
    for name in CODE:
        (frozen / name).write_bytes((BASE / name).read_bytes())
    subprocess.run([sys.executable, str(BASE / 'check_candidate_reviews.py'),
                    '--round-dir', str(directory)], cwd=BASE, check=True)
    from candidate_review_report import summary, text_report
    s = summary(directory)
    write(directory / 'summary.json', s)
    (directory / 'report.txt').write_text(text_report(s))
    write(BASE / 'candidate-review-results/latest.json', {'round_directory': str(directory)})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('plan')
    p.add_argument('--source', required=True, type=Path)
    p.add_argument('--cofinal-audit', required=True, type=Path)
    p.add_argument('--round-dir', required=True, type=Path)
    p.add_argument('--workers', type=int, default=3)
    p.add_argument('--prior-review-round', type=Path)
    p = sub.add_parser('finalize')
    p.add_argument('--round-dir', required=True, type=Path)
    args = parser.parse_args()
    if args.command == 'plan':
        plan(args.source, args.cofinal_audit, args.round_dir, args.workers,
             args.prior_review_round)
    else:
        finalize(args.round_dir)
