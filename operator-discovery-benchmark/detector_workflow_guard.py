#!/usr/bin/env python3
"""Safe runtime boundary and witness-derived exclusions for frozen workflows."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parent


def require_verified_runtime():
    if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE', '') not in ('', '0'):
        raise RuntimeError('Verified detector workflows require assertions enabled; optimized Python is unsupported')


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def digest(v):
    return hashlib.sha256(json.dumps(v, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def require_unsealed_destination(directory):
    require_verified_runtime()
    d = Path(directory).resolve()
    protected = ('seal.json', 'verification.json', 'analytical_verification.json',
                 'candidate_batch.json', 'validation.json', 'proof_queue.json', 'failure.json',
                 'review_protocol.json', 'collection.json', 'integration_verification.json')
    if any((d / n).exists() for n in protected):
        raise FileExistsError('Retain existing evidence; discovery worker requires an unused destination')
    if not (d / 'protocol.json').is_file():
        raise FileNotFoundError('A frozen protocol is required before discovery')
    return d


def witness_derived_refutations(directory, verification=None):
    """Recompute promotion IDs from frozen typed attempts, never count alone."""
    require_verified_runtime()
    from candidate_review_report import summary
    from signed_gap_cofinal_report import summary as cofinal_summary
    from check_candidate_reviews import endpoint_certificate, find_certificate
    d = Path(directory).resolve()
    legacy = summary(d)
    m = read(d / 'manifest.json')
    v = read(d / 'verification.json') if verification is None else verification
    source = Path(m['source_run'])
    queue = read(source / 'proof_queue.json')['queue']
    programs = {r['program_id']: r['exact_program'] for r in queue}
    if len(programs) != len(queue) or legacy['original_queue_candidate_count'] != len(queue):
        raise ValueError('Original queue count or uniqueness differs from the frozen source')
    if v['original_queue_candidate_count'] != len(queue):
        raise ValueError('Reported queue count differs from the frozen source')
    predecessor = set(cofinal_summary(m['cofinal_audit'])['refuted_candidate_ids'])
    if m.get('prior_verified_review_round'):
        predecessor.update(witness_derived_refutations(m['prior_verified_review_round'])['all_refuted_candidate_ids'])
    native = []
    for i in range(1, m['batch_count'] + 1):
        batch = read(d / f'batch-{i:02d}.json')
        result = read(d / f'batch-{i:02d}-review.json')
        assigned = {r['program_id']: r for r in batch['candidates']}
        for attempt in result['reviews']:
            pid = attempt['program_id']
            if pid not in assigned or pid not in programs or digest(programs[pid]) != pid:
                raise ValueError('Review candidate identity does not match the frozen source')
            if attempt['exact_program_sha256'] != pid or assigned[pid]['exact_program'] != programs[pid]:
                raise ValueError('Review formula changed')
            if attempt['disposition'] == 'disproved_global':
                proof = endpoint_certificate(programs[pid], find_certificate(attempt))
                native.append(dict(proof, program_id=pid))
    native_ids = {r['program_id'] for r in native}
    claimed_new, claimed_all = v['new_refuted_candidate_ids'], v['all_refuted_candidate_ids']
    if len(claimed_new) != len(set(claimed_new)) or len(claimed_all) != len(set(claimed_all)):
        raise ValueError('Duplicate refutation IDs')
    if native_ids != set(claimed_new) or native_ids | predecessor != set(claimed_all):
        raise ValueError('Refutation IDs differ from independently rechecked witnesses and predecessors')
    if v['remaining_uniform_half_gap_claims'] != len(programs) - len(native_ids | predecessor):
        raise ValueError('Remaining count differs from the witness-derived source partition')
    if sorted(native, key=lambda r: r['program_id']) != sorted(v['verified_witnesses'], key=lambda r: r['program_id']):
        raise ValueError('Recorded witnesses differ from the rechecked typed certificates')
    return {'round_directory': str(d), 'new_refuted_candidate_ids': sorted(native_ids),
            'all_refuted_candidate_ids': sorted(native_ids | predecessor),
            'independently_rechecked_witnesses': len(native),
            'remaining_uniform_half_gap_claims': len(programs) - len(native_ids | predecessor),
            'RH_proved': False}


def run_worker(directory):
    d = require_unsealed_destination(directory)
    subprocess.run([sys.executable, str(BASE / 'inverse_prefix_search.py'),
                    'worker', '--run-dir', str(d)], cwd=BASE, check=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['check-refutations', 'worker'])
    parser.add_argument('--directory', type=Path, required=True)
    args = parser.parse_args()
    require_verified_runtime()
    if args.command == 'worker':
        run_worker(args.directory)
    else:
        print(json.dumps(witness_derived_refutations(args.directory), indent=2))
