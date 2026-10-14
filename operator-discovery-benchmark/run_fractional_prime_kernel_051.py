"""Frozen finite search, independent arithmetic audits and conditional feedback.

The numeric selector has no proof-provider access. Proofs are attempted only
after its archive is saved. Final numbers never participate in selection.
"""
from collections import Counter
from copy import deepcopy
from pathlib import Path
import json
import multiprocessing as mp
import resource
import time

import fractional_prime_kernel_search_051 as SEARCH
import fractional_prime_kernel_051 as PROOF
import check_fractional_prime_kernel_051 as CHECK
import check_fractional_prime_kernel_values_051 as VALUES
import fractional_prime_rh_bridge_052 as BRIDGE
import check_fractional_prime_rh_bridge_052 as BRIDGE_CHECK
import run_floor_residual_transitions_050 as PRIOR

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'fractional-prime-kernel-results'/'pilot-001'
SPEC = {'grammar': {'a_denominator': 7, 'alpha_denominator': 11, 'max_candidates': 4000},
        'precision': 192, 'irregular_numbers': [81, 125, 210, 231, 385]}
TRAIN = list(range(2, 65))
FINAL = [67, 71, 97, 101, 121, 143, 169, 187, 221, 247, 289, 323, 361, 437,
         499, 512, 625, 729, 1001, 2310, 30030, 510510, 9699690]
FILES = [
    'fractional_prime_kernel_search_051.py', 'test_fractional_prime_kernel_search_051.py',
    'fractional_prime_kernel_search_051_development.json',
    'fractional_prime_kernel_051.py', 'test_fractional_prime_kernel_051.py',
    'fractional_prime_kernel_051_development.json',
    'check_fractional_prime_kernel_051.py', 'test_check_fractional_prime_kernel_051.py',
    'check_fractional_prime_kernel_051_development.json',
    'check_fractional_prime_kernel_values_051.py', 'test_check_fractional_prime_kernel_values_051.py',
    'check_fractional_prime_kernel_values_051_development.json',
    'FRACTIONAL_PRIME_KERNEL_REVIEW_051.txt',
    'fractional_prime_rh_bridge_052.py',
    'check_fractional_prime_rh_bridge_052.py', 'test_check_fractional_prime_rh_bridge_052.py',
    'check_fractional_prime_rh_bridge_052_development.json',
    'FRACTIONAL_PRIME_RH_BRIDGE_REVIEW_052.txt', 'FRACTIONAL_PRIME_RH_BRIDGE_CHECK_SCOPE_052.txt',
    'run_fractional_prime_kernel_051.py', 'test_fractional_prime_kernel_runner_051.py',
    'fractional_prime_kernel_runner_051_development.json', 'fractional_prime_kernel_protocol_051.txt']


def write(path, value):
    with path.open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True)
        f.write('\n')


def emit(event, **data):
    print(json.dumps({'event': event, **data}, sort_keys=True), flush=True)


def validate_parent():
    counts = PRIOR.validate_parent()
    snapshots = list((PRIOR.OUT/'source_snapshot').iterdir())
    if len(snapshots) != len(PRIOR.FILES) or any((ROOT/f.name).read_bytes() != f.read_bytes() for f in snapshots):
        raise ValueError('preserve frozen050 sources')
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if report['recurrence_refuted'] is not True or report['RH_refuted'] is not False:
        raise ValueError('preserve prior recurrence counterexample scope')
    return counts+[len(snapshots)]


def check_receipt(receipt):
    runs = receipt.get('invocations', receipt.get('runs'))
    if type(runs) is not list or not runs:
        raise ValueError('nonempty development invocation ledger')
    for row in runs:
        if type(row) is not dict or type(row.get('returncode')) is not int:
            raise ValueError('typed recorded invocation')
        if type(row.get('tests')) is not int or row['tests'] <= 0:
            raise ValueError('positive test count')
        if type(row.get('operations')) is not int or row['operations'] < 0:
            raise ValueError('metered development work')
    if runs[-1]['returncode'] != 0:
        raise ValueError('last development invocation must pass')
    if any(r['returncode'] != 0 for r in runs):
        if receipt.get('final_status') != 'PASS' or receipt.get('prior_failure_preserved') is not True or not receipt.get('correction'):
            raise ValueError('failed fixture requires explicit resolution')
    return sum(r['operations'] for r in runs)


def assess_proof(row, certificate, verification):
    if verification.get('verified') is not True:
        raise ValueError('independently verified proof rule')
    paid = verification['uniform_pointwise_control_proved']
    negative = row['finite_negative_witness'] is not None
    if paid and negative:
        raise ValueError('pointwise theorem conflicts with finite negative')
    if not paid and not negative:
        raise ValueError('licensed2/6/30 sign counterexample missing from complete training')
    return {'id': row['id'], 'request': row['request'], 'role': row['role'],
            'finite_status': row['finite_status'], 'certificate': certificate,
            'verification': verification, 'finite_and_symbolic_status_consistent': True}


def final_one(task):
    kernel, n = task['request'], task['n']
    pm, cm = SEARCH.Meter(cap=100_000_000), CHECK.Meter(cap=100_000_000)
    row = SEARCH.evaluate(kernel, n, meter=pm)
    checked = VALUES.verify_value(kernel, n, row, cm)
    return {'id': task['id'], 'n': n, 'producer': row, 'verification': checked,
            'producer_operations': pm.operations, 'checker_operations': cm.operations,
            'worker_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


def main():
    started = time.monotonic()
    if OUT.exists():
        raise FileExistsError('preserve completed or failed scientific application')
    prior_counts = validate_parent()
    if set(FINAL) & set(TRAIN+SPEC['irregular_numbers']):
        raise ValueError('fresh final integers must be disjoint')
    development_operations = sum(check_receipt(json.loads((ROOT/name).read_text()))
                                 for name in FILES if name.endswith('_development.json'))
    snapshots = {name: (ROOT/name).read_bytes() for name in FILES}
    gm = SEARCH.Meter()
    bank = SEARCH.grammar(SPEC['grammar'], gm)
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    for name, data in snapshots.items():
        (OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'protocol.json', {'spec': SPEC, 'training_numbers': TRAIN, 'final_numbers': FINAL,
            'archive_limit': 6, 'selection': 'unchanged SEARCH.select; no proof-provider or final-score access',
            'calibration': 'alpha1 separate from discovery selection',
            'proof_attempts': 'all3024 entries after finite archive is saved; independent checker for each',
            'final_audit': 'two workers,192-bit source and independent256-bit all-divisor checker',
            'feedback': 'for selected forward fractional kernels attach exact OPEN052 centered-error premise',
            'search_operations_limit': 20_000_000_000, 'runtime_seconds_limit': 7200,
            'memory_limit_bytes': 16*1024**3, 'search_prospective_cap_bytes': SEARCH.MAX_SEARCH_BYTES,
            'prior_frozen_source_counts': prior_counts, 'new_frozen_source_count': len(FILES),
            'hashes_used': False, 'unresolved_intervals_are_not_positive_certificates': True})
        write(OUT/'grammar.json', bank)
        emit('grammar_frozen', candidates=bank['candidate_count'], discovery=len(bank['discovery']),
             calibrations=len(bank['calibrations']), final_numbers=len(FINAL))
        sm = SEARCH.Meter()
        study = SEARCH.search(SPEC, TRAIN, sm)
        if study['grammar'] != bank:
            raise ValueError('generated bank changed after freeze')
        write(OUT/'training.json', study)
        selected = SEARCH.select(study['rows'], limit=6)
        write(OUT/'selected.json', selected)
        emit('finite_archive_frozen', eligible=selected['eligible_count'],
             selected=[{'id': r['id'], 'request': r['request']} for r in selected['selected']])
        producer_meter, checker_meter = PROOF.Meter(cap=50_000_000), CHECK.Meter(cap=50_000_000)
        proof_rows = []
        for row in study['rows']+study['calibrations']:
            certificate = PROOF.build_certificate(row['request'], producer_meter)
            verification = CHECK.verify_certificate(row['request'], certificate, checker_meter)
            proof_rows.append(assess_proof(row, certificate, verification))
        write(OUT/'proofs.json', {'rows': proof_rows, 'scope': 'all-integer pointwise control or exact sign refutation only'})
        discovery_counts = Counter(r['certificate']['branch'] for r in proof_rows if r['role'] == 'discovery')
        calibration_counts = Counter(r['certificate']['status'] for r in proof_rows if r['role'] != 'discovery')
        training_counts, cache_metadata = sm.counts(), SEARCH.CACHE.metadata()
        observed_rows = sum(r['observed_count'] for r in study['rows']+study['calibrations'])
        skipped_rows = sum(len(r['skipped_after_counterexample']) for r in study['rows']+study['calibrations'])
        # All training evidence is now on disk. Release it and the cache before
        # forking final audits, so independent work stays comfortably below16GiB.
        del study
        SEARCH.CACHE = SEARCH.KernelCache()
        final_rows = []
        tasks = [{'id': row['id'], 'request': row['request'], 'n': n}
                 for row in selected['selected'] for n in FINAL]
        with mp.get_context('fork').Pool(2) as pool:
            for row in pool.imap_unordered(final_one, tasks, chunksize=4):
                if row['producer']['finite_sign'] == 'FINITE_NEGATIVE':
                    write(OUT/'unexpected_final_counterexample.json', row)
                    raise ValueError('selected certified kernel has a negative final value')
                final_rows.append(row)
        final_rows.sort(key=lambda r: (r['id'], r['n']))
        write(OUT/'final_values.json', {'rows': final_rows, 'finite_only': True,
            'no_retuning_from_final_values': True})
        bm, bcheck = PROOF.Meter(cap=5_000_000), BRIDGE_CHECK.Meter(cap=5_000_000)
        proof_by_id = {r['id']: r for r in proof_rows}
        bridge_rows = []
        for row in selected['selected']:
            if proof_by_id[row['id']]['certificate']['branch'] != 'fractional_forward':
                continue
            request = BRIDGE.make_request(row['request'])
            cert = BRIDGE.build_certificate(request, bm)
            verified = BRIDGE_CHECK.verify_certificate(request, cert, bcheck)
            bridge_rows.append({'id': row['id'], 'request': request, 'certificate': cert, 'verification': verified})
        write(OUT/'conditional_rh_bridges.json', {'rows': bridge_rows,
            'all_centered_error_premises': 'OPEN', 'RH_proved': False})
        feedback = {'schema': 'fractional-prime-bound-feedback-v1',
            'parent': str((PRIOR.OUT/'next_search_input.json').relative_to(ROOT)),
            'pointwise_kernels': [{'id': row['id'], 'request': row['request'],
                'branch': proof_by_id[row['id']]['certificate']['branch']} for row in selected['selected']],
            'next_targets': [{'id': row['id'], 'request': row['request'],
                'obligation': row['certificate']['open_premise'],
                'conditional_implication': 'this exact centered error implies RH'} for row in bridge_rows],
            'search_constructions': ['centered sums retaining prime and composite cross terms',
                'telescoping or pairings that bound the centered error',
                'positive cross-scale auxiliary energies with independently bounded increments',
                'correlation reductions with new explicit acyclic arithmetic leaves'],
            'ranking_priority': ['prove stronger exponent', 'extend control uniformly in scale',
                'reduce to independently paid lemmas', 'improve finite constants'],
            'forbidden_admissions': ['pointwise kernel positivity as centered cancellation',
                'finite samples as a uniform error estimate', 'fitted leading term replacing exactM',
                'circular use of RH or an equivalent unproved premise',
                'unchanged050 recurrence already refuted at683'],
            'centered_error_bound_proved': False, 'original_floor_energy_bound_proved': False,
            'RH_proved': False, 'RH_refuted': False}
        write(OUT/'next_search_input.json', feedback)
        validate_parent()
        if any((ROOT/name).read_bytes() != data for name, data in snapshots.items()):
            raise ValueError('frozen051/052 source changed during run')
        report = {'status': 'UNIFORM_POINTWISE_KERNEL_CONTROLS_CENTERED_RH_ERROR_OPEN',
            'candidates': bank['candidate_count'], 'discovery_candidates': len(bank['discovery']),
            'calibrations': len(bank['calibrations']), 'finite_archive_eligible': selected['eligible_count'],
            'selected': [{'id': r['id'], 'request': r['request'],
                'branch': proof_by_id[r['id']]['certificate']['branch']} for r in selected['selected']],
            'discovery_proof_branch_counts': dict(discovery_counts), 'calibration_proof_counts': dict(calibration_counts),
            'training_scalar_evaluations': observed_rows, 'stopped_after_counterexample_skips': skipped_rows,
            'independent_final_scalar_checks': len(final_rows),
            'final_unresolved_sign_enclosures': sum(r['producer']['finite_sign'] == 'UNRESOLVED_SIGN' for r in final_rows),
            'pointwise_certificates_independently_checked': len(proof_rows),
            'conditional_rh_bridges': len(bridge_rows), 'centered_error_bound_proved': False,
            'original_floor_energy_bound_proved': False, 'RH_proved': False, 'RH_refuted': False,
            'grammar_operations': gm.operations, 'development_operations': development_operations,
            'training_counts': training_counts, 'training_cache': cache_metadata,
            'pointwise_proof_producer_operations': producer_meter.operations,
            'pointwise_proof_checker_operations': checker_meter.operations,
            'final_producer_operations': sum(r['producer_operations'] for r in final_rows),
            'final_checker_operations': sum(r['checker_operations'] for r in final_rows),
            'bridge_producer_operations': bm.operations, 'bridge_checker_operations': bcheck.operations,
            'parent_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'largest_individual_worker_peak_rss_kib': max((r['worker_peak_rss_kib'] for r in final_rows), default=0),
            'memory_limit_bytes': 16*1024**3, 'workers': 2,
            'prior_frozen_source_counts': prior_counts, 'new_frozen_source_count': len(FILES),
            'elapsed_seconds': time.monotonic()-started, 'hashes_used': False,
            'old_scientific_studies_or_suites_replayed': False}
        write(OUT/'report.json', report)
        emit('completed', status=report['status'], branches=dict(discovery_counts),
             final_checks=len(final_rows), elapsed_seconds=report['elapsed_seconds'])
    except Exception as error:
        write(OUT/'failure.json', {'type': type(error).__name__, 'message': str(error),
                                 'elapsed_seconds': time.monotonic()-started})
        raise


if __name__ == '__main__':
    main()
