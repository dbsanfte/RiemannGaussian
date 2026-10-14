"""Discover and test explicit RH-strength signed arithmetic inequalities.

Freeze before observation; three workers construct independently verified
sources, numerical selection sees training scores only, final inequalities
are never refit. Every unproved uniform premise remains OPEN or REFUTED.
"""
from collections import Counter
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import json
import multiprocessing as mp
import resource
import time
import numpy as np

import run_fractional_prime_kernel_051 as PRIOR
import prime_scale_source_053 as SOURCE
import prime_scale_search_053 as SEARCH
import check_prime_scale_values_053 as VALUES
import prime_scale_filter_053 as PROOF
import check_prime_scale_filter_053 as CHECK

ROOT = Path(__file__).resolve().parent
OUT = PRIOR.OUT/'scale_followup_001'
TRAIN = list(range(2, 257))+[384, 512, 768, 1024]
FINAL = [263, 389, 521, 769, 1021, 1531, 2053, 3079, 4093, 6143, 8191]
FILES = ['prime_scale_filter_053.py', 'check_prime_scale_filter_053.py',
    'test_check_prime_scale_filter_053.py', 'check_prime_scale_filter_053_development.json',
    'PRIME_SCALE_FILTER_REVIEW_053.txt', 'PRIME_SCALE_FILTER_CHECK_SCOPE_053.txt',
    'prime_scale_source_053.py', 'test_prime_scale_source_053.py', 'prime_scale_source_053_development.json',
    'prime_scale_search_053.py', 'test_prime_scale_search_053.py', 'prime_scale_search_053_development.json',
    'check_prime_scale_values_053.py', 'test_check_prime_scale_values_053.py',
    'check_prime_scale_values_053_development.json',
    'run_prime_scale_search_053.py', 'test_prime_scale_runner_053.py',
    'prime_scale_runner_053_development.json', 'prime_scale_protocol_053.txt']
write, emit = PRIOR.write, PRIOR.emit
SOURCES = {}


def validate_parent():
    counts = PRIOR.validate_parent()
    snapshots = list((PRIOR.OUT/'source_snapshot').iterdir())
    if len(snapshots) != len(PRIOR.FILES) or any((ROOT/p.name).read_bytes() != p.read_bytes() for p in snapshots):
        raise ValueError('preserve all frozen051/052 sources')
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if report['centered_error_bound_proved'] is not False or report['RH_proved'] is not False:
        raise ValueError('preserve OPEN parent arithmetic premise')
    return counts+[len(snapshots)]


def source_fields(source):
    return {k: getattr(source, k) for k in ('alpha', 'max_n', 'bits', 'mu', 'prefix_w', 'prefix_up', 'prefix_down')}


def build_source(task):
    pm = SOURCE.Meter(cap=30_000_000_000, seconds=7200)
    cm = VALUES.Meter(cap=200_000_000_000, seconds=7200)
    if task.get('previous') is None:
        source = SOURCE.make_source(task['alpha'], task['max_n'], bits=32, meter=pm)
        checked = VALUES.verify_source(source_fields(source), cm)
    else:
        old_source, old_checked = task['previous']
        source = SOURCE.extend_source(old_source, task['max_n'], pm)
        checked = VALUES.verify_source(source_fields(source), cm, old_checked)
    return {'alpha': task['alpha'], 'source': source, 'checked': checked,
        'producer_counts': pm.counts(), 'checker_operations': cm.operations,
        'worker_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


def save_source(row, phase):
    source = row['source']
    name = 'source_'+row['alpha'].replace('/', '_')+'_'+phase
    with (OUT/(name+'.npz')).open('xb') as f:
        np.savez(f, mu=source.mu, prefix_w=source.prefix_w, prefix_up=source.prefix_up, prefix_down=source.prefix_down)
    receipt = {'alpha': row['alpha'], 'phase': phase, 'source': source.metadata(),
        'independent_verification': row['checked'].metadata,
        'producer_counts': row['producer_counts'], 'checker_operations': row['checker_operations'],
        'worker_peak_rss_kib': row['worker_peak_rss_kib'],
        'array_file': name+'.npz', 'array_loading': 'numpy.load(...,allow_pickle=False)'}
    write(OUT/(name+'.json'), receipt)
    return receipt


def final_one(task):
    selected, N = task['selected'], task['N']
    request, word = selected['request'], selected['word']
    source, verified = SOURCES[request['alpha']]
    sm, pm, cm = SEARCH.Meter(), SOURCE.Meter(), VALUES.Meter(cap=200_000_000_000, seconds=7200)
    pair = SEARCH.source_value(source, word, N, {}, sm, pm)
    weight = SEARCH.bound_weight(N, request['bound']['log_power'], sm)
    C = Q(request['bound']['C'])
    target = tuple(C*x for x in weight)
    checked = VALUES.joint_filter(verified, request, N, SEARCH.interval(pair), cm)
    comparison = VALUES.check_bound(request, N, checked, SEARCH.interval(target), cm)
    producer_status = SEARCH.assess(pair, target)
    if producer_status != 'UNRESOLVED_INTERVAL' and producer_status != comparison['status']:
        raise ValueError('independent bound assessment conflicts with producer')
    return {'id': selected['id'], 'N': N, 'producer_interval': SEARCH.interval(pair),
        'producer_target': SEARCH.interval(target), 'producer_status': producer_status,
        'joint_source_verification': checked, 'bound_verification': comparison,
        'source_query_counts': pm.counts(), 'search_operations': sm.operations,
        'checker_operations': cm.operations,
        'worker_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


def summarize_candidate(selected, results):
    rows = [r for r in results if r['id'] == selected['id']]
    if {r['N'] for r in rows} != set(FINAL) or len(rows) != len(FINAL):
        raise ValueError('complete fresh-scale audit required')
    statuses = Counter(r['bound_verification']['status'] for r in rows)
    status = 'REFUTED_FIXED_UNIFORM_BOUND' if statuses['FINITE_REFUTATION'] else 'OPEN_AFTER_FINITE_TESTS'
    return {'id': selected['id'], 'request': selected['request'], 'status': status,
        'finite_status_counts': dict(statuses),
        'counterexample_scales': [r['N'] for r in rows if r['bound_verification']['status'] == 'FINITE_REFUTATION'],
        'uniform_arithmetic_bound_proved': False, 'RH_proved': False, 'RH_refuted': False}


def main():
    global SOURCES
    started = time.monotonic()
    if OUT.exists():
        raise FileExistsError('preserve completed or failed053 application')
    counts = validate_parent()
    if set(TRAIN) & set(FINAL):
        raise ValueError('fresh final scales must be disjoint')
    development_operations = sum(PRIOR.check_receipt(json.loads((ROOT/name).read_text()))
                                 for name in FILES if name.endswith('_development.json'))
    snapshots = {name: (ROOT/name).read_bytes() for name in FILES}
    gm = SEARCH.Meter()
    bank = SEARCH.grammar(meter=gm)
    max_training_source = max(w['q']**w['degree']*max(TRAIN) for w in bank['words'])
    if max_training_source > SOURCE.MAX_N:
        raise OverflowError('training source cap')
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in snapshots.items():
        (OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'protocol.json', {'training_scales': TRAIN, 'final_scales': FINAL,
            'source_bits': 32, 'training_source_maximum': max_training_source,
            'archive_size': 6, 'workers': 3, 'aggregate_memory_limit_bytes': 16*1024**3,
            'maximum_source_domain': SOURCE.MAX_N,
            'uniform_bound_template': '|T_P(N)|/alpha<=C*sqrt(N)*(1+log(N))^eta, EVERYintegerN>=2',
            'normalization': 'primitive integer coefficients, positive leading, divide by alpha',
            'source_independence': 'prime-sieve128bit producer; divisor-recurrence192bit checker, all atoms and prefixes',
            'final_independence': 'hyperbola sum of A enclosures versus joint complete floor weights;192/256bit bounds',
            'source_extension': 'only selected filters; preserve all old atoms exactly',
            'stop_rule': 'evaluate all11 fresh scales for each of6 selected bounds, with no refitting',
            'proof_order': 'numerical archive saved before conditional symbolic rule attempts',
            'root_locations_restricted': False, 'kappa_evaluated_or_fitted': False,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES),
            'source_free_metadata_preflight_operations': 259200,
            'hashes_used': False, 'old_scientific_studies_replayed': False})
        write(OUT/'grammar.json', bank)
        emit('scale_grammar_frozen', words=bank['word_count'], bound_candidates=bank['bound_candidate_count'],
             training_scales=len(TRAIN), final_scales=len(FINAL), source_maximum=max_training_source)
        source_receipts = []
        tasks = [{'alpha': a, 'max_n': max_training_source} for a in bank['spec']['alphas']]
        with mp.get_context('fork').Pool(3) as pool:
            for row in pool.imap_unordered(build_source, tasks):
                SOURCES[row['alpha']] = row['source'], row['checked']
                source_receipts.append(save_source(row, 'training'))
                emit('arithmetic_source_independently_verified', alpha=row['alpha'], maximum=row['source'].max_n)
        sm, qm = SEARCH.Meter(), SOURCE.Meter()
        study = SEARCH.search(bank, {a: pair[0] for a, pair in SOURCES.items()}, TRAIN, sm, qm)
        write(OUT/'training.json', study)
        selected = SEARCH.select(study['candidates'], 6)
        if len(selected['selected']) != 6:
            raise ValueError('six frozen bound candidates required for this pilot')
        write(OUT/'selected.json', selected)
        emit('scale_bound_archive_frozen', selected=[{'id': r['id'], 'request': r['request']} for r in selected['selected']])
        pm, cm = PROOF.Meter(), CHECK.Meter()
        proofs = []
        for row in selected['selected']:
            certificate = PROOF.build_certificate(row['request'], pm)
            verified = CHECK.verify_filter(row['request'], certificate, cm)
            proofs.append({'id': row['id'], 'request': row['request'], 'certificate': certificate, 'verification': verified})
        write(OUT/'conditional_proofs.json', {'rows': proofs, 'every_arithmetic_premise': 'OPEN'})
        needed = {}
        for row in selected['selected']:
            w = row['word']
            needed[w['alpha']] = max(needed.get(w['alpha'], 0), w['q']**w['degree']*max(FINAL))
        tasks = [{'alpha': a, 'max_n': n, 'previous': SOURCES[a]}
                 for a, n in needed.items() if n > SOURCES[a][0].max_n]
        if tasks:
            with mp.get_context('fork').Pool(3) as pool:
                for row in pool.imap_unordered(build_source, tasks):
                    SOURCES[row['alpha']] = row['source'], row['checked']
                    source_receipts.append(save_source(row, 'extension'))
                    emit('selected_source_extended_and_verified', alpha=row['alpha'], maximum=row['source'].max_n,
                         reused_through=row['source'].reused_prefix_through)
        final_rows = []
        tasks = [{'selected': row, 'N': n} for row in selected['selected'] for n in FINAL]
        with mp.get_context('fork').Pool(3) as pool:
            for row in pool.imap_unordered(final_one, tasks, chunksize=2):
                final_rows.append(row)
        final_rows.sort(key=lambda r: (r['id'], r['N']))
        write(OUT/'final.json', {'rows': final_rows, 'finite_only': True, 'constants_refitted': False})
        summaries = [summarize_candidate(r, final_rows) for r in selected['selected']]
        write(OUT/'assessment.json', {'rows': summaries, 'uniform_arithmetic_bound_proved': False,
            'RH_proved': False, 'RH_refuted': False})
        feedback = {'schema': 'prime-scale-signed-bound-feedback-v1',
            'parent': str((PRIOR.OUT/'next_search_input.json').relative_to(ROOT)),
            'next_targets': summaries,
            'exact_arithmetic_source': '-sum_(d<=q^degree*N)mu(d)*(log d)^alpha*sum_j c_j*floor(q^j*N/d)',
            'normalization': 'divide by exact alpha; primitive integer polynomial',
            'proof_grammar_additions': ['any nonzero finite scale polynomial with P(q)=0 retains RH sensitivity',
                'exact finite-head Mellin identity', 'integer-to-real transfer from paid pointwiseK bound'],
            'remaining_obligation': 'prove the actual signed source bound uniformly; algebraic mean cancellation and finite tests do not pay it',
            'next_auxiliaries': ['joint prime/cofactor pairing before absolute values',
                'telescoping or cross-scale energy increments with independent arithmetic estimates',
                'source-specific correlation inequalities with acyclic explicitly unpaid leaves'],
            'refuted_constant_policy': 'do not count a fitted largerC as discovery of a cancellation mechanism',
            'uniform_arithmetic_bound_proved': False, 'RH_proved': False}
        write(OUT/'next_search_input.json', feedback)
        validate_parent()
        if any((ROOT/name).read_bytes() != data for name, data in snapshots.items()):
            raise ValueError('frozen053 sources changed during application')
        report = {'status': 'EXPLICIT_RH_STRENGTH_FILTER_BOUNDS_TESTED_UNIFORM_PROOF_OPEN',
            'polynomials': bank['polynomials'], 'words': bank['word_count'],
            'bound_candidates': bank['bound_candidate_count'], 'training_scales': len(TRAIN),
            'training_signed_filter_values': len(bank['words'])*len(TRAIN),
            'cached_training_A_values': study['cached_A_values'],
            'selected': summaries, 'independent_final_bound_checks': len(final_rows),
            'finite_final_statuses': dict(Counter(r['bound_verification']['status'] for r in final_rows)),
            'source_extensions': len(source_receipts)-len(bank['spec']['alphas']),
            'source_verified_through': {a: v[0].max_n for a, v in sorted(SOURCES.items())},
            'grammar_operations': gm.operations, 'metadata_preflight_operations': 259200,
            'development_operations': development_operations,
            'source_producer_operations': sum(r['producer_counts']['operations'] for r in source_receipts),
            'source_checker_operations': sum(r['checker_operations'] for r in source_receipts),
            'training_search_operations': sm.operations, 'training_source_query_counts': qm.counts(),
            'proof_producer_operations': pm.operations, 'proof_checker_operations': cm.operations,
            'final_source_query_operations': sum(r['source_query_counts']['operations'] for r in final_rows),
            'final_search_operations': sum(r['search_operations'] for r in final_rows),
            'final_checker_operations': sum(r['checker_operations'] for r in final_rows),
            'parent_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'largest_individual_worker_peak_rss_kib': max([r['worker_peak_rss_kib'] for r in source_receipts+final_rows]),
            'source_persistent_array_bytes': sum(v[0].metadata()['persistent_array_bytes']+v[1].mu.nbytes+v[1].weights.nbytes for v in SOURCES.values()),
            'workers': 3, 'aggregate_memory_limit_bytes': 16*1024**3,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES),
            'elapsed_seconds': time.monotonic()-started, 'hashes_used': False,
            'kappa_evaluated_or_fitted': False, 'uniform_arithmetic_bound_proved': False,
            'centered_error_bound_proved': False, 'original_floor_energy_bound_proved': False,
            'RH_proved': False, 'RH_refuted': False, 'old_scientific_studies_replayed': False}
        write(OUT/'report.json', report)
        emit('scale_search_completed', final_statuses=report['finite_final_statuses'],
             selected_statuses=[r['status'] for r in summaries], elapsed_seconds=report['elapsed_seconds'])
    except Exception as error:
        write(OUT/'failure.json', {'type': type(error).__name__, 'message': str(error),
                                 'elapsed_seconds': time.monotonic()-started})
        raise


if __name__ == '__main__': main()
