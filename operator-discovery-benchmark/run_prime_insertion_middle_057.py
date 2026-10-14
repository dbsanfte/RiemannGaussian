"""Actual-middle source discovery with independently checked final drifts."""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import json
import multiprocessing as mp
import os
import resource
import time

import run_prime_insertion_core_056 as PRIOR
from run_fractional_prime_kernel_051 import write, emit, check_receipt
import prime_insertion_middle_search_057 as SEARCH
import prime_insertion_search_055 as INTERVAL
from run_prime_insertion_055 import independent_energy, independent_forcing

ROOT = Path(__file__).resolve().parent
OUT = PRIOR.OUT/'middle_followup_001'
ALPHA = '1/5'
TRAIN = [n for n in range(3, 34) if n != 19]+[47, 71, 107, 163, 233]
FINAL = [19, 37, 61, 97, 149, 211, 307, 419]
FILES = ['prime_insertion_middle_source_057.py', 'test_prime_insertion_middle_source_057.py',
    'prime_insertion_middle_source_057_development.json', 'PRIME_INSERTION_MIDDLE_SOURCE_SCOPE_057.txt',
    'check_prime_insertion_middle_057.py', 'test_check_prime_insertion_middle_057.py',
    'check_prime_insertion_middle_057_development.json', 'PRIME_INSERTION_MIDDLE_CHECK_SCOPE_057.txt',
    'PRIME_INSERTION_MIDDLE_REVIEW_057.txt', 'prime_insertion_middle_search_057.py',
    'test_prime_insertion_middle_search_057.py', 'prime_insertion_middle_search_057_development.json',
    'run_prime_insertion_middle_057.py', 'test_prime_insertion_middle_runner_057.py',
    'prime_insertion_middle_runner_057_development.json', 'prime_insertion_middle_protocol_057.txt']
SOURCE_METER = SOURCE_CONTEXT = None
WORKER_FEATURES = None
SCORING = None


def validate_parent():
    counts = PRIOR.validate_parent()
    snapshots = list((PRIOR.OUT/'source_snapshot').iterdir())
    if len(snapshots) != len(PRIOR.FILES) or any((ROOT/p.name).read_bytes() != p.read_bytes() for p in snapshots):
        raise ValueError('preserve every frozen056 source')
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if report['full_source_bound_proved'] is not False or report['RH_proved'] is not False:
        raise ValueError('preserve the open056 middle obstruction')
    return counts+[len(snapshots)]


def source_init(features):
    global SOURCE_METER, SOURCE_CONTEXT, WORKER_FEATURES
    import prime_insertion_middle_source_057 as SOURCE
    SOURCE_METER = SOURCE.Meter(cap=1_000_000_000_000, seconds=7200)
    SOURCE_CONTEXT = SOURCE.prepare_context(SOURCE_METER)
    WORKER_FEATURES = features


def source_task(task):
    import prime_insertion_middle_source_057 as SOURCE
    N, indices = task
    rows = []
    for i in indices:
        request = SEARCH.source_request(ALPHA, WORKER_FEATURES[i], N)
        value = SOURCE.evaluate(request, precision=192, meter=SOURCE_METER, context=SOURCE_CONTEXT)
        rows.append({'feature': i, 'N': N, 'value': value})
    return {'rows': rows, 'pid': os.getpid(), 'producer_counts': SOURCE_METER.counts(),
        'worker_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


def score_task(form):
    global SCORING
    if SCORING is None:
        data = json.loads((OUT/'training_score_input.json').read_text())
        SCORING = {'table': {int(n): [INTERVAL.pair(x) for x in values] for n, values in data['table'].items()},
            'decays': {d: {int(n): INTERVAL.pair(v) for n, v in values.items()} for d, values in data['decays'].items()},
            'transports': data['transports'], 'constants': list(map(Q, data['constants']))}
    meter = SEARCH.Meter(cap=100_000_000_000, seconds=7200)
    rows = SEARCH.score_form(form, SCORING['table'], TRAIN, SCORING['transports'],
        SCORING['decays'], SCORING['constants'], meter)
    return {'rows': rows, 'operations': meter.operations,
        'worker_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


def fill_sources(pool, numbers, indices, cache, costs, phase):
    tasks = [(n, [i for i in (indices[n] if isinstance(indices, dict) else indices) if (i, n) not in cache]) for n in reversed(numbers)]
    tasks = [task for task in tasks if task[1]]
    completed = 0
    for result in pool.imap_unordered(source_task, tasks, chunksize=1):
        for row in result['rows']: cache[(row['feature'], row['N'])] = row['value']
        costs[result['pid']] = {**result['producer_counts'],
            'worker_peak_rss_kib': result['worker_peak_rss_kib']}
        completed += 1
        if completed == len(tasks) or completed % 8 == 0:
            emit('middle_source_progress', phase=phase, completed=completed, groups=len(tasks))


def table_from_cache(cache, numbers, feature_count, required=None):
    # Unused final coordinates are exact zero placeholders; selected forms
    # have coefficientzero there. Target0 is always supplied and checked.
    required = list(range(feature_count)) if required is None else required
    for n in numbers:
        indices = required[n] if isinstance(required, dict) else required
        if 0 not in indices or any((i, n) not in cache for i in indices):
            raise ValueError('every used source coordinate, including target0, must exist')
    return {n: [INTERVAL.pair({k: cache[(i, n)][k] for k in ('lower', 'upper')})
        if (i, n) in cache else (Q(0), Q(0)) for i in range(feature_count)] for n in numbers}


def used_features(rows):
    return sorted({0}|{i for row in rows for i, c in enumerate(row['form']['coefficients']) if c})


def required_requests(rows, centers):
    needed = {}
    for row in rows:
        features = used_features([row])
        offsets = [s for s, w in zip((-1, 0, 1), row['transport']['weights']) if Q(w)]
        for N in centers:
            for n in [2*N, 2*N+1]+[N+s for s in offsets]:
                needed.setdefault(n, set()).update(features)
    return {n: sorted(indices) for n, indices in sorted(needed.items())}


def check_transition(row, N, parity, producer_table, checked_table, meter):
    if type(N) is not int or N < 3 or type(parity) is not int or parity not in (0, 1):
        raise ValueError('complete neighbor recurrence domain')
    form, weights = row['form'], list(map(Q, row['transport']['weights']))
    if len(weights) != 3 or any(w < 0 for w in weights) or sum(weights) != 1:
        raise ValueError('convex transport')
    offsets = [s for s, w in zip((-1, 0, 1), weights) if w]
    indices = [N+s for s in offsets]+[2*N+parity]
    intervals = {}
    for n in indices:
        produced = INTERVAL.energy(form, producer_table[n], n, meter)
        checked = independent_energy(form, checked_table[n], n)
        if not produced[0] <= checked[0] <= checked[1] <= produced[1]:
            raise ValueError('independent energy must be contained in producer')
        intervals[n] = checked
    parent = tuple(sum((w*intervals[N+s][k] for w, s in zip(weights, (-1, 0, 1)) if w), Q(0)) for k in (0, 1))
    child = intervals[2*N+parity]
    drift = (child[0]-parent[1], child[1]-parent[0])
    checked_forcing = independent_forcing(N, row['delta'], row['C'])
    producer_forcing = tuple(Q(row['C'])*x for x in INTERVAL.decay(N, row['delta'], meter))
    if not producer_forcing[0] <= checked_forcing[0] <= checked_forcing[1] <= producer_forcing[1]:
        raise ValueError('independent forcing must be contained')
    status = INTERVAL.assess(drift, checked_forcing)
    meter.charge(256**2)
    return {'id': row['id'], 'N': N, 'parity': parity, 'checked_drift': INTERVAL.interval(drift),
        'checked_forcing': INTERVAL.interval(checked_forcing), 'status': status,
        'uniform_recurrence_proved': False, 'uniform_middle_bound_proved': False,
        'RH_proved': False, 'RH_refuted': False}


def assessment(selected, rows):
    entries = [row for row in rows if row['id'] == selected['id']]
    if len(entries) != 2*len(FINAL) or {(row['N'], row['parity']) for row in entries} != {(n, r) for n in FINAL for r in (0, 1)}:
        raise ValueError('all final transitions required')
    counts = Counter(row['status'] for row in entries)
    return {'id': selected['id'], 'form': selected['form'], 'transport': selected['transport'],
        'delta': selected['delta'], 'C': selected['C'], 'archive_family': selected['archive_family'],
        'status': 'REFUTED_FIXED_RECURRENCE' if counts['FINITE_REFUTATION'] else
            'UNRESOLVED_FINITE_COMPARISONS' if counts['UNRESOLVED_INTERVAL'] else 'OPEN_AFTER_FINITE_TESTS',
        'finite_status_counts': dict(counts),
        'counterexamples': [{'N': row['N'], 'parity': row['parity']} for row in entries if row['status'] == 'FINITE_REFUTATION'],
        'uniform_recurrence_proved': False, 'uniform_middle_bound_proved': False,
        'RH_proved': False, 'RH_refuted': False}


def main():
    import check_prime_insertion_middle_057 as CHECK
    started = time.monotonic()
    if OUT.exists(): raise FileExistsError('preserve completed/failed057 run')
    counts = validate_parent()
    if set(TRAIN)&set(FINAL): raise ValueError('disjoint training/final parent transitions')
    development = sum(check_receipt(json.loads((ROOT/name).read_text())) for name in FILES if name.endswith('_development.json'))
    snapshots = {name: (ROOT/name).read_bytes() for name in FILES}
    gm = SEARCH.Meter(); grammar = SEARCH.grammar(meter=gm); features = grammar['features']
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in snapshots.items(): (OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'protocol.json', {'alpha': ALPHA, 'features': features,
            'training_centers': TRAIN, 'final_centers': FINAL, 'parities': [0, 1],
            'workers': 3, 'persistent_source_contexts': True, 'source_values_observed_before_freeze': False,
            'evaluation_separation': 'disjoint recurrence transitions; endpoint source values may overlap and are cached',
            'aggregate_memory_limit_bytes': 16*1024**3, 'module_seconds': 7200,
            'hashes_used': False, 'old_suites_or_studies_replayed': False,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES)})
        write(OUT/'grammar.json', grammar)
        emit('middle_search_grammar_frozen', forms=len(grammar['forms']), transports=len(grammar['transports']), bounds=grammar['bound_candidate_count'])
        cache, source_costs = {}, {}
        training_numbers = SEARCH.sample_numbers(TRAIN)
        with mp.get_context('fork').Pool(3, initializer=source_init, initargs=(features,)) as pool:
            fill_sources(pool, training_numbers, list(range(len(features))), cache, source_costs, 'training')
            table = table_from_cache(cache, training_numbers, len(features))
            dm = SEARCH.Meter()
            decays = {d: {n: INTERVAL.decay(n, d, dm) for n in TRAIN} for d in grammar['decay_exponents']}
            write(OUT/'training_sources.json', {'rows': [{'feature': i, 'N': n, 'value': v} for (i, n), v in sorted(cache.items())]})
            write(OUT/'training_score_input.json', {'table': {str(n): [INTERVAL.interval(v) for v in values] for n, values in table.items()},
                'decays': {d: {str(n): INTERVAL.interval(v) for n, v in values.items()} for d, values in decays.items()},
                'transports': grammar['transports'], 'constants': grammar['constants']})
            candidates, training_operations, worker_peak = [], 0, 0
            for result in pool.imap_unordered(score_task, grammar['forms'], chunksize=4):
                candidates.extend(result['rows']); training_operations += result['operations']
                worker_peak = max(worker_peak, result['worker_peak_rss_kib'])
            candidates.sort(key=lambda row: row['id'])
            write(OUT/'training_bounds.json', {'rows': candidates, 'uniform_recurrence_proved': False})
            selected = SEARCH.select(candidates)
            write(OUT/'selected.json', selected)
            emit('middle_control_archive_frozen', selected=len(selected['selected']))
            cm = CHECK.Meter(cap=2_000_000_000_000, seconds=7200)
            proofs = []
            for row in selected['selected']:
                request = SEARCH.recovery_request(ALPHA, features, row)
                certificate = SEARCH.recovery_certificate(request)
                checked = CHECK.verify_parent_recovery(request, certificate, cm)
                proofs.append({'id': row['id'], 'request': request, 'certificate': certificate,
                    'verification': checked, 'proof_attempt': SEARCH.proof_attempt(request, certificate),
                    'exact_energy_correlations': SEARCH.energy_correlations(row['form'], row['transport']['weights'])})
            write(OUT/'proof_attempts.json', {'rows': proofs, 'uniform_recurrence_proved': False})
            needed = required_requests(selected['selected'], FINAL); final_numbers = sorted(needed)
            fill_sources(pool, final_numbers, needed, cache, source_costs, 'final')
        write(OUT/'all_sources.json', {'rows': [{'feature': i, 'N': n, 'value': v} for (i, n), v in sorted(cache.items())],
            'raw_arithmetic_overlaps_prior_work': True, 'middle_integrals_are_new': True})
        producer_table = table_from_cache(cache, final_numbers, len(features), needed)
        context = CHECK.prepare_context(cm); checked_cache, final_sources = {}, []
        for index, n in enumerate(reversed(final_numbers)):
            for i in needed[n]:
                request = SEARCH.source_request(ALPHA, features[i], n)
                proposal = {k: cache[(i, n)][k] for k in ('lower', 'upper')}
                checked = CHECK.verify_middle_interval(request, proposal, cm, context)
                checked_cache[(i, n)] = checked; final_sources.append(checked)
            if index % 4 == 3 or index+1 == len(final_numbers):
                emit('middle_independent_source_progress', completed=index+1, groups=len(final_numbers))
        write(OUT/'final_source_verification.json', {'rows': final_sources, 'uniform_middle_bound_proved': False})
        checked_table = table_from_cache(checked_cache, final_numbers, len(features), needed)
        fm = SEARCH.Meter()
        final = [check_transition(row, n, r, producer_table, checked_table, fm)
            for row in selected['selected'] for n in FINAL for r in (0, 1)]
        write(OUT/'final.json', {'rows': final, 'constants_refitted': False})
        assessments = [assessment(row, final) for row in selected['selected']]
        write(OUT/'assessment.json', {'rows': assessments, 'uniform_middle_bound_proved': False})
        write(OUT/'next_search_input.json', {'schema': 'moving-middle-transport-feedback-v1',
            'source_obligations': str((PRIOR.OUT/'next_search_input.json').relative_to(ROOT)),
            'targets': assessments, 'exact_recurrence_programs': proofs,
            'paid': ['complete finite middle integral evaluator', 'coercivity and all four base cases',
                'conditional convex-neighbor induction with shifted integer tree'],
            'unpaid': 'uniform joined child/parent energy work, preserving all moving-cutoff and signed correlation terms',
            'source_review': 'PRIME_INSERTION_MIDDLE_REVIEW_057.txt',
            'refitted_constants_are_not_a_cancellation_mechanism': True,
            'uniform_middle_bound_proved': False, 'RH_proved': False})
        validate_parent()
        if any((ROOT/name).read_bytes() != data for name, data in snapshots.items()):
            raise ValueError('preserve frozen057 source bytes')
        report = {'status': 'ACTUAL_SIGNED_MIDDLE_CONTROLS_SEARCHED_UNIFORM_WORK_OPEN',
            'forms': len(grammar['forms']), 'transports': len(grammar['transports']),
            'bound_candidates': len(candidates), 'selected': assessments,
            'finite_final_statuses': dict(Counter(row['status'] for row in final)),
            'new_middle_source_values': len(cache), 'independent_final_source_values': len(final_sources),
            'producer_worker_counts': source_costs,
            'development_operations': development, 'grammar_operations': gm.operations,
            'decay_operations': dm.operations, 'training_operations': training_operations,
            'independent_checker_operations': cm.operations, 'final_operations': fm.operations,
            'elapsed_seconds': time.monotonic()-started, 'workers': 3,
            'parent_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'largest_individual_worker_peak_rss_kib': max([worker_peak]+
                [value['worker_peak_rss_kib'] for value in source_costs.values()]),
            'aggregate_memory_limit_bytes': 16*1024**3,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES),
            'hashes_used': False, 'old_suites_or_studies_replayed': False,
            'uniform_recurrence_proved': False, 'uniform_middle_bound_proved': False,
            'RH_proved': False, 'RH_refuted': False}
        write(OUT/'report.json', report)
        emit('middle_control_search_completed', elapsed_seconds=report['elapsed_seconds'], statuses=report['finite_final_statuses'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json', {'type': type(exc).__name__, 'message': str(exc),
            'elapsed_seconds': time.monotonic()-started,
            'uniform_middle_bound_proved': False, 'RH_proved': False})
        raise


if __name__ == '__main__': main()
