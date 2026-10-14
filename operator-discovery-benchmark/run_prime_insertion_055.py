"""Discover auxiliaries for a fixed signed target, with exact OPEN proof leaves."""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import json
import multiprocessing as mp
import resource
import time
import numpy as np
from flint import arb, ctx

import run_prime_scale_dense_054 as PRIOR
from run_fractional_prime_kernel_051 import write, emit, check_receipt
import prime_insertion_search_055 as SEARCH
import prime_insertion_argument_055 as ARGUMENT

ROOT = Path(__file__).resolve().parent
OUT = PRIOR.OUT/'insertion_followup_001'
ALPHA, SCALE, COEFFICIENTS = '1/5', 2, [2, -3, 1]
TRAIN = list(range(2, 129))+[191, 257, 383, 509]
FINAL = [131, 193, 263, 389, 521, 769, 1013]
FILES = ['prime_insertion_source_055.py', 'test_prime_insertion_source_055.py',
    'prime_insertion_source_055_development.json', 'check_prime_insertion_055.py',
    'test_check_prime_insertion_055.py', 'check_prime_insertion_055_development.json',
    'PRIME_INSERTION_CHECK_SCOPE_055.txt', 'PRIME_INSERTION_AUXILIARY_REVIEW_055.txt',
    'prime_insertion_search_055.py', 'prime_insertion_argument_055.py',
    'test_prime_insertion_search_055.py', 'prime_insertion_search_055_development.json',
    'run_prime_insertion_055.py', 'test_prime_insertion_runner_055.py',
    'prime_insertion_runner_055_development.json', 'prime_insertion_protocol_055.txt']
TABLE, WEIGHTS, CONSTANTS = {}, {}, []


def validate_parent():
    counts = PRIOR.validate_parent()
    snapshots = list((PRIOR.OUT/'source_snapshot').iterdir())
    if len(snapshots) != len(PRIOR.FILES) or any((ROOT/p.name).read_bytes() != p.read_bytes() for p in snapshots):
        raise ValueError('preserve all frozen054 sources')
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if report['uniform_arithmetic_bound_proved'] is not False or report['finite_pass_count'] != 236596:
        raise ValueError('preserve dense054 finite evidence and OPEN scope')
    return counts+[len(snapshots)]


def source_fields():
    receipt = json.loads((PRIOR.OUT/'dense_1_5.json').read_text())
    metadata = receipt['dense_source']
    if metadata['alpha'] != ALPHA or metadata['max_n'] != 128000 or metadata['dyadic_bits'] != 32:
        raise ValueError('declared complete054 dense source required')
    with np.load(PRIOR.OUT/'dense_1_5.npz', allow_pickle=False) as stored:
        if set(stored.files) != {'Acenter', 'Adown', 'Aup'}:
            raise ValueError('exact dense source arrays')
        arrays = {name: stored[name] for name in stored.files}
    return {'alpha': ALPHA, 'max_n': 128000, 'bits': 32, 'metadata': metadata, **arrays}


def sample_numbers(scales):
    return sorted({x for n in scales for x in (n, 2*n, 2*n+1)})


def fill_table(bank, features, numbers, cache, meter):
    import prime_insertion_source_055 as SOURCE
    for n in numbers:
        for index, primes in enumerate(features):
            key = (index, n)
            if key not in cache:
                value = SOURCE.evaluate_filter(bank, primes, SCALE, COEFFICIENTS, n, meter)
                cache[key] = {'lower': value['lower'], 'upper': value['upper']}
    return {n: [SEARCH.pair(cache[(index, n)]) for index in range(len(features))] for n in numbers}


def score_task(form):
    meter = SEARCH.Meter()
    rows = SEARCH.score_form(form, TABLE, TRAIN, WEIGHTS, CONSTANTS, meter)
    return {'rows': rows, 'operations': meter.operations,
        'worker_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


def independent_energy(form, values, N):
    """Independent interval algebra on already checked source channels."""
    a, b = values[0]
    target_low = min(a*a, b*b) if a*b > 0 else Q(0)
    target_high = max(a*a, b*b)
    lower, upper = Q(0), Q(0)
    for coefficient, endpoints in zip(form['coefficients'], values):
        products = [coefficient*x for x in endpoints]
        lower += min(products); upper += max(products)
    aux_low = min(lower*lower, upper*upper) if lower*upper > 0 else Q(0)
    aux_high = max(lower*lower, upper*upper)
    weight = Q(form['lambda'])
    return ((target_low+weight*aux_low)/N, (target_high+weight*aux_high)/N)


def independent_forcing(N, delta, C):
    exponent, constant = Q(delta), Q(C)
    if constant == 0: return Q(0), Q(0)
    if exponent == 0: return constant, constant
    def endpoint(v):
        mantissa, power = v.man_exp(); mantissa, power = int(mantissa), int(power)
        return Q(mantissa << power) if power >= 0 else Q(mantissa, 1 << -power)
    with ctx.workprec(256):
        # Independent rational power rather than the producer's exp(-delta logN).
        value = arb(N)**(-arb(exponent.numerator)/exponent.denominator)*constant.numerator/constant.denominator
        return endpoint(value.lower()), endpoint(value.upper())


def check_transition(selected, N, parity, producer_table, checked_table, meter):
    if parity not in (0, 1) or type(parity) is not int or type(N) is not int or N < 2:
        raise ValueError('both ordinary binary branches atN>=2')
    child = 2*N+parity
    form = selected['form']
    pp = SEARCH.energy(form, producer_table[N], N, meter)
    pc = SEARCH.energy(form, producer_table[child], child, meter)
    cp = independent_energy(form, checked_table[N], N)
    cc = independent_energy(form, checked_table[child], child)
    if not (pp[0] <= cp[0] <= cp[1] <= pp[1] and pc[0] <= cc[0] <= cc[1] <= pc[1]):
        raise ValueError('independent source energies must be contained in producer intervals')
    drift = (cc[0]-cp[1], cc[1]-cp[0])
    decay = SEARCH.decay(N, selected['delta'], meter)
    C = Q(selected['C'])
    forcing = tuple(C*x for x in decay)
    checked_forcing = independent_forcing(N, selected['delta'], selected['C'])
    if not forcing[0] <= checked_forcing[0] <= checked_forcing[1] <= forcing[1]:
        raise ValueError('independent forcing enclosure must be contained')
    status = ('FINITE_PASS' if drift[1] <= checked_forcing[0] else
        'FINITE_REFUTATION' if drift[0] > checked_forcing[1] else 'UNRESOLVED_INTERVAL')
    meter.charge(256**2+256*len(form['coefficients']))
    return {'id': selected['id'], 'N': N, 'parity': parity,
        'producer_parent_energy': SEARCH.interval(pp), 'producer_child_energy': SEARCH.interval(pc),
        'checked_parent_energy': SEARCH.interval(cp), 'checked_child_energy': SEARCH.interval(cc),
        'checked_drift': SEARCH.interval(drift), 'checked_forcing': SEARCH.interval(checked_forcing),
        'status': status, 'finite_only': True, 'uniform_drift_proved': False,
        'uniform_target_bound_proved': False, 'RH_proved': False, 'RH_refuted': False}


def summarize(selected, rows):
    entries = [row for row in rows if row['id'] == selected['id']]
    expected = {(n, r) for n in FINAL for r in (0, 1)}
    if len(entries) != len(expected) or {(r['N'], r['parity']) for r in entries} != expected:
        raise ValueError('complete final parent/parity coverage required')
    counts = Counter(r['status'] for r in entries)
    return {'id': selected['id'], 'form': selected['form'], 'delta': selected['delta'], 'C': selected['C'],
        'status': 'REFUTED_FIXED_DRIFT' if counts['FINITE_REFUTATION'] else 'OPEN_AFTER_FINITE_DRIFT_TESTS',
        'finite_status_counts': dict(counts),
        'counterexamples': [{'N': r['N'], 'parity': r['parity']} for r in entries if r['status'] == 'FINITE_REFUTATION'],
        'uniform_drift_proved': False, 'uniform_target_bound_proved': False, 'RH_proved': False, 'RH_refuted': False}


def main():
    global TABLE, WEIGHTS, CONSTANTS
    import prime_insertion_source_055 as SOURCE
    import check_prime_insertion_055 as CHECK
    started = time.monotonic()
    if OUT.exists(): raise FileExistsError('preserve completed or failed055 study')
    counts = validate_parent()
    if set(TRAIN)&set(FINAL): raise ValueError('fresh final transitions required')
    development_operations = sum(check_receipt(json.loads((ROOT/name).read_text()))
        for name in FILES if name.endswith('_development.json'))
    snapshots = {name: (ROOT/name).read_bytes() for name in FILES}
    gm = SEARCH.Meter(); grammar = SEARCH.grammar(meter=gm)
    features = grammar['spec']['features']
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in snapshots.items(): (OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'protocol.json', {'alpha': ALPHA, 'scale': SCALE, 'coefficients': COEFFICIENTS,
            'source_maximum': 128000, 'features': features, 'training_parents': TRAIN, 'final_parents': FINAL,
            'parities': [0, 1], 'archive_size': 7, 'workers': 3,
            'aggregate_memory_limit_bytes': 16*1024**3,
            'prior_target_values_already_observed': True,
            'evaluation_separation': 'new auxiliary drifts; selector sees training transitions only; underlying054 target/source values are reused',
            'source_producer': 'exact Boolean insertion into checked054K, no new atoms',
            'source_checker': 'new shifted-log atoms, ordinarymu and coprime cofactor counts; cache shared across all selected endpoints',
            'selection_order': 'freeze numeric archive before conditional recovery/proof attempts or final comparisons',
            'proof_success_requires': 'the actual uniform both-parity drift, not its algebraic recovery',
            'constants_refitted_from_final': False, 'hashes_used': False,
            'old_scientific_studies_replayed': False, 'prior_frozen_source_counts': counts,
            'new_frozen_source_count': len(FILES)})
        write(OUT/'grammar.json', grammar)
        emit('insertion_grammar_frozen', forms=grammar['form_count'], bounds=grammar['bound_candidate_count'])
        pm = SOURCE.Meter(cap=50_000_000_000, seconds=7200)
        cm = CHECK.Meter(cap=200_000_000_000, seconds=7200)
        bank = SOURCE.build_insertion_sources(source_fields(), features, pm)
        source_certificates = []
        for primes in features:
            source = bank.sources[tuple(primes)]
            verification = CHECK.verify_insertion({'alpha': ALPHA, 'primes': primes}, source.certificate, cm)
            source_certificates.append({'primes': primes, 'certificate': source.certificate, 'verification': verification})
            if primes:
                with (OUT/('prefix_'+str(source.product)+'.npz')).open('xb') as f:
                    np.savez(f, Bcenter=source.Bcenter, Bdown=source.Bdown, Bup=source.Bup)
        write(OUT/'insertion_sources.json', {'bank': bank.metadata(), 'proofs': source_certificates,
            'empty_source_arrays_reused_from': str((PRIOR.OUT/'dense_1_5.npz').relative_to(ROOT))})
        cache = {}
        TABLE = fill_table(bank, features, sample_numbers(TRAIN), cache, pm)
        wm = SEARCH.Meter()
        WEIGHTS = {delta: {n: SEARCH.decay(n, delta, wm) for n in TRAIN} for delta in grammar['decay_exponents']}
        CONSTANTS = list(map(Q, grammar['constants']))
        candidates, training_operations, worker_peaks = [], 0, []
        with mp.get_context('fork').Pool(3) as pool:
            for result in pool.imap_unordered(score_task, grammar['forms'], chunksize=4):
                candidates.extend(result['rows']); training_operations += result['operations']
                worker_peaks.append(result['worker_peak_rss_kib'])
        candidates.sort(key=lambda r: r['id'])
        write(OUT/'training.json', {'candidates': candidates,
            'source_values': [{'feature': i, 'N': n, **value} for (i, n), value in sorted(cache.items())],
            'finite_only': True})
        selected = SEARCH.select(candidates, 7)
        if not selected['selected']: raise ValueError('no eligible auxiliary archive')
        write(OUT/'selected.json', selected)
        emit('insertion_auxiliary_archive_frozen', selected=[{'id': r['id'], 'C': r['C'], 'delta': r['delta'],
            'coefficients': r['form']['coefficients'], 'lambda': r['form']['lambda']} for r in selected['selected']])
        proofs = []
        for row in selected['selected']:
            request = ARGUMENT.energy_request(ALPHA, features, row)
            certificate = ARGUMENT.energy_certificate(request)
            checked = CHECK.verify_energy_recovery(request, certificate, cm)
            proofs.append({'id': row['id'], 'request': request, 'certificate': certificate,
                'verification': checked, 'pointwise_attempt': ARGUMENT.pointwise_proof_attempt(request),
                'exact_remaining_drift': SEARCH.drift_polynomial(row['form'])})
        write(OUT/'proof_attempts.json', {'rows': proofs, 'uniform_drift_proved': False})
        tail_proofs = []
        for primes in features:
            request = {'alpha': ALPHA, 'primes': primes, 'tau': 8}
            certificate = ARGUMENT.tail_certificate(request)
            checked = CHECK.verify_tail_bound(request, certificate, cm)
            tail_proofs.append({'request': request, 'certificate': certificate, 'verification': checked})
        write(OUT/'uniform_tail_bounds.json', {'rows': tail_proofs, 'scope': 'all integerN>=2, only t>=8 tail',
            'complete_target_bound_proved': False, 'RH_proved': False})
        final_table = fill_table(bank, features, sample_numbers(FINAL), cache, pm)
        context = CHECK.prepare_context(cm)
        checks = {}; final_source_rows = []
        # One shared independent context avoids rebuilding common shifted atoms.
        for n in reversed(sample_numbers(FINAL)):
            for i, primes in enumerate(features):
                request = {'alpha': ALPHA, 'primes': primes, 'q': SCALE, 'coefficients': COEFFICIENTS, 'N': n}
                checked = CHECK.verify_filter_interval(request, cache[(i, n)], cm, context)
                checks[(i, n)] = (Q(checked['lower']), Q(checked['upper']))
                final_source_rows.append(checked)
        checked_table = {n: [checks[(i, n)] for i in range(len(features))] for n in sample_numbers(FINAL)}
        write(OUT/'final_source_verification.json', {'rows': final_source_rows,
            'source_atoms_overlap_earlier053_work': True, 'old_sample_bank_replayed': False})
        fm = SEARCH.Meter()
        final_rows = [check_transition(row, n, r, final_table, checked_table, fm)
            for row in selected['selected'] for n in FINAL for r in (0, 1)]
        write(OUT/'final.json', {'rows': final_rows, 'constants_refitted': False, 'finite_only': True})
        assessments = [summarize(row, final_rows) for row in selected['selected']]
        write(OUT/'assessment.json', {'rows': assessments, 'uniform_target_bound_proved': False, 'RH_proved': False})
        write(OUT/'next_search_input.json', {'schema': 'prime-insertion-drift-feedback-v1',
            'parent': str((PRIOR.OUT/'next_search_input.json').relative_to(ROOT)),
            'targets': assessments, 'exact_drift_programs': proofs,
            'paid': ['Boolean prime insertion on radical states with masks and unit terms',
                'positive-square majorant and source-free base', 'conditional both-parity recurrence recovery'],
            'unpaid': 'uniform joined arithmetic drift for each surviving exact program',
            'pointwise_only_obstruction': 'paid F upper hasN power1, whereas requested drift hasN power-delta',
            'new_analytical_reduction': {'review': 'PRIME_INSERTION_AUXILIARY_REVIEW_055.txt',
                'uniform_large_t_tail_paid': True, 'small_t_joint_arithmetic_control': 'OPEN',
                'tail_rule_executable_certificate_implemented': True,
                'uniform_tail_certificates': 'uniform_tail_bounds.json'},
            'refitted_constant_is_not_cancellation_mechanism': True,
            'uniform_target_bound_proved': False, 'RH_proved': False})
        validate_parent()
        if any((ROOT/name).read_bytes() != data for name, data in snapshots.items()):
            raise ValueError('frozen055 sources changed during application')
        report = {'status': 'INSERTION_AUXILIARIES_SEARCHED_UNIFORM_DRIFT_OPEN',
            'forms': grammar['form_count'], 'bound_candidates': grammar['bound_candidate_count'],
            'training_parent_scales': len(TRAIN), 'training_branches_per_form': 2*len(TRAIN),
            'selected': assessments, 'finite_final_statuses': dict(Counter(r['status'] for r in final_rows)),
            'independent_final_source_values': len(final_source_rows),
            'uniform_tail_bounds_checked': len(tail_proofs),
            'grammar_operations': gm.operations, 'decay_weight_operations': wm.operations,
            'training_operations': training_operations, 'source_producer_counts': pm.counts(),
            'independent_checker_operations': cm.operations, 'final_comparison_operations': fm.operations,
            'development_operations': development_operations, 'new_producer_atoms_evaluated': 0,
            'parent_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'largest_individual_worker_peak_rss_kib': max(worker_peaks),
            'workers': 3, 'aggregate_memory_limit_bytes': 16*1024**3,
            'elapsed_seconds': time.monotonic()-started, 'hashes_used': False,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES),
            'uniform_drift_proved': False, 'uniform_target_bound_proved': False,
            'RH_proved': False, 'RH_refuted': False, 'old_scientific_studies_replayed': False}
        write(OUT/'report.json', report)
        emit('insertion_auxiliary_search_completed', statuses=report['finite_final_statuses'],
            elapsed_seconds=report['elapsed_seconds'])
    except Exception as error:
        write(OUT/'failure.json', {'type': type(error).__name__, 'message': str(error),
            'elapsed_seconds': time.monotonic()-started})
        raise


if __name__ == '__main__': main()
