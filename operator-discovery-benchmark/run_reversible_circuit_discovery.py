"""Freeze, search and independently audit a new reversible-circuit study."""
import argparse
import ast
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction as Q
import json
import multiprocessing
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

import reversible_divisor_circuits as L
import reversible_circuit_discovery as D

ROOT = Path(__file__).resolve().parent
TESTS = ['test_reversible_circuit_discovery', 'test_check_reversible_divisor_circuits']
ALLOCATIONS = dict(preparation=20000000, generation=5000000, discovery=55000000,
                   final=155000000, independent=215000000)
DEVELOPMENT_OPERATIONS = 281990  # Producer/workflow153434 + independent checker128556.
PRIOR_PREFIX_REVIEW_OPERATIONS = 4838
ROOT_RESERVE = 1000000
CAP = 8 * 1024 * 1024
SOURCES = ['mu', 'one', 'partial_prime_13']


def write(path, value):
    data = (D.canonical(value) + '\n').encode()
    if len(data) > CAP:
        raise OverflowError('individual artifact cap8MiB')
    with Path(path).open('xb') as handle:
        handle.write(data)


def read(path):
    with Path(path).open('rb') as handle:
        data = handle.read(CAP + 1)
    if len(data) > CAP:
        raise OverflowError('bounded input artifact')
    return json.loads(data)


def protocol():
    return dict(schema='reversible-circuit-discovery-v1', seed=90317, generated=64,
                families=D.FAMILIES, quota=16, selection_per_family=2,
                training=D.TRAIN, validation=D.VALIDATION, final=D.FINAL, levels=D.LEVELS,
                alphas=D.ALPHAS, prime_phases=D.PRIME_PHASES, sign_phases=D.SIGNS,
                conjugation_production='every fourth interleaved word uses inverse of its first convolution as its last convolution',
                selection='validation failures; conditional H cost at q12/6/3/2 including inverse and initial head; complexity; ordinal. Two per family.',
                adaptation=False, optimizer=False, final_sources=SOURCES,
                source_overlap_with_previous_research=True, final_used_for_adaptation=False,
                constants='fit training only, fixed before validation; threshold32; full finite head1..31 retained',
                conditional_cost='(1+q)^(2R)*(head_energy+4*q*C_q), conditional on unproved cofinal moment estimate',
                numerical_semantics='full divisor convolution of prefix sequence; exact rational; no omitted terms',
                recovery_theorem='restricted grammar certificate, independently checked; prose proof, no proof assistant',
                total_work=450000000, allocations=ALLOCATIONS, tests=TESTS,
                development_operations=DEVELOPMENT_OPERATIONS,
                prefix_review_operations=PRIOR_PREFIX_REVIEW_OPERATIONS, root_reserve=ROOT_RESERVE,
                max_bits=4096, max_cells=6000000, phase_seconds=7200,
                parallel_final_workers=3, total_process_memory_bytes=16 * 1024**3,
                per_process_memory_bytes=4 * 1024**3,
                hashes=False, research_attempts=1, independent_audits=1, **D.FLAGS)


def source_files():
    pending = ['run_reversible_circuit_discovery', 'reversible_circuit_discovery',
               'reversible_divisor_circuits', 'check_reversible_divisor_circuits', *TESTS]
    found = set()
    while pending:
        name = pending.pop(); path = ROOT / (name + '.py')
        if name in found or not path.is_file():
            continue
        found.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                pending.extend(item.name.split('.')[0] for item in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split('.')[0])
    return sorted(name + '.py' for name in found) + [
        'reversible_divisor_circuit_contract.txt', 'reversible_divisor_circuit_review.txt']


def freeze(directory):
    directory = Path(directory).resolve()
    if directory.exists():
        raise FileExistsError('new study directory required')
    if DEVELOPMENT_OPERATIONS <= 0:
        raise ValueError('all development receipts must precede freeze')
    names = source_files()
    if sum((ROOT / name).stat().st_size for name in names) > CAP:
        raise OverflowError('complete snapshot cap')
    directory.mkdir(); (directory / 'source_snapshot').mkdir()
    for name in names:
        (directory / 'source_snapshot' / name).write_bytes((ROOT / name).read_bytes())
    write(directory / 'source_snapshot.json', names)
    write(directory / 'protocol.json', protocol())


def frozen_source(directory):
    names = read(directory / 'source_snapshot.json')
    if names != source_files():
        raise ValueError('complete frozen dependency closure')
    for name in names:
        if (ROOT / name).read_bytes() != (directory / 'source_snapshot' / name).read_bytes():
            raise ValueError('source changed after freeze: ' + name)


def synthetic_receipt(stdout):
    found = re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$', stdout, re.M)
    if len(found) != len(TESTS) or sorted(k for k, _ in found) != sorted(TESTS):
        raise ValueError('all cumulative synthetic test receipts required')
    frozen = {k: int(v) for k, v in found}
    total = DEVELOPMENT_OPERATIONS + PRIOR_PREFIX_REVIEW_OPERATIONS + ROOT_RESERVE + sum(frozen.values())
    if total > ALLOCATIONS['preparation']:
        raise OverflowError('combined synthetic/preparation budget')
    return dict(development=DEVELOPMENT_OPERATIONS, prefix_review=PRIOR_PREFIX_REVIEW_OPERATIONS,
                root_reserve=ROOT_RESERVE, frozen=frozen, total=total)


def evaluate_one(record, values, scales, meter):
    row = dict(id=record['id'], status='available', cases=[])
    try:
        output = L.evaluate(record['program'], values, meter)
        cases = L.moments(output, scales, meter)
        head = L.initial_cost(output, meter)
        row.update(cases=cases, initial_cost=head)
    except (OverflowError, TimeoutError, MemoryError) as error:
        row.update(status='missing', reason=str(error) or type(error).__name__)
    except (ValueError, TypeError, KeyError, ZeroDivisionError) as error:
        row.update(status='invalid', reason=str(error) or type(error).__name__)
    return row


def _meter(budget):
    return L.Meter(budget, deadline=time.monotonic() + 7200)


def final_source(name, selected, budget):
    """A disjoint source allocation: no worker can spend another's work budget."""
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, hard))
    meter = _meter(budget); start, cpu = time.monotonic(), time.process_time()
    rows = []
    try:
        values = L.source(name, 2 * max(D.FINAL) - 1, meter)
        for item in selected:
            row = evaluate_one(item['record'], values, D.FINAL, meter)
            row.update(source=name, constants=item['constants'], scores=[])
            if row['status'] == 'available':
                row['scores'] = D.scores(row['cases'], item['constants'], meter)
            rows.append(row)
    except (ValueError, TypeError, KeyError, OverflowError, TimeoutError, MemoryError) as error:
        # Preserve every unattempted candidate; lack of a result is never success.
        for item in selected[len(rows):]:
            rows.append(dict(id=item['record']['id'], source=name, constants=item['constants'],
                             status='missing', reason=str(error) or type(error).__name__, cases=[], scores=[]))
    return dict(source=name, rows=rows, allocated=budget, counts=meter.counts(),
                elapsed_seconds=time.monotonic() - start, cpu_seconds=time.process_time() - cpu,
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def run(directory):
    directory = Path(directory).resolve()
    if read(directory / 'protocol.json') != protocol():
        raise ValueError('fixed protocol required')
    frozen_source(directory)
    write(directory / 'run_started.json', dict(one_search=True))
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, hard))
    start, cpu = time.monotonic(), time.process_time()
    meters = {}; worker_receipts = []
    receipt = dict(status='UNKNOWN', **D.FLAGS)
    try:
        tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=ROOT,
                               text=True, capture_output=True, timeout=300)
        test_record = dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr)
        if tests.returncode == 0:
            test_record['work'] = synthetic_receipt(tests.stdout)
        write(directory / 'tests.json', test_record)
        if tests.returncode:
            raise ValueError('frozen tests failed before research')
        generation = _meter(ALLOCATIONS['generation']); discovery = _meter(ALLOCATIONS['discovery'])
        meters.update(generation=generation, discovery=discovery)
        records = D.generate(generation); write(directory / 'candidate_batch.json', records)
        values = L.source('mu', 2 * max(D.TRAIN) - 1, discovery)
        training = []
        for record in records:
            row = evaluate_one(record, values, D.TRAIN, discovery)
            row['constants'] = D.constants(row['cases'], generation) if row['status'] == 'available' else None
            training.append(row)
        write(directory / 'training.json', training)
        # Every fit is written before the first validation response is computed.
        values = L.source('mu', 2 * max(D.VALIDATION) - 1, discovery)
        evidence = []
        for record, fitted in zip(records, training):
            row = dict(fitted); row['training_cases'] = row.pop('cases'); row['cases'] = []; row['scores'] = []
            if fitted['status'] == 'available':
                validation = evaluate_one(record, values, D.VALIDATION, discovery)
                if validation.get('initial_cost') != fitted['initial_cost'] and validation['status'] == 'available':
                    raise ValueError('fixed source/circuit head changed with horizon')
                row.update(status=validation['status'], cases=validation['cases'])
                if validation['status'] == 'available':
                    row['scores'] = D.scores(row['cases'], row['constants'], generation)
                else:
                    row['reason'] = validation['reason']
            evidence.append(row)
        write(directory / 'discovery_evidence.json', evidence)
        chosen = [records[0]] + D.choose(records, evidence, generation)
        by_id = {row['id']: row for row in evidence}
        selected = [dict(record=r, constants=by_id[r['id']]['constants']) for r in chosen]
        if any(item['constants'] is None for item in selected):
            raise ValueError('baseline and every selected candidate need complete discovery')
        write(directory / 'final_batch.json', selected)
        write(directory / 'proof_queue.json', [D.obligation(r) for r in chosen if r['id']])
        # Separate source partitions evaluate the frozen batch concurrently.
        budgets = [ALLOCATIONS['final'] // 3 + (i < ALLOCATIONS['final'] % 3) for i in range(3)]
        with ProcessPoolExecutor(max_workers=3, mp_context=multiprocessing.get_context('spawn')) as pool:
            pending = [pool.submit(final_source, name, selected, budget) for name, budget in zip(SOURCES, budgets)]
            for future in as_completed(pending):
                result = future.result()
                write(directory / ('final_source_' + result['source'] + '.json'), result)
                worker_receipts.append(result)
        worker_receipts.sort(key=lambda row: SOURCES.index(row['source']))
        final = [row for worker in worker_receipts for row in worker['rows']]
        write(directory / 'final_responses.json', final)
        generation.charge(sum(len(D.canonical(v)) // 32 + 1 for v in (records, training, evidence, selected, final)))
        receipt.update(status='CANDIDATE_LEADS', generated=len(records) - 1,
                       selected_ids=[r['id'] for r in chosen if r['id']],
                       final_available=sum(r['status'] == 'available' for r in final),
                       final_missing=sum(r['status'] == 'missing' for r in final),
                       final_invalid=sum(r['status'] == 'invalid' for r in final))
    except (ValueError, TypeError, KeyError, OverflowError, TimeoutError, MemoryError,
            subprocess.TimeoutExpired, RuntimeError) as error:
        receipt.update(reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        receipt.update(stage_counts={name: meter.counts() for name, meter in meters.items()},
                       final_workers=[{k: v for k, v in worker.items() if k != 'rows'} for worker in worker_receipts],
                       cost=dict(elapsed_seconds=time.monotonic() - start, cpu_seconds=time.process_time() - cpu,
                                 peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss))
        write(directory / 'receipt.json', receipt)
        resource.setrlimit(resource.RLIMIT_AS, (soft, hard))
    return receipt


def _independent_fit(cases, meter):
    result = {}
    for q in D.LEVELS:
        maximum = Q(0)
        for case in cases:
            k = 1
            while k ** q < case['X']:
                meter.charge(); k += 1
            maximum = max(maximum, meter.number(Q(case['energy']) / k))
        result[str(q)] = str(maximum)
    return result


def _independent_scores(cases, fitted, meter):
    result = []
    for case in cases:
        for q in D.LEVELS:
            k = 1
            while k ** q < case['X']:
                meter.charge(); k += 1
            bound = meter.number(Q(fitted[str(q)]) * k)
            result.append(dict(X=case['X'], q=q, bound=str(bound), passed=Q(case['energy']) <= bound,
                               dyadic=case['X'] & (case['X'] - 1) == 0))
    return result


def _independent_choose(records, evidence, meter):
    ranked = []
    for record, row in zip(records, evidence):
        meter.charge()
        if record['id'] and row['status'] == 'available':
            R = sum((abs(Q(s['alpha']).numerator) + Q(s['alpha']).denominator - 1) // Q(s['alpha']).denominator
                    for s in record['program']['stages'] if s['op'] == 'convolve')
            costs = tuple(meter.number((1 + q) ** (2 * R) * (Q(row['initial_cost']) + 4 * q * Q(row['constants'][str(q)])))
                          for q in (12, 6, 3, 2))
            ranked.append(((sum(not s['passed'] for s in row['scores']), costs,
                            record['complexity'], record['id']), record))
    ranked.sort(key=lambda pair: pair[0])
    return [r for family in D.FAMILIES for r in [r for _, r in ranked if r['family'] == family][:2]]


def audit(directory):
    import check_reversible_divisor_circuits as C
    directory = Path(directory).resolve()
    write(directory / 'independent_started.json', dict(one_audit=True))
    start = time.monotonic(); meter = _meter(ALLOCATIONS['independent'])
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, hard))
    result = dict(status='UNKNOWN', finite_arithmetic_verified=False, recovery_certificates_checked=False, **D.FLAGS)
    checked = certificates = 0

    def require(condition, message):
        if not condition:
            raise ValueError(message)

    def get(name):
        value = read(directory / name); meter.charge(len(D.canonical(value)) // 32 + 1)
        return value

    def verify_row(record, row, values, scales):
        nonlocal checked
        require(row['id'] == record['id'], 'ordinal program binding')
        if row['status'] != 'available':
            require(row['status'] in ('missing', 'invalid') and row.get('reason') and not row['cases'],
                    'failed whole evaluation is explicit and has no fabricated cases')
            return
        output = C.evaluate(record['program'], values, meter)
        expected = C.moments(output, scales, meter)
        require(row['cases'] == expected, 'independent complete divisor-convolution moment')
        head = Q(0)
        for n in range(1, 32):
            head = meter.number(head + Q(output[n] * output[n], n * n))
        require(row['initial_cost'] == str(head), 'complete original-head recovery cost')
        checked += len(scales)

    try:
        frozen_source(directory)
        require(get('protocol.json') == protocol(), 'complete frozen protocol')
        tests, receipt = get('tests.json'), get('receipt.json')
        require(tests['returncode'] == 0 and tests['work'] == synthetic_receipt(tests['stdout'])
                and tests['stderr'].rstrip().endswith('OK'), 'one successful frozen suite')
        require(receipt['status'] == 'CANDIDATE_LEADS', 'completed bounded research run')
        require(set(receipt['stage_counts']) == {'generation', 'discovery'}, 'all parent work counters retained')
        for stage, counts in receipt['stage_counts'].items():
            require(type(counts['operations']) is int and 0 <= counts['operations'] <= ALLOCATIONS[stage], 'shared parent budgets')
        require(all(receipt[k] is False for k in D.FLAGS), 'no unproved global admission')
        records, training, evidence = get('candidate_batch.json'), get('training.json'), get('discovery_evidence.json')
        require(records == D.generate(meter), 'full payload replay of frozen generator (shared implementation)')
        require(len(records) == len(training) == len(evidence) == 65, 'all structural outputs retained')
        for record in records:
            require(C.verify(record['certificate'], meter) is True and record['certificate']['program'] == record['program'],
                    'independent program-bound recovery certificate')
            require(record['inverse'] == L.inverse(record['program'], meter), 'declared inverse word')
            certificates += 1
        values = C.source('mu', 2 * max(D.TRAIN) - 1, meter)
        for record, row in zip(records, training):
            verify_row(record, row, values, D.TRAIN)
            if row['status'] == 'available':
                require(row['constants'] == _independent_fit(row['cases'], meter), 'training-only exact constants')
            else:
                require(row['constants'] is None, 'no constants fitted to incomplete training')
        values = C.source('mu', 2 * max(D.VALIDATION) - 1, meter)
        for record, trained, row in zip(records, training, evidence):
            require(row['training_cases'] == trained['cases'] and row['constants'] == trained['constants']
                    and row.get('initial_cost') == trained.get('initial_cost'), 'validation cannot refit')
            verify_row(record, row, values, D.VALIDATION)
            if row['status'] == 'available':
                require(trained['status'] == 'available' and row['scores'] == _independent_scores(row['cases'], row['constants'], meter),
                        'independent validation comparisons')
            else:
                require(not row['scores'], 'missing comparisons are not passes')
        chosen = [records[0]] + _independent_choose(records, evidence, meter)
        by_id = {row['id']: row for row in evidence}
        selected = [dict(record=r, constants=by_id[r['id']]['constants']) for r in chosen]
        require(get('final_batch.json') == selected, 'final selection fixed by discovery alone')
        require(get('proof_queue.json') == [D.obligation(r) for r in chosen if r['id']], 'complete unproved moment obligations')
        rows = get('final_responses.json')
        require(len(rows) == len(selected) * len(SOURCES), 'every final actual/control candidate retained')
        workers = receipt['final_workers']
        require([w['source'] for w in workers] == SOURCES and sum(w['allocated'] for w in workers) == ALLOCATIONS['final'],
                'disjoint complete parallel allocations')
        for index, name in enumerate(SOURCES):
            worker = get('final_source_' + name + '.json')
            require({k: v for k, v in worker.items() if k != 'rows'} == workers[index], 'complete parallel worker receipt')
            require(type(worker['counts']['operations']) is int and 0 <= worker['counts']['operations'] <= worker['allocated'], 'worker cannot exceed partition')
            partition = rows[index * len(selected):(index + 1) * len(selected)]
            require(partition == worker['rows'], 'all worker outcomes retained verbatim')
            values = C.source(name, 2 * max(D.FINAL) - 1, meter)
            for item, row in zip(selected, partition):
                require(row['source'] == name and row['constants'] == item['constants'], 'same fixed source and constants')
                verify_row(item['record'], row, values, D.FINAL)
                if row['status'] == 'available':
                    require(row['scores'] == _independent_scores(row['cases'], row['constants'], meter), 'independent final comparison')
                else:
                    require(not row['scores'], 'missing final has no passes')
        research_work = sum(c['operations'] for c in receipt['stage_counts'].values()) + sum(w['counts']['operations'] for w in workers)
        cumulative = tests['work']['total'] + research_work + meter.operations
        require(cumulative <= 450000000, 'whole study combined ceiling')
        result.update(status='FINITE_EVALUATION_VERIFIED', finite_arithmetic_verified=True,
                      recovery_certificates_checked=True, selected_ids=[r['id'] for r in chosen if r['id']],
                      cumulative_operations=cumulative,
                      scope='independent finite source/factor/divisor arithmetic, recovery certificate syntax and fit/selection arithmetic; generator and inverse-word replay share implementation; no moment theorem')
    except (ValueError, TypeError, KeyError, OverflowError, TimeoutError, MemoryError) as error:
        result.update(reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        result.update(cases_verified=checked, certificates_checked=certificates, counts=meter.counts(),
                      elapsed_seconds=time.monotonic() - start,
                      peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        write(directory / 'independent_verification.json', result)
        resource.setrlimit(resource.RLIMIT_AS, (soft, hard))
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['freeze', 'run', 'audit'])
    parser.add_argument('directory')
    args = parser.parse_args()
    result = globals()[args.command](args.directory)
    if result is not None:
        print(D.canonical(result))
