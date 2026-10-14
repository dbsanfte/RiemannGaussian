"""Freeze once, perform bounded discovery once, and audit once without resets."""
import argparse
import ast
from concurrent.futures import ProcessPoolExecutor, as_completed
from copy import deepcopy
from fractions import Fraction as Q
import json
import multiprocessing
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

from potential_candidate_language import Meter
import permuted_circuit_discovery as D

ROOT = Path(__file__).resolve().parent
TESTS = ['test_permuted_arithmetic_circuits', 'test_check_permuted_arithmetic_circuits',
         'test_permuted_circuit_discovery']
DEVELOPMENT = ['permuted_producer_development.json', 'permuted_checker_development.json',
               'permuted_workflow_development.json']
TOTAL = 450000000
ALLOCATIONS = dict(preparation=10000000, generation=3000000, discovery=50000000, final=140000000)
FINAL_BUDGETS = {'mu': 80000000, 'one': 30000000, 'partial_prime_13': 30000000}
ROOT_RESERVE = 1000000
CAP = 8 * 1024**2
SECONDS = 7200
FINAL_DECOMPOSITION = [8192, 16384, 32768]


class ResidentMeter(Meter):
    def live(self, cells):
        return super().live(cells + 1000000)


def read(path):
    with Path(path).open('rb') as handle:
        raw = handle.read(CAP + 1)
    if len(raw) > CAP: raise OverflowError('bounded8MiB artifact')
    return json.loads(raw)


def write(path, value):
    raw = (D.canonical(value) + '\n').encode()
    if len(raw) > CAP: raise OverflowError('bounded8MiB artifact')
    directory = Path(path).parent
    current = sum(p.stat().st_size for p in directory.iterdir() if p.suffix in ('.json', '.jsonl'))
    if current + len(raw) > CAP: raise OverflowError('aggregate8MiB retained artifacts')
    with Path(path).open('xb') as handle: handle.write(raw)


def append_checkpoint(path, row):
    raw = (D.canonical(row) + '\n').encode()
    current = sum(p.stat().st_size for p in Path(path).parent.iterdir() if p.suffix in ('.json', '.jsonl'))
    if current + len(raw) > CAP: raise OverflowError('aggregate8MiB checkpoints/artifacts')
    with Path(path).open('ab') as handle:
        handle.write(raw); handle.flush()


def development_receipts():
    result = {}
    for name in DEVELOPMENT:
        receipt = read(ROOT / name)
        if 'operations' in receipt and 'runs' in receipt:
            total, runs = receipt['operations'], receipt['runs']
        elif 'cumulative_operations' in receipt and 'invocations' in receipt:
            total, runs = receipt['cumulative_operations'], receipt['invocations']
        else: raise ValueError('explicit cumulative development receipt schema: ' + name)
        if type(total) is not int or total < 0 or not isinstance(runs, list) or not runs:
            raise ValueError('nonempty cumulative development invocation receipt')
        if any(type(r.get('operations')) is not int or r['operations'] < 0
               or type(r.get('returncode')) is not int for r in runs):
            raise ValueError('all invocation costs and returncodes retained')
        if sum(r['operations'] for r in runs) != total or runs[-1]['returncode'] != 0:
            raise ValueError('cumulative development receipt and final passed invocation')
        result[name] = receipt
    return result


def protocol():
    return dict(schema='permuted-circuit-discovery-v1', catalogue='fixed48+baseline; no RNG or response adaptation',
                families=D.FAMILIES, per_family=12, train=D.TRAIN, validation=D.VALIDATION,
                levels=D.LEVELS, sources=D.SOURCES, maps=D.MAPS, phases=D.PHASES, alphas=D.ALPHAS,
                discovery_horizons=[511, 2047], final_scales=D.FINAL_SCALES,
                final_horizons=D.FINAL_HORIZONS, final_decomposition=FINAL_DECOMPOSITION,
                final_specificity='unmatched scales; no cross-source specificity conclusion',
                selection='within family: validation failures, Pareto layer within equal-failure stratum on worst raw ratio/specificity/q12 cost, specificity, raw ratio, cost, complexity, id',
                undefined_diagnostics='ineligible; retain complete evidence',
                fit='mu training only; write before validation; q2,3,6,12',
                conditional_cost='9^P*shear_factor^2*13^(2R)*(head+48*C12); conditional, not proved',
                source_overlap_with_previous_research=True, final_used_for_adaptation=False,
                tests=TESTS, development=development_receipts(), root_reserve=ROOT_RESERVE,
                total_work=TOTAL, allocations=ALLOCATIONS,
                final_budgets=FINAL_BUDGETS,
                audit_allocation='entire remaining450m after actual preparation/reserve and research spend; no reset/retry',
                max_cells=6000000, resident_cells=1000000, max_bits=4096, seconds=SECONDS,
                aggregate_memory_bytes=16 * 1024**3, process_memory_bytes=4 * 1024**3,
                final_workers=3, max_processes=4, hashes=False, attempts=1, audits=1, **D.FLAGS)


def source_files():
    pending = ['permuted_circuit_discovery', 'run_permuted_circuit_discovery',
               'permuted_arithmetic_circuits', 'check_permuted_arithmetic_circuits', *TESTS]
    found = set()
    while pending:
        name = pending.pop(); path = ROOT / (name + '.py')
        if name in found or not path.is_file(): continue
        found.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import): pending.extend(n.name.split('.')[0] for n in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module: pending.append(node.module.split('.')[0])
    return sorted(n + '.py' for n in found) + ['permuted_circuit_contract.txt',
            'permuted_discovery_protocol.txt', 'permuted_circuit_recovery_review.txt', *DEVELOPMENT]


def freeze(directory):
    p = protocol(); names = source_files()
    if any(not (ROOT / name).is_file() for name in names): raise ValueError('complete sources/review/receipts required')
    if sum((ROOT / name).stat().st_size for name in names) > CAP: raise OverflowError('8MiB snapshot')
    directory = Path(directory).resolve()
    if directory.exists(): raise FileExistsError('new study directory required')
    directory.mkdir(); (directory / 'source_snapshot').mkdir()
    for name in names: (directory / 'source_snapshot' / name).write_bytes((ROOT / name).read_bytes())
    write(directory / 'source_snapshot.json', names); write(directory / 'protocol.json', p)


def frozen_source(directory):
    names = read(directory / 'source_snapshot.json')
    if names != source_files(): raise ValueError('complete dependency closure changed')
    for name in names:
        if (ROOT / name).read_bytes() != (directory / 'source_snapshot' / name).read_bytes():
            raise ValueError('frozen source bytes changed: ' + name)
    if read(directory / 'protocol.json') != protocol(): raise ValueError('frozen protocol changed')


def synthetic_receipt(stdout):
    pairs = re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$', stdout, re.M)
    if len(pairs) != len(TESTS) or sorted(k for k, _ in pairs) != sorted(TESTS):
        raise ValueError('exactly one cumulative receipt per frozen test module')
    development = development_receipts()
    spent = sum(r.get('operations', r.get('cumulative_operations')) for r in development.values())
    frozen = {k: int(v) for k, v in pairs}
    total = spent + sum(frozen.values()) + ROOT_RESERVE
    if total > ALLOCATIONS['preparation']: raise OverflowError('all synthetic work/preparation reserve cap')
    return dict(development=spent, frozen=frozen, root_reserve=ROOT_RESERVE, total=total)


def _meter(cap, deadline):
    return ResidentMeter(cap, deadline=deadline)


def _missing(record, source, horizon, scales, reason, status='missing'):
    return dict(id=record['evaluation_id'], source=source, horizon=horizon, scales=list(scales),
                status=status, cases=[], reason=reason)


def final_source(name, selected, cap, deadline):
    import permuted_arithmetic_circuits as P
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, hard))
    meter = _meter(cap, deadline); rows = []; started = time.monotonic()
    H, scales = D.FINAL_HORIZONS[name], D.FINAL_SCALES[name]
    cache = {}
    try:
        values = P.source(name, H, meter)
        for item in selected:
            record = item['record']; eid = record['evaluation_id']
            if eid in cache:
                row = deepcopy(cache[eid]); row['id'] = record['id']; row['alias_of'] = eid
            else:
                row = _missing(record, name, H, scales, 'unattempted')
                try:
                    state = P.evaluate(record['program'], values, meter)
                    row.update(status='available', cases=P.moments(state, scales, meter),
                               initial_cost=P.initial_cost(state, meter))
                    row.pop('reason')
                    if name == 'mu':
                        row['decomposition'] = P.decomposition(record['program'], values, state, FINAL_DECOMPOSITION, meter)
                except (OverflowError, TimeoutError, MemoryError) as error:
                    row = _missing(record, name, H, scales, str(error) or type(error).__name__)
                except (ValueError, TypeError, KeyError, ZeroDivisionError) as error:
                    row = _missing(record, name, H, scales, str(error) or type(error).__name__, 'invalid')
                cache[eid] = deepcopy(row); row['id'] = record['id']
            row['constants'] = item['constants']
            row['scores'] = D.scores(row['cases'], item['constants'], meter) if row['status'] == 'available' else []
            rows.append(row)
    except (ValueError, TypeError, KeyError, OverflowError, TimeoutError, MemoryError) as error:
        for item in selected[len(rows):]:
            row = _missing(item['record'], name, H, scales, str(error) or type(error).__name__)
            row.update(id=item['record']['id'], constants=item['constants'], scores=[]); rows.append(row)
    return dict(source=name, allocated=cap, counts=meter.counts(), rows=rows,
                elapsed_seconds=time.monotonic() - started,
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def run(directory):
    import permuted_arithmetic_circuits as P
    directory = Path(directory).resolve(); frozen_source(directory)
    epoch = time.time(); deadline = time.monotonic() + SECONDS
    write(directory / 'run_started.json', dict(one_attempt=True, epoch=epoch, deadline_seconds=SECONDS))
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, hard))
    meters = {}; workers = []; result = dict(status='UNKNOWN', **D.FLAGS)
    try:
        tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=ROOT,
                               capture_output=True, text=True, timeout=min(300, max(1, deadline - time.monotonic())))
        tested = dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr)
        if not tests.returncode: tested['work'] = synthetic_receipt(tests.stdout)
        write(directory / 'tests.json', tested)
        if tests.returncode: raise ValueError('frozen combined suite failed; no research')
        generation = _meter(ALLOCATIONS['generation'], deadline)
        discovery = _meter(ALLOCATIONS['discovery'], deadline)
        meters.update(generation=generation, discovery=discovery)
        catalog = D.generate_catalog(generation, P); write(directory / 'candidate_batch.json', catalog)
        unique = [r for r in catalog if r['id'] == r['evaluation_id']]
        cases = []
        for H, scales in ((511, D.TRAIN), (2047, D.VALIDATION)):
            for source in D.SOURCES:
                try: values = P.source(source, H, discovery); failure = None
                except (ValueError, TypeError, OverflowError, TimeoutError, MemoryError) as error:
                    values = None; failure = str(error) or type(error).__name__
                for record in unique:
                    row = (D.evaluate_case(record, source, H, scales, discovery, P, values)
                           if failure is None else _missing(record, source, H, scales, failure))
                    cases.append(row)
                    append_checkpoint(directory / 'discovery_checkpoints.jsonl', dict(row=row, counts=discovery.counts()))
            if H == 511:
                training = deepcopy(cases)
                fits = {str(r['id']): D.constants(r['cases'], generation)
                        for r in training if r['source'] == 'mu' and r['status'] == 'available'}
                write(directory / 'training.json', training); write(directory / 'training_fits.json', fits)
        write(directory / 'discovery_cases.json', cases)
        analysis = D.analyze_discovery(catalog, cases, generation)
        for row in analysis:
            if row['constants'] is not None and row['constants'] != fits.get(str(row['evaluation_id'])):
                raise ValueError('validation cannot refit training')
        selection = D.select_leads(analysis, generation)
        write(directory / 'discovery_analysis.json', analysis); write(directory / 'selection.json', selection)
        indexed = {r['id']: r for r in catalog}; evidence = {r['id']: r for r in analysis}
        selected = [dict(record=indexed[i], constants=fits.get(str(indexed[i]['evaluation_id']))) for i in selection['selected_ids']]
        if any(s['constants'] is None for s in selected): raise ValueError('selected baseline/lead requires complete mu training')
        write(directory / 'final_batch.json', selected)
        write(directory / 'proof_queue.json', [D.obligation(s['record']) for s in selected if s['record']['id']])
        with ProcessPoolExecutor(max_workers=3, mp_context=multiprocessing.get_context('spawn')) as pool:
            pending = {pool.submit(final_source, name, selected, FINAL_BUDGETS[name], deadline): name for name in D.SOURCES}
            for future in as_completed(pending):
                name = pending[future]; cap = FINAL_BUDGETS[name]
                try: worker = future.result()
                except Exception as error:
                    # Unknown worker spend consumes its ENTIRE reservation, never zero.
                    worker = dict(source=name, allocated=cap, counts=dict(operations=cap, peak_live_cells=6000000, maximum_rational_bits=4096),
                                  resource_failure='worker_failed_unknown_spend', rows=[])
                    for item in selected:
                        row = _missing(item['record'], name, D.FINAL_HORIZONS[name], D.FINAL_SCALES[name], str(error) or type(error).__name__)
                        row.update(id=item['record']['id'], constants=item['constants'], scores=[]); worker['rows'].append(row)
                write(directory / ('final_source_' + name + '.json'), worker); workers.append(worker)
        workers.sort(key=lambda w: D.SOURCES.index(w['source']))
        final = [row for worker in workers for row in worker['rows']]
        write(directory / 'final_responses.json', final)
        generation.charge(sum(len(D.canonical(x)) // 32 + 1 for x in (catalog, cases, analysis, selected, final)))
        result.update(status='CANDIDATE_LEADS', selected_ids=selection['selected_ids'],
                      missing_families=selection['missing_families'],
                      final_available=sum(r['status'] == 'available' for r in final),
                      final_missing=sum(r['status'] == 'missing' for r in final),
                      final_invalid=sum(r['status'] == 'invalid' for r in final))
    except (ValueError, TypeError, KeyError, OverflowError, TimeoutError, MemoryError, RuntimeError, subprocess.TimeoutExpired) as error:
        result.update(reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        result.update(stage_counts={k: m.counts() for k, m in meters.items()},
                      final_workers=[{k: v for k, v in w.items() if k != 'rows'} for w in workers],
                      elapsed_seconds=time.time() - epoch)
        write(directory / 'receipt.json', result); resource.setrlimit(resource.RLIMIT_AS, (soft, hard))
    return result


def independent_analysis(catalog, cases, meter, train=D.TRAIN, validation=D.VALIDATION):
    """Independent fit, diagnostic and gate implementation (no discovery calls)."""
    def rootceil(n, q):
        value = 1
        while value ** q < n: meter.charge(q); value += 1
        meter.number(value ** q)
        return value

    def ratio(a, b, inactive=False):
        numerator, denominator = Q(a), Q(b)
        if min(numerator, denominator) < 0: raise ValueError('negative complete energy')
        if not denominator:
            if not numerator and inactive: return dict(status='defined', value='1', inactive=True)
            if inactive: raise ValueError('positive energy without absolute envelope')
            return dict(status='undefined', reason='zero_denominator')
        return dict(status='defined', value=str(meter.number(numerator / denominator)), inactive=False)

    index = {(c['id'], c['source'], c['horizon']): c for c in cases}
    if len(index) != len(cases): raise ValueError('duplicate case key')
    Ht, Hv = 2 * max(train) - 1, 2 * max(validation) - 1
    result = []
    for record in catalog:
        meter.charge(); eid = record['evaluation_id']
        out = dict(id=record['id'], evaluation_id=eid, family=record['family'], status='ineligible',
                   reason='missing_complete_discovery', constants=None, scores=[], diagnostics=[],
                   gate_failures=None, raw_ratio=None, specificity=None, conditional_cost=None,
                   complexity=record['complexity'])
        if record['id'] != 0 and eid == 0:
            out['reason'] = 'baseline_alias'; result.append(out); continue
        training = [index.get((eid, source, Ht)) for source in D.SOURCES]
        vals = [index.get((eid, source, Hv)) for source in D.SOURCES]
        baseline = index.get((0, 'mu', Hv))
        if not all(x is not None and x['status'] == 'available' for x in training + vals + [baseline]):
            result.append(out); continue
        if any([c['X'] for c in r['cases']] != list(train) for r in training) or any(
                [c['X'] for c in r['cases']] != list(validation) for r in vals + [baseline]):
            raise ValueError('fixed complete discovery scales')
        if any(a['initial_cost'] != b['initial_cost'] for a, b in zip(training, vals)):
            raise ValueError('finite head must be horizon invariant')
        fitted = {}
        for q in D.LEVELS:
            best = Q(0)
            for c in training[0]['cases']:
                best = max(best, meter.number(Q(c['energy']) / rootceil(c['X'], q)))
            fitted[str(q)] = str(best)
        out['constants'] = fitted
        for j, actual in enumerate(vals[0]['cases']):
            X = actual['X']
            for q in D.LEVELS:
                threshold = meter.number(Q(fitted[str(q)]) * rootceil(X, q))
                out['scores'].append(dict(X=X, q=q, bound=str(threshold), passed=Q(actual['energy']) <= threshold,
                                          dyadic=X & (X - 1) == 0))
            kappas = {s: ratio(vals[k]['cases'][j]['energy'], vals[k]['cases'][j]['absolute_energy'], True)
                      for k, s in enumerate(D.SOURCES)}
            if any(k['status'] == 'defined' and Q(k['value']) > 1 for k in kappas.values()):
                raise ValueError('path envelope does not majorize signed energy')
            specific = (ratio(kappas['mu']['value'], min(Q(kappas[s]['value']) for s in D.SOURCES[1:]))
                        if all(k['status'] == 'defined' for k in kappas.values())
                        else dict(status='undefined', reason='undefined_kappa'))
            out['diagnostics'].append(dict(X=X, kappas=kappas,
                                          raw_ratio=ratio(actual['energy'], baseline['cases'][j]['energy']),
                                          specificity=specific))
        if any(d[k]['status'] != 'defined' for d in out['diagnostics'] for k in ('raw_ratio', 'specificity')):
            out['reason'] = 'undefined_matched_validation_diagnostic'; result.append(out); continue
        # Independently derive the certificate exponents/factors from the word.
        order = Q(0); permutations = 0; shear_factor = Q(1)
        for s in record['program']['stages']:
            meter.charge()
            if s['op'] == 'convolve': order += abs(Q(s['alpha']))
            if s['op'] == 'permute': permutations += 1
            if s['op'] == 'shear': shear_factor = meter.number(shear_factor * (1 + 2 * abs(Q(s['coefficient']))))
        R = (order.numerator + order.denominator - 1) // order.denominator
        cost = meter.number(9 ** permutations * shear_factor ** 2 * 13 ** (2 * R)
                            * (Q(training[0]['initial_cost']) + 48 * Q(fitted['12'])))
        out.update(status='eligible', reason=None, gate_failures=sum(not x['passed'] for x in out['scores']),
                   raw_ratio=str(max(Q(x['raw_ratio']['value']) for x in out['diagnostics'])),
                   specificity=str(max(Q(x['specificity']['value']) for x in out['diagnostics'])), conditional_cost=str(cost))
        result.append(out)
    return result


def independent_selection(analysis, meter):
    selected = [0]; ranked = []; missing = []; used = {0}
    for family in D.FAMILIES:
        family_rows = [deepcopy(r) for r in analysis if r['family'] == family and r['status'] == 'eligible']
        for failed in sorted({r['gate_failures'] for r in family_rows}):
            pending = {r['id']: r for r in family_rows if r['gate_failures'] == failed}; layer = 0
            while pending:
                unbeaten = []
                for key, row in pending.items():
                    own = [Q(row[k]) for k in ('raw_ratio', 'specificity', 'conditional_cost')]
                    wins = False
                    for other_key, other in pending.items():
                        meter.charge(3)
                        opponent = [Q(other[k]) for k in ('raw_ratio', 'specificity', 'conditional_cost')]
                        if other_key != key and all(x <= y for x, y in zip(opponent, own)) and opponent != own:
                            wins = True; break
                    if not wins: unbeaten.append(key)
                for key in unbeaten:
                    row = pending.pop(key); row['pareto_layer'] = layer; ranked.append(row)
                layer += 1
        family_rank = [r for r in ranked if r['family'] == family]
        if not family_rank: missing.append(family); continue
        def key(r):
            return (r['gate_failures'], r['pareto_layer'], Q(r['specificity']), Q(r['raw_ratio']),
                    Q(r['conditional_cost']), r['complexity'], r['id'])
        options = [r for r in family_rank if r['evaluation_id'] not in used]
        if options:
            chosen = min(options, key=key); selected.append(chosen['id']); used.add(chosen['evaluation_id'])
        else: missing.append(family)
    return dict(selected_ids=selected, ranking=sorted(ranked, key=lambda r: r['id']), missing_families=missing)


def audit(directory):
    import check_permuted_arithmetic_circuits as C
    directory = Path(directory).resolve(); frozen_source(directory)
    # This exclusive marker forbids starting again, including after exhaustion.
    write(directory / 'independent_started.json', dict(one_audit=True, no_restart=True))
    tests, receipt = read(directory / 'tests.json'), read(directory / 'receipt.json')
    if tests['returncode'] != 0 or tests['work'] != synthetic_receipt(tests['stdout']):
        raise ValueError('one successful frozen combined suite required')
    research = 0
    for name, counts in receipt['stage_counts'].items():
        if name not in ('generation', 'discovery') or type(counts['operations']) is not int or not 0 <= counts['operations'] <= ALLOCATIONS[name]:
            raise ValueError('bounded actual research counters')
        research += counts['operations']
    if receipt['status'] != 'CANDIDATE_LEADS' or set(receipt['stage_counts']) != {'generation', 'discovery'}:
        raise ValueError('complete research outcome required for complete audit')
    workers = receipt['final_workers']
    if [w['source'] for w in workers] != D.SOURCES or sum(w['allocated'] for w in workers) != ALLOCATIONS['final']:
        raise ValueError('complete disjoint source allocations')
    for w in workers:
        if w['allocated'] != FINAL_BUDGETS[w['source']] or type(w['counts']['operations']) is not int or not 0 <= w['counts']['operations'] <= w['allocated']:
            raise ValueError('worker cost within actual source reservation')
        research += w['counts']['operations']
    previous = tests['work']['total'] + research
    cap = TOTAL - previous
    if cap < 1: raise OverflowError('no whole-study audit reserve remaining')
    epoch = read(directory / 'run_started.json')['epoch']
    remaining_seconds = SECONDS - (time.time() - epoch)
    meter = _meter(cap, time.monotonic() + max(0, remaining_seconds))
    started = time.monotonic(); soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, hard))
    result = dict(status='UNKNOWN', finite_arithmetic_verified=False, recovery_certificates_checked=False,
                  allocated=cap, previously_consumed=previous, **D.FLAGS)
    checked = missing = certificates = 0
    cache = {}

    def require(condition, reason):
        if not condition: raise ValueError(reason)

    def get(name):
        value = read(directory / name); meter.charge(len(D.canonical(value)) // 32 + 1); return value

    def check(record, row, final=False):
        nonlocal checked, missing
        if row['status'] != 'available':
            require(row['status'] in ('missing', 'invalid') and bool(row.get('reason')) and row['cases'] == [], 'explicit unfilled failure disposition')
            missing += 1
        else:
            name, H, scales = row['source'], row['horizon'], row['scales']
            if (name, H) not in cache: cache[(name, H)] = C.source(name, H, meter)
            values = cache[(name, H)]
            state = C.evaluate(record['program'], values, meter)
            require(C.moments(state, scales, meter) == row['cases'], 'independent complete moments and path envelope')
            require(C.initial_cost(state, meter) == row['initial_cost'], 'complete finite signed head')
            if final and name == 'mu':
                require(C.decomposition(record['program'], values, state, FINAL_DECOMPOSITION, meter) == row.get('decomposition'), 'exact fresh/lower/mixed signed decomposition')
            elif 'decomposition' in row: raise ValueError('mu-only final decomposition')
            checked += 1
        append_checkpoint(directory / 'independent_checkpoints.jsonl', dict(kind='completed_evaluation',
                          id=row['id'], source=row['source'], horizon=row['horizon'], status=row['status'],
                          finite_verified=row['status'] == 'available', counts=meter.counts(), cumulative_operations=previous + meter.operations))

    try:
        require(all(receipt[k] is False for k in D.FLAGS), 'no unproved theorem flag')
        catalog = get('candidate_batch.json')
        require(catalog == D.generate_catalog(meter, C), 'frozen source-free generator; independent normalization/certificate metadata')
        require(len(catalog) == 49, 'all48 raw words and baseline retained')
        for r in catalog:
            require(C.verify(r['certificate'], meter), 'independent recovery certificate'); certificates += 1
        unique = {r['id']: r for r in catalog if r['id'] == r['evaluation_id']}
        cases = get('discovery_cases.json')
        expected_keys = [(eid, s, H) for H in (511, 2047) for s in D.SOURCES for eid in unique]
        require([(r['id'], r['source'], r['horizon']) for r in cases] == expected_keys, 'one evaluation per normalized word/source/partition')
        for row in cases:
            require(row['scales'] == (D.TRAIN if row['horizon'] == 511 else D.VALIDATION), 'frozen discovery scale binding')
            check(unique[row['id']], row)
        training = [r for r in cases if r['horizon'] == 511]
        require(get('training.json') == training, 'training archived before validation')
        analysis = independent_analysis(catalog, cases, meter)
        # Fits also exist when another required control/validation case is missing.
        independent_fits = {}
        for r in training:
            if r['source'] == 'mu' and r['status'] == 'available':
                fitted = {}
                for q in D.LEVELS:
                    maximum = Q(0)
                    for c in r['cases']:
                        k = 1
                        while k ** q < c['X']: meter.charge(q); k += 1
                        maximum = max(maximum, meter.number(Q(c['energy']) / k))
                    fitted[str(q)] = str(maximum)
                independent_fits[str(r['id'])] = fitted
        require(get('training_fits.json') == independent_fits, 'independent training-only fits')
        require(get('discovery_analysis.json') == analysis, 'independent gates, kappas, ratios and inverse-aware conditional costs')
        selection = independent_selection(analysis, meter)
        require(get('selection.json') == selection, 'independent exact Pareto ranking and family quotas')
        selected = [dict(record=catalog[i], constants=independent_fits[str(catalog[i]['evaluation_id'])]) for i in selection['selected_ids']]
        require(get('final_batch.json') == selected, 'final chosen before final arithmetic')
        require(get('proof_queue.json') == [D.obligation(s['record']) for s in selected if s['record']['id']], 'full missing moment obligation')
        final = get('final_responses.json'); cursor = 0
        for worker in workers:
            full = get('final_source_' + worker['source'] + '.json')
            require({k: v for k, v in full.items() if k != 'rows'} == worker, 'full worker receipt')
            partition = final[cursor:cursor + len(selected)]; cursor += len(selected)
            require(partition == full['rows'] and len(partition) == len(selected), 'all final outcomes retained')
            done = {}
            for item, row in zip(selected, partition):
                record = item['record']; name = worker['source']
                require(row['id'] == record['id'] and row['source'] == name and row['horizon'] == D.FINAL_HORIZONS[name]
                        and row['scales'] == D.FINAL_SCALES[name] and row['constants'] == item['constants'], 'frozen final source/scales/program/constants')
                eid = record['evaluation_id']
                if eid in done:
                    earlier = done[eid]
                    require({k: v for k, v in row.items() if k not in ('id', 'alias_of')} ==
                            {k: v for k, v in earlier.items() if k not in ('id', 'alias_of')}, 'normalized final alias exactly inherits one evaluation')
                else:
                    check(record, row, True); done[eid] = row
                expected_scores = []
                if row['status'] == 'available':
                    for c in row['cases']:
                        for q in D.LEVELS:
                            k = 1
                            while k ** q < c['X']: meter.charge(q); k += 1
                            bound = meter.number(Q(item['constants'][str(q)]) * k)
                            expected_scores.append(dict(X=c['X'], q=q, bound=str(bound), passed=Q(c['energy']) <= bound,
                                                        dyadic=c['X'] & (c['X'] - 1) == 0))
                require(row['scores'] == expected_scores, 'independent final comparison without refitting')
        require(cursor == len(final), 'no extra final outcomes')
        require(previous + meter.operations <= TOTAL, 'one cumulative whole-study cap')
        result.update(status='FINITE_AVAILABLE_EVALUATIONS_VERIFIED', finite_arithmetic_verified=True,
                      all_expected_evaluations_available=missing == 0, recovery_certificates_checked=True,
                      selected_ids=selection['selected_ids'],
                      scope='independent available finite arithmetic and exact inverse certificate; shared source-free generator; separate fit/diagnostic/selection arithmetic; cofinal moment gate unproved')
    except (ValueError, TypeError, KeyError, OverflowError, TimeoutError, MemoryError, ZeroDivisionError) as error:
        result.update(reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        result.update(evaluations_verified=checked, missing_or_invalid=missing, certificates_checked=certificates,
                      counts=meter.counts(), cumulative_operations=previous + meter.operations,
                      elapsed_seconds=time.monotonic() - started)
        write(directory / 'independent_verification.json', result); resource.setrlimit(resource.RLIMIT_AS, (soft, hard))
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['freeze', 'run', 'audit'])
    parser.add_argument('directory')
    args = parser.parse_args(); result = globals()[args.command](args.directory)
    if result is not None: print(D.canonical(result))
