"""Frozen candidate discovery for repeated multiplicative shift differences."""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
import json
from fractions import Fraction as Q
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

import flint
from flint import arb, ctx
import renewal_shift_candidates as P

ROOT = Path(__file__).resolve().parent
TRAIN = [96, 192, 384, 640]
VALIDATION = [896, 1280, 1792, 2560]
FINAL = [73728, 114688]
DISCOVERY_H = 5119
FINAL_H = 229375
LEVELS = [2, 3, 6, 12]
TOTAL = 1000000000
SECONDS = 7200
ROOT_RESERVE = 1000000  # Symbolic enumeration, metadata and file orchestration.
TESTS = ['test_renewal_shift_candidates', 'test_check_renewal_shift_candidates',
         'test_run_renewal_shift_discovery']
RECEIPTS = ['renewal_producer_development.json', 'renewal_checker_development.json',
            'renewal_workflow_development.json']
SOURCE_FILES = ['renewal_shift_candidates.py', 'check_renewal_shift_candidates.py',
                'run_renewal_shift_discovery.py', 'renewal_shift_discovery_protocol.txt',
                'shifted_quotient_candidates.py',  # Unmodified shared work meter.
                'RENEWAL_SHIFT_ANALYTIC_REVIEW_001.txt',
                'RENEWAL_SHIFT_STRUCTURE_REVIEW_001.txt'] + [m+'.py' for m in TESTS] + RECEIPTS
FAILURES = (ValueError, ArithmeticError, OverflowError, TimeoutError, MemoryError)


def read(path):
    with Path(path).open('rb') as stream:
        raw = stream.read(8*1024**2+1)
    if len(raw) > 8*1024**2:
        raise OverflowError('eight MiB artifact cap')
    return json.loads(raw)


def write(path, value):
    raw = (json.dumps(value, sort_keys=True, indent=2, allow_nan=False)+'\n').encode()
    if len(raw) > 8*1024**2:
        raise OverflowError('eight MiB artifact cap')
    with Path(path).open('xb') as stream:
        stream.write(raw)


def checkpoint(path, row):
    # One writer per file. Completed cases survive any later cap failure.
    with Path(path).open('a') as stream:
        stream.write(json.dumps(row, sort_keys=True, allow_nan=False)+'\n')
        stream.flush()


def receipts():
    result = {}
    for name in RECEIPTS:
        row = read(ROOT/name)
        if (not row['runs'] or row['runs'][-1]['returncode'] != 0
                or row['operations'] != sum(r['operations'] for r in row['runs'])):
            raise ValueError('complete cumulative passed receipt '+name)
        result[name] = row
    return result


def protocol():
    return dict(schema='renewal-shift-discovery-v1', catalogue=P.catalogue(),
                train=TRAIN, validation=VALIDATION, final=FINAL, levels=LEVELS,
                discovery_horizon=DISCOVERY_H, final_horizon=FINAL_H, sources=P.SOURCES,
                producer_bits=128, checker_bits=192, total_work=TOTAL,
                seconds=SECONDS, aggregate_memory_bytes=16*1024**3,
                process_memory_bytes=4*1024**3, workers=3, hashes=False,
                source_overlap_with_previous_research=True,
                baseline='complete mu-delta_1, identical for every word length',
                controls='same multiplicative shift word on each base Dirichlet source',
                selection=['validation_growth_failures', 'worst_full_energy_ratio', 'id'],
                lead_gate='all16 validation growth tests and all4 E<=0.95 E_baseline',
                adaptation_from_final=False, tests=TESTS, development=receipts(),
                python=sys.version, flint=getattr(flint, '__version__', 'unknown'), **P.FLAGS)


def freeze(directory):
    directory = Path(directory).resolve()
    data = protocol()
    contents = {name: (ROOT/name).read_bytes() for name in SOURCE_FILES}
    if directory.exists():
        raise FileExistsError('new immutable study directory required')
    directory.mkdir(parents=True)
    (directory/'source_snapshot').mkdir()
    for name, raw in contents.items():
        (directory/'source_snapshot'/name).write_bytes(raw)
    write(directory/'protocol.json', data)
    write(directory/'source_files.json', SOURCE_FILES)


def verify_source(directory):
    if read(directory/'source_files.json') != SOURCE_FILES:
        raise ValueError('exact source manifest')
    for name in SOURCE_FILES:
        if (ROOT/name).read_bytes() != (directory/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)
    if read(directory/'protocol.json') != protocol():
        raise ValueError('changed frozen protocol')


def tight(value):
    return value.is_finite() and value.rad() <= arb(2)**(-70)*(1+abs(value.mid()))


def parse(row):
    result = dict(X=row['X'], energy=arb(row['energy']), absolute_energy=arb(row['absolute_energy']))
    if not tight(result['energy']) or not tight(result['absolute_energy']):
        raise ValueError('tight finite interval required')
    return result


def constants(rows, meter):
    result = {}
    for q in LEVELS:
        largest = arb(0)
        for row in rows:
            if not tight(row['energy']):
                raise ValueError('tight training energy')
            meter.charge(72)
            upper = (row['energy']/arb(row['X'])**(arb(1)/q)).upper()
            largest = max(largest, upper)
        integer = int((largest*2**40).ceil().unique_fmpz())
        result[str(q)] = str(Q(max(1, integer), 2**40))
    return result


def scores(rows, fitted, baseline, meter):
    tests, ratios, improvement = [], [], []
    for row in rows:
        E, B = row['energy'], baseline[row['X']]['energy']
        if not tight(E) or not tight(B) or not B > 0:
            raise ValueError('positive tight complete energy comparator')
        meter.charge(10)
        ratios.append(float((E/B).mid()))
        improvement.append(bool(E <= arb(95)/100*B))
        for q in LEVELS:
            meter.charge(72)
            tests.append(dict(X=row['X'], q=q,
                              passed=bool(E <= P.real(fitted[str(q)])*arb(row['X'])**(arb(1)/q))))
    return dict(growth_tests=tests, growth_failures=sum(not t['passed'] for t in tests),
                energy_ratios=ratios, worst_full_energy_ratio=max(ratios),
                strict_improvements=improvement,
                numerical_lead=all(improvement) and all(t['passed'] for t in tests))


def selected(records):
    result = []
    for depth in range(1, 5):
        candidates = [r for r in records if r['source'] == 'mu' and r['depth'] == depth]
        best = min(candidates, key=lambda r: (r['scores']['growth_failures'],
                                              r['scores']['worst_full_energy_ratio'], r['id']))
        result.append({k: best[k] for k in ('id', 'depth', 'program', 'stencil', 'normalization',
                                          'constants', 'scores')})
    return result


def encode_normalizer(rows):
    return [dict(shift=r['shift'], residue=r['residue'].str(45, radius=True),
                 coefficient=r['coefficient'].str(45, radius=True)) for r in rows]


def discovery(directory, meter):
    records, fitted, baseline = [], {}, []
    path = directory/'discovery_checkpoints.jsonl'
    for source in P.SOURCES:
        workspace = P.Workspace(source, DISCOVERY_H, meter)
        if source == 'mu':
            state = workspace.baseline()
            baseline = P.encoded(P.moments(state, TRAIN+VALIDATION, meter))
            checkpoint(path, dict(stage='baseline', rows=baseline, operations=meter.operations))
            del state
        base = {r['X']: parse(r) for r in baseline}
        for item in P.catalogue():
            if not item['eligible']:
                continue
            state = workspace.evaluate(item['program'])
            training = P.moments(state, TRAIN, meter)
            if source == 'mu':
                fitted[str(item['id'])] = constants(training, meter)
                checkpoint(path, dict(stage='fit_before_validation', id=item['id'],
                                      constants=fitted[str(item['id'])], operations=meter.operations))
            validation = P.moments(state, VALIDATION, meter)
            row = dict(**item, source=source, training=P.encoded(training),
                       validation=P.encoded(validation), constants=fitted[str(item['id'])],
                       scores=scores(validation, fitted[str(item['id'])], base, meter),
                       normalizer=encode_normalizer(state['normalizer']))
            records.append(row)
            checkpoint(path, dict(stage='discovery', result=row, operations=meter.operations))
            del state
        print(json.dumps(dict(stage='discovery_source', source=source,
                              operations=meter.operations)), flush=True)
        del workspace
    return dict(records=records, baseline=baseline, selected=selected(records),
                counts=meter.counts(), **P.FLAGS)


def worker_meter(cap, deadline):
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, hard))
    meter = P.Meter(cap)
    meter.deadline = deadline
    return meter


def final_worker(directory, source, choices, cap, deadline):
    ctx.prec = 128
    meter = worker_meter(cap, deadline)
    rows, baseline = [], []
    path = Path(directory)/('final_checkpoints_'+source+'.jsonl')
    try:
        workspace = P.Workspace(source, FINAL_H, meter)
        if source == 'mu':
            state = workspace.baseline()
            baseline = P.encoded(P.moments(state, FINAL, meter))
            checkpoint(path, dict(stage='baseline', rows=baseline, operations=meter.operations))
            del state
        for item in choices:
            state = workspace.evaluate(item['program'])
            row = dict(id=item['id'], depth=item['depth'], program=item['program'],
                       normalizer=encode_normalizer(state['normalizer']),
                       cases=P.encoded(P.moments(state, FINAL, meter)))
            rows.append(row)
            checkpoint(path, dict(stage='final', result=row, operations=meter.operations))
            del state
        status, reason = 'available', None
    except FAILURES as error:
        status, reason = 'incomplete', str(error) or type(error).__name__
    return dict(source=source, status=status, reason=reason, rows=rows, baseline=baseline,
                counts=meter.counts(), peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def compare_rows(expected, actual):
    if len(expected) != len(actual):
        raise ValueError('same complete block list')
    for old, new in zip(expected, actual):
        if old['X'] != new['X']:
            raise ValueError('same block endpoints')
        for key in ('energy', 'absolute_energy'):
            value = arb(old[key])
            if not tight(value) or not tight(new[key]) or not value.overlaps(new[key]):
                raise ArithmeticError('independent tight interval disagreement '+key)


def compare_normalizer(expected, actual):
    if len(expected) != len(actual):
        raise ValueError('all normalizer terms')
    for old, new in zip(expected, actual):
        if old['shift'] != new['shift']:
            raise ValueError('normalizer shift')
        for key in ('residue', 'coefficient'):
            value = arb(old[key])
            if not tight(value) or not tight(new[key]) or not value.overlaps(new[key]):
                raise ArithmeticError('independent tight residue disagreement '+key)


def audit_worker(directory, source, discovered, final, cap, deadline):
    import check_renewal_shift_candidates as C
    ctx.prec = 192
    meter = worker_meter(cap, deadline)
    checked, invalid = [], []
    path = Path(directory)/('audit_checkpoints_'+source+'.jsonl')

    def record(stage, identity, cases):
        row = dict(stage=stage, id=identity, cases=cases)
        checked.append(row)
        checkpoint(path, dict(**row, operations=meter.operations))

    try:
        # Compare symbolic identities using the checker's independently compiled subsets.
        for item in P.catalogue():
            if item['eligible']:
                if item['stencil'] != [[str(s), c] for s, c in C.stencil(item['program'])]:
                    raise ValueError('independent merged-stencil disagreement')
        for row in discovered['records']:
            if row['source'] != source:
                continue
            state = C.evaluate(row['program'], source, DISCOVERY_H, meter)
            compare_normalizer(row['normalizer'], state['normalizer'])
            compare_rows(row['training']+row['validation'], C.moments(state, TRAIN+VALIDATION, meter))
            record('discovery', row['id'], len(TRAIN+VALIDATION))
            del state
        if source == 'mu':
            state = C.baseline(DISCOVERY_H, meter)
            compare_rows(discovered['baseline'], C.moments(state, TRAIN+VALIDATION, meter))
            record('discovery_baseline', None, len(TRAIN+VALIDATION))
            del state
        if final['status'] != 'available':
            raise ValueError('complete final source evidence required')
        for row in final['rows']:
            state = C.evaluate(row['program'], source, FINAL_H, meter)
            compare_normalizer(row['normalizer'], state['normalizer'])
            compare_rows(row['cases'], C.moments(state, FINAL, meter))
            record('final', row['id'], len(FINAL))
            del state
        if source == 'mu':
            state = C.baseline(FINAL_H, meter)
            compare_rows(final['baseline'], C.moments(state, FINAL, meter))
            record('final_baseline', None, len(FINAL))
            del state
        status = 'verified'
    except FAILURES as error:
        status = 'incomplete'
        invalid.append(str(error) or type(error).__name__)
    return dict(source=source, status=status, checked=checked, errors=invalid,
                counts=meter.counts(), peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def run(directory):
    directory = Path(directory).resolve()
    verify_source(directory)
    started = time.monotonic()
    deadline = started+SECONDS
    write(directory/'started.json', dict(attempt=1, monotonic=started))
    ctx.prec = 128
    development = sum(r['operations'] for r in receipts().values())
    result = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS],
                            cwd=ROOT, capture_output=True, text=True, timeout=120)
    matches = re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$', result.stdout, re.M)
    frozen = sum(int(n) for _, n in matches)
    write(directory/'frozen_tests.json', dict(returncode=result.returncode, stdout=result.stdout,
                                            stderr=result.stderr, operations=frozen))
    if result.returncode or sorted(m for m, _ in matches) != sorted(TESTS):
        raise RuntimeError('single complete frozen calibration invocation required')
    spent = development+frozen+ROOT_RESERVE
    meter = P.Meter(min(140000000, TOTAL-spent))
    meter.deadline = deadline
    try:
        discovered = discovery(directory, meter)
    except FAILURES as error:
        write(directory/'incomplete.json', dict(stage='discovery', error=str(error),
                                               operations=spent+meter.operations, **P.FLAGS))
        return
    spent += meter.operations
    write(directory/'discovery.json', discovered)
    final = {}
    # Per-worker caps reserve enough remaining capacity for the independent audit.
    final_cap = min(160000000, (TOTAL-spent)//6)
    with ProcessPoolExecutor(max_workers=3) as pool:
        futures = {pool.submit(final_worker, str(directory), s, discovered['selected'], final_cap, deadline): s
                   for s in P.SOURCES}
        for future in as_completed(futures):
            value = future.result()
            final[value['source']] = value
            spent += value['counts']['operations']
            write(directory/('final_'+value['source']+'.json'), value)
            print(json.dumps(dict(stage='final_source', source=value['source'], status=value['status'],
                                  total_operations=spent)), flush=True)
    audit_cap = max(0, (TOTAL-spent-ROOT_RESERVE)//3)
    audits = {}
    with ProcessPoolExecutor(max_workers=3) as pool:
        futures = {pool.submit(audit_worker, str(directory), s, discovered, final[s], audit_cap, deadline): s
                   for s in P.SOURCES}
        for future in as_completed(futures):
            value = future.result()
            audits[value['source']] = value
            spent += value['counts']['operations']
            write(directory/('audit_'+value['source']+'.json'), value)
            print(json.dumps(dict(stage='independent_source', source=value['source'], status=value['status'],
                                  total_operations=spent)), flush=True)
    ranking_meter = P.Meter(min(ROOT_RESERVE, TOTAL-spent))
    ranking_meter.deadline = deadline
    summaries = []
    for item in discovered['selected']:
        cases = {}
        for source in P.SOURCES:
            record = next((r for r in final[source]['rows'] if r['id'] == item['id']), None)
            base = final['mu']['baseline']
            if record is not None and base:
                cases[source] = scores([parse(r) for r in record['cases']], item['constants'],
                                       {r['X']: parse(r) for r in base}, ranking_meter)
        admitted = item['scores']['numerical_lead'] and cases.get('mu', {}).get('numerical_lead', False)
        summaries.append(dict(**item, final=cases, admitted_through_final=admitted))
    spent += ranking_meter.operations
    verify_source(directory)
    checked = sum(row['cases'] for value in audits.values() for row in value['checked'])
    expected = (sum(row['eligible'] for row in P.catalogue())*len(P.SOURCES)+1)*len(TRAIN+VALIDATION)
    expected += (len(discovered['selected'])*len(P.SOURCES)+1)*len(FINAL)
    verified = (all(a['status'] == 'verified' for a in audits.values())
                and checked == expected and spent <= TOTAL)
    write(directory/'report.json', dict(status='FINITE_INTERVAL_EVALUATIONS_VERIFIED' if verified else 'INCOMPLETE',
                                        selected=summaries, total_operations=spent, work_limit=TOTAL,
                                        preparation_operations=development+frozen+ROOT_RESERVE,
                                        discovery_operations=meter.operations,
                                        final_operations=sum(r['counts']['operations'] for r in final.values()),
                                        audit_operations=sum(r['counts']['operations'] for r in audits.values()),
                                        final_ranking_operations=ranking_meter.operations,
                                        elapsed_seconds=time.monotonic()-started,
                                        checked_blocks=checked, expected_blocks=expected,
                                        all_scale_bound_status='open', **P.FLAGS))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['freeze', 'run'])
    parser.add_argument('directory')
    arguments = parser.parse_args()
    globals()[arguments.action](arguments.directory)
