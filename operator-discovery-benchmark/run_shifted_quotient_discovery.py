"""Frozen structural search and independent full-block interval checks."""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction as Q
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

import flint
from flint import arb, ctx
import shifted_quotient_candidates as P

ROOT = Path(__file__).resolve().parent
TRAIN = [64, 128, 256, 512]
VALIDATION = [768, 1024, 1536, 2048]
FINAL = [49152, 65536]
LEVELS = [2, 3, 6, 12]
TOTAL = 800000000
SECONDS = 7200
ROOT_RESERVE = 1000000
TESTS = ['test_shifted_quotient_candidates', 'test_check_shifted_quotient_candidates',
         'test_run_shifted_quotient_discovery']
RECEIPTS = ['shifted_producer_development.json', 'shifted_checker_development.json',
            'shifted_workflow_development.json']
SOURCES = ['shifted_quotient_candidates.py', 'check_shifted_quotient_candidates.py',
           'run_shifted_quotient_discovery.py', 'shifted_quotient_discovery_protocol.txt',
           'SHIFTED_QUOTIENT_ANALYTIC_REVIEW_001.txt',
           'SHIFTED_QUOTIENT_STRUCTURE_REVIEW_001.txt'] + [x+'.py' for x in TESTS] + RECEIPTS


def read(path):
    with Path(path).open('rb') as f:
        raw = f.read(8*1024**2 + 1)
    if len(raw) > 8*1024**2:
        raise OverflowError('eight MiB artifact cap')
    return json.loads(raw)


def write(path, value):
    data = (json.dumps(value, sort_keys=True, indent=2, allow_nan=False)+'\n').encode()
    if len(data) > 8*1024**2:
        raise OverflowError('eight MiB artifact cap')
    with Path(path).open('xb') as f:
        f.write(data)


def checkpoint(directory, row):
    with (directory/'checkpoints.jsonl').open('a') as f:
        f.write(json.dumps(row, sort_keys=True, allow_nan=False)+'\n')
        f.flush()


def receipts():
    out = {}
    for name in RECEIPTS:
        row = read(ROOT/name)
        if (not row['runs'] or row['runs'][-1]['returncode'] != 0
                or row['operations'] != sum(r['operations'] for r in row['runs'])):
            raise ValueError('complete cumulative passed development receipt '+name)
        out[name] = row
    return out


def protocol():
    return dict(schema='shifted-quotient-discovery-v1', catalogue=P.catalogue(),
                train=TRAIN, validation=VALIDATION, final=FINAL, levels=LEVELS,
                discovery_horizon=4095, final_horizon=131071, sources=P.SOURCES,
                producer_bits=128, checker_bits=192, total_work=TOTAL,
                seconds=SECONDS, aggregate_memory_bytes=16*1024**3,
                process_memory_bytes=4*1024**3, workers=3, hashes=False,
                source_overlap_with_previous_research=True,
                baseline='(mu-delta_1) Dirichlet convolution power, same degree',
                selection=['validation_growth_failures', 'worst_full_energy_ratio', 'id'],
                lead_gate='all16 growth tests and all4 E<=0.95 E_same_degree_baseline',
                adaptation_from_final=False, tests=TESTS, development=receipts(),
                python=sys.version, flint=getattr(flint, '__version__', 'unknown'),
                **P.FLAGS)


def freeze(directory):
    directory = Path(directory).resolve()
    data = protocol()
    contents = {name: (ROOT/name).read_bytes() for name in SOURCES}
    if directory.exists():
        raise FileExistsError('new immutable study directory required')
    directory.mkdir(parents=True)
    (directory/'source_snapshot').mkdir()
    for name, raw in contents.items():
        (directory/'source_snapshot'/name).write_bytes(raw)
    write(directory/'protocol.json', data)
    write(directory/'source_files.json', SOURCES)


def verify_source(directory):
    if read(directory/'source_files.json') != SOURCES:
        raise ValueError('exact source manifest')
    for name in SOURCES:
        if (ROOT/name).read_bytes() != (directory/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)
    if read(directory/'protocol.json') != protocol():
        raise ValueError('changed frozen protocol')


def tight(value):
    return value.is_finite() and value.rad() <= arb(2)**(-70)*(1+abs(value.mid()))


def parse(row):
    result = dict(X=row['X'], energy=arb(row['energy']), absolute_energy=arb(row['absolute_energy']))
    if not tight(result['energy']) or not tight(result['absolute_energy']):
        raise ValueError('tight certified finite interval required')
    return result


def constants(rows):
    out = {}
    for q in LEVELS:
        largest = max((r['energy']/arb(r['X'])**(arb(1)/q)).upper() for r in rows)
        integer = int((largest*2**40).ceil().unique_fmpz())
        out[str(q)] = str(Q(max(1, integer), 2**40))
    return out


def scores(rows, fitted, baseline):
    tests = []
    ratios = []
    improvement = []
    for row in rows:
        E = row['energy']
        B = baseline[row['X']]['energy']
        if not tight(E) or not tight(B) or not B > 0:
            raise ValueError('positive tight complete energy comparator')
        ratio = E/B
        ratios.append(float(ratio.mid()))
        improvement.append(bool(E <= arb(95)/100*B))
        for q in LEVELS:
            tests.append(dict(X=row['X'], q=q,
                              passed=bool(E <= P.real(fitted[str(q)])*arb(row['X'])**(arb(1)/q))))
    return dict(growth_tests=tests, growth_failures=sum(not t['passed'] for t in tests),
                energy_ratios=ratios, worst_full_energy_ratio=max(ratios),
                strict_improvements=improvement,
                numerical_lead=all(improvement) and all(t['passed'] for t in tests))


def discovery(directory, meter):
    baselines = {}
    records = []
    fitted = {}
    for source in P.SOURCES:
        workspace = P.Workspace(source, 4095, meter)
        if source == 'mu':
            for degree in (1, 2, 3):
                state = workspace.baseline(degree)
                rows = P.moments(state, TRAIN+VALIDATION, meter)
                baselines[str(degree)] = P.encoded(rows)
                del state
        for item in P.catalogue():
            state = workspace.evaluate(item['program'])
            training = P.moments(state, TRAIN, meter)
            if source == 'mu':
                fitted[str(item['id'])] = constants(training)
                checkpoint(directory, dict(stage='fit_before_validation', id=item['id'],
                                            constants=fitted[str(item['id'])], operations=meter.operations))
            validation = P.moments(state, VALIDATION, meter)
            base = {r['X']: parse(r) for r in baselines[str(item['degree'])]}
            result = dict(**item, source=source, training=P.encoded(training),
                          validation=P.encoded(validation), constants=fitted[str(item['id'])],
                          scores=scores(validation, fitted[str(item['id'])], base),
                          normalizer=[dict(shift=r['shift'], residue=r['residue'].str(45, radius=True),
                                           coefficient=r['coefficient'].str(45, radius=True)) for r in state['normalizer']])
            records.append(result)
            checkpoint(directory, dict(stage='discovery', id=item['id'], source=source, operations=meter.operations))
            del state
        del workspace
    selected = []
    for degree in (1, 2, 3):
        candidates = [r for r in records if r['source'] == 'mu' and r['degree'] == degree]
        best = min(candidates, key=lambda r: (r['scores']['growth_failures'],
                                              r['scores']['worst_full_energy_ratio'], r['id']))
        selected.append(dict(id=best['id'], degree=degree, program=best['program'],
                             constants=best['constants'], scores=best['scores']))
    return dict(records=records, baselines=baselines, selected=selected, counts=meter.counts(), **P.FLAGS)


def worker_meter(cap, deadline):
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, hard))
    meter = P.Meter(cap)
    meter.deadline = deadline
    return meter


def final_worker(source, selected, cap, deadline):
    ctx.prec = 128
    meter = worker_meter(cap, deadline)
    rows, baselines = [], {}
    try:
        workspace = P.Workspace(source, 131071, meter)
        for item in selected:
            state = workspace.evaluate(item['program'])
            rows.append(dict(id=item['id'], degree=item['degree'], program=item['program'],
                             cases=P.encoded(P.moments(state, FINAL, meter))))
            del state
            if source == 'mu':
                state = workspace.baseline(item['degree'])
                baselines[str(item['degree'])] = P.encoded(P.moments(state, FINAL, meter))
                del state
        status, reason = 'available', None
    except (ValueError, ArithmeticError, OverflowError, TimeoutError, MemoryError) as error:
        status, reason = 'incomplete', str(error) or type(error).__name__
    return dict(source=source, status=status, reason=reason, rows=rows, baselines=baselines,
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


def audit_worker(source, discovered, final, cap, deadline):
    import check_shifted_quotient_candidates as C
    ctx.prec = 192
    meter = worker_meter(cap, deadline)
    checked, invalid = [], []
    try:
        values = C.source(source, 4095, meter)
        for row in discovered['records']:
            if row['source'] != source:
                continue
            state = C.evaluate(row['program'], values, meter)
            compare_rows(row['training']+row['validation'], C.moments(state, TRAIN+VALIDATION, meter))
            if len(row['normalizer']) != len(state['normalizer']):
                raise ValueError('all normalizer terms')
            for old, new in zip(row['normalizer'], state['normalizer']):
                if old['shift'] != new['shift']:
                    raise ValueError('normalizer shift')
                for key in ('residue', 'coefficient'):
                    if not arb(old[key]).overlaps(new[key]):
                        raise ArithmeticError('independent complete residue disagreement')
            checked.append(dict(stage='discovery', id=row['id'], cases=8))
            del state
        if source == 'mu':
            for degree in (1, 2, 3):
                state = C.baseline(degree, 4095, meter)
                compare_rows(discovered['baselines'][str(degree)], C.moments(state, TRAIN+VALIDATION, meter))
                checked.append(dict(stage='discovery_baseline', degree=degree, cases=8))
                del state
        if final['status'] != 'available':
            raise ValueError('complete final source evidence required')
        values = C.source(source, 131071, meter)
        for row in final['rows']:
            state = C.evaluate(row['program'], values, meter)
            compare_rows(row['cases'], C.moments(state, FINAL, meter))
            checked.append(dict(stage='final', id=row['id'], cases=2))
            del state
        if source == 'mu':
            for degree in (1, 2, 3):
                state = C.baseline(degree, 131071, meter)
                compare_rows(final['baselines'][str(degree)], C.moments(state, FINAL, meter))
                checked.append(dict(stage='final_baseline', degree=degree, cases=2))
                del state
        status = 'verified'
    except (ValueError, ArithmeticError, OverflowError, TimeoutError, MemoryError) as error:
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
    meter = P.Meter(100000000)
    meter.deadline = deadline
    try:
        discovered = discovery(directory, meter)
    except (ValueError, ArithmeticError, OverflowError, TimeoutError, MemoryError) as error:
        write(directory/'incomplete.json', dict(stage='discovery', error=str(error),
                                               operations=spent+meter.operations, **P.FLAGS))
        return
    spent += meter.operations
    write(directory/'discovery.json', discovered)
    final = {}
    with ProcessPoolExecutor(max_workers=3) as pool:
        futures = {pool.submit(final_worker, s, discovered['selected'], 125000000, deadline): s for s in P.SOURCES}
        for future in as_completed(futures):
            value = future.result()
            final[value['source']] = value
            spent += value['counts']['operations']
            write(directory/('final_'+value['source']+'.json'), value)
            checkpoint(directory, dict(stage='final_source', source=value['source'], status=value['status'], total_operations=spent))
            print(json.dumps(dict(stage='final_source', source=value['source'], status=value['status'], total_operations=spent)), flush=True)
    available = max(0, TOTAL-spent)
    audits = {}
    with ProcessPoolExecutor(max_workers=3) as pool:
        futures = {pool.submit(audit_worker, s, discovered, final[s], available//3, deadline): s for s in P.SOURCES}
        for future in as_completed(futures):
            value = future.result()
            audits[value['source']] = value
            spent += value['counts']['operations']
            write(directory/('audit_'+value['source']+'.json'), value)
            checkpoint(directory, dict(stage='independent_source', source=value['source'], status=value['status'], total_operations=spent))
            print(json.dumps(dict(stage='independent_source', source=value['source'], status=value['status'], total_operations=spent)), flush=True)
    summaries = []
    for item in discovered['selected']:
        cases = {}
        for source in P.SOURCES:
            record = next((r for r in final[source]['rows'] if r['id'] == item['id']), None)
            base = final['mu']['baselines'].get(str(item['degree']))
            if record is not None and base is not None:
                cases[source] = scores([parse(r) for r in record['cases']], item['constants'],
                                       {r['X']: parse(r) for r in base})
        summaries.append(dict(**item, final=cases))
    verify_source(directory)
    verified = all(a['status'] == 'verified' for a in audits.values()) and spent <= TOTAL
    write(directory/'report.json', dict(status='FINITE_INTERVAL_EVALUATIONS_VERIFIED' if verified else 'INCOMPLETE',
                                        selected=summaries, total_operations=spent, work_limit=TOTAL,
                                        preparation_operations=development+frozen+ROOT_RESERVE,
                                        discovery_operations=meter.operations,
                                        final_operations=sum(r['counts']['operations'] for r in final.values()),
                                        audit_operations=sum(r['counts']['operations'] for r in audits.values()),
                                        elapsed_seconds=time.monotonic()-started,
                                        checked_blocks=sum(x['cases'] for a in audits.values() for x in a['checked']),
                                        all_scale_bound_status='open', **P.FLAGS))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['freeze', 'run'])
    parser.add_argument('directory')
    args = parser.parse_args()
    globals()[args.action](args.directory)
