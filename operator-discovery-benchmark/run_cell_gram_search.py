"""Freeze and run full shared divisor-cell PSD searches with exact admission."""
import argparse
import ast
import importlib.metadata
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import run_detector as R
from detector_parallel import run_jobs
from detector_workflow_guard import require_verified_runtime
import cancellation_cell_gram_program as P

ROOT = Path(__file__).resolve().parent
FLAGS = dict(global_bound_proved=False, RH_proved=False)
TESTS = ['test_cancellation_shared_gram_synthesis', 'test_check_cancellation_shared_gram',
         'test_cancellation_shared_gram_dual', 'test_check_cancellation_cell_gram_program',
         'test_run_cell_gram_search']
LIMITS = dict(R.DEFAULT_LIMITS, time_limit=180, max_columns=2048, max_monomials=100000)
SOLVER_LIMITS = dict(LIMITS, max_exact_cells=4000000, max_exact_work=2000000000)
DUAL_LIMITS = dict(time_limit=180, max_rows=2500, max_variables=60000, max_work=400000000,
                   max_cells=4000000, max_denominator=2**4096, max_coefficient_bits=4096,
                   max_columns=2048, max_monomials=100000, max_operations=200000000,
                   max_horizon=80, max_degree=12)


def sources():
    pending = ['run_cell_gram_search', 'check_cell_gram_search', *TESTS]
    seen = set()
    while pending:
        name = pending.pop()
        path = ROOT / (name + '.py')
        if name in seen or not path.is_file():
            continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split('.')[0])
    return sorted(n + '.py' for n in seen)


def freeze(directory):
    require_verified_runtime()
    for name in ['check_cell_gram_search', *TESTS]:
        if not (ROOT / (name + '.py')).is_file():
            raise FileNotFoundError(name)
    d = Path(directory).resolve()
    programs = R.read(ROOT / 'detector_resource_search.json')['programs']
    protocol = dict(schema=1, language=P.SPEC, dictionary=P.C.descriptors(),
                    gram_specs=P.gram_specs(), gram_groups=P.group_descriptors(), programs=programs,
                    training_scales=[1, 2, 3, 5], final_scales=[8, 13], limits=LIMITS,
                    solver_limits=SOLVER_LIMITS, dual_limits=DUAL_LIMITS, tests=TESTS,
                    parallel=dict(workers=2, worker_memory_bytes=2*1024**3, memory_budget_bytes=4*1024**3,
                                  timeout_seconds=600, max_jobs=64, max_result_bytes=65536),
                    solver='sparse full shared PSD proposal; native exact equality and rational PSD admission',
                    dual_rule='one diagonal-moment proposal checked against all complete shared PSD blocks if critical not accepted',
                    no_actual_signed_response_inputs=True, final_refit=False,
                    conditioning='all 18 cell matrices and both legacy matrices fixed before scores; diagnostic motivated broader mixing',
                    evaluation_scope='unchanged-weight and unchanged-matrix transfer; historical scales reused, not unseen arithmetic data',
                    auxiliary='gamma=0 necessary gate; all new cell Gram scalar charges explicitly retained and O(X)',
                    recovery='unchanged complete original signed defect and all source complements',
                    runtime=dict(python=sys.version, packages={n: importlib.metadata.version(n)
                                 for n in ['numpy', 'scipy', 'python-flint', 'cvxpy', 'clarabel']}), **FLAGS)
    names = ['cancellation-arithmetic-results/publication-004/manifest.json',
             'detector-performance-results/publication-001/manifest.json',
             'cancellation-arithmetic-results/divisor-cell-gram-probe-001/independent_verification.json',
             'detector_resource_search.json']
    inputs = {n: R.sha(ROOT / n) for n in names}
    for path in names[:2]:
        for name, h in R.read(ROOT / path)['files'].items():
            if R.sha(ROOT / name) != h:
                raise ValueError('prior publication changed: ' + name)
    d.mkdir(parents=True, exist_ok=False)
    (d / 'frozen_source').mkdir(); (d / 'jobs').mkdir()
    hashes = {}
    for name in sources():
        data = (ROOT / name).read_bytes()
        (d / 'frozen_source' / name).write_bytes(data)
        hashes[name] = R.sha(ROOT / name)
    R.write(d / 'protocol.json', protocol)
    R.write(d / 'source_seal.json', hashes)
    R.write(d / 'input.json', dict(input_sha256=inputs))
    R.write(d / 'seal.json', dict(protocol_sha256=R.sha(d / 'protocol.json'),
            source_seal_sha256=R.sha(d / 'source_seal.json'), input_sha256=R.sha(d / 'input.json')))
    return d


def validate(d):
    R.validate_sources(d)
    for name, h in R.read(Path(d) / 'input.json')['input_sha256'].items():
        if R.sha(ROOT / name) != h:
            raise ValueError('bound input changed: ' + name)


def worker(job):
    require_verified_runtime()
    d = Path(job['directory']); validate(d)
    if (d / 'receipt.json').exists():
        raise FileExistsError('sealed run is immutable')
    import check_cancellation_cell_gram_program as B
    import check_cancellation_shared_gram as CHECK
    from cancellation_shared_gram_synthesis import synthesize, instantiate_certificate
    from cancellation_shared_gram_dual import propose
    spec = R.read(d / 'protocol.json'); phase = job['phase']; index = job['index']
    start = time.monotonic(); cpu = time.process_time()
    out = dict(phase=phase, index=index, refitted=False, **FLAGS)
    try:
        if phase == 'train':
            program = spec['programs'][index]; scales = spec['training_scales']
        else:
            if R.sha(d / 'candidate_seal.json') != job['candidate_seal_sha256']:
                raise ValueError('candidate plan changed')
            plan = R.read(d / 'candidate_seal.json')
            if R.sha(d / 'training.json') != plan['training_sha256']:
                raise ValueError('training binding changed')
            followup = plan['jobs'][index]; program = followup['program']
            if followup['phase'] != phase:
                raise ValueError('phase binding')
            scales = [followup['X']] if phase == 'final' else spec['training_scales']
        if program['allow_constant_slack'] is not True:
            raise ValueError('this protocol declares nonnegative scalar slack')
        built = [B.build(program, X) for X in scales]
        instances = [v['instance'] for v in built]; blocks = [v['gram_blocks'] for v in built]
        out.update(program=program, scales=scales, ordinary_case_hashes=list(map(R.digest, instances)),
                   factor_archive_hashes=[R.digest(b['factor_archive']) for b in built],
                   divisor_archive_hashes=[R.digest(b['divisor_archive']) for b in built],
                   cell_archive_hashes=[R.digest(b['cell_archive']) for b in built],
                   gram_archive_hashes=[R.digest(b['gram_archive']) for b in built],
                   dictionary_sha256=R.digest(spec['dictionary']), gram_specs=B.gram_specs())
        if phase in ['train', 'dual'] and program['constraint'] == 'zero_cubic':
            aux = B.auxiliary(); instances.append(aux['instance']); blocks.append(aux['gram_blocks'])
        out.update(case_hashes=list(map(R.digest, instances)), gram_block_hashes=list(map(R.digest, blocks)))
        if phase == 'train':
            result = synthesize(instances, blocks, gram_specs=spec['gram_specs'], **spec['solver_limits'])
        elif phase == 'final':
            path = d / followup['attempt_file']
            if R.sha(path) != followup['attempt_sha256']:
                raise ValueError('accepted candidate binding')
            accepted = R.read(path)['synthesis']; weights = accepted['weights']; grams = accepted['grams']
            record = instantiate_certificate(instances[0], weights, grams, blocks[0], **spec['limits'])
            result = dict(status='finite_PSD_certificate', weights=weights, grams=grams,
                          gram_specs=spec['gram_specs'], source_hashes=out['case_hashes'],
                          gram_block_hashes=out['gram_block_hashes'], certificates=[record],
                          constant_slacks=[record['constant_slack']], **FLAGS)
            out.update(weights_sha256=R.digest(weights), grams_sha256=R.digest(grams))
        else:
            result = propose(instances, blocks, gram_specs=spec['gram_specs'], **spec['dual_limits'])
        if result['status'] == 'finite_PSD_certificate':
            check = CHECK.verify_primal(instances, blocks, spec['gram_specs'], result)
        elif result['status'] == 'exact_separator':
            check = CHECK.verify_dual(instances, blocks, spec['gram_specs'], result)
        else:
            check = dict(verified=False, status=result['status'], finite_only=True, **FLAGS)
        out.update(status=result['status'], synthesis=result, independent_check=check)
        if phase != 'train' and R.sha(d / 'candidate_seal.json') != job['candidate_seal_sha256']:
            raise ValueError('candidate plan changed during evaluation')
    except (OverflowError, TimeoutError, MemoryError, ImportError) as e:
        out.update(status='missing_resource', reason=str(e) or type(e).__name__)
    except (ValueError, TypeError, KeyError, ZeroDivisionError, RuntimeError) as e:
        out.update(status='rejected', reason=str(e) or type(e).__name__)
    out['cost'] = dict(elapsed_seconds=time.monotonic()-start, cpu_seconds=time.process_time()-cpu,
                       peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                       observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())), pid=os.getpid())
    validate(d)
    name = f'jobs/{phase}-{index:03d}.json'; R.write(d / name, out)
    return dict(file=name, sha256=R.sha(d / name), status=out['status'], cost=out['cost'], **FLAGS)


def run(directory):
    require_verified_runtime()
    d = Path(directory).resolve(); validate(d); spec = R.read(d / 'protocol.json')
    if (d / 'tests.json').exists():
        raise FileExistsError('run already started')
    t = subprocess.run([sys.executable, '-B', '-m', 'unittest', *spec['tests']], cwd=ROOT,
                       capture_output=True, text=True, timeout=180)
    R.write(d / 'tests.json', dict(returncode=t.returncode, stdout=t.stdout, stderr=t.stderr))
    if t.returncode:
        raise ValueError('pre-score calibrations failed')
    train = run_jobs([dict(directory=str(d), phase='train', index=i) for i in range(len(spec['programs']))],
                     worker='run_cell_gram_search:worker', **spec['parallel'])
    R.write(d / 'training.json', train)
    jobs = []
    for i, receipt in enumerate(train['results']):
        if receipt['status'] == 'available' and receipt['value']['status'] == 'finite_PSD_certificate':
            value = receipt['value']; attempt = R.read(d / value['file'])
            if R.sha(d / value['file']) != value['sha256'] or not attempt['independent_check']['verified']:
                raise ValueError('accepted training receipt')
            jobs.extend(dict(phase='final', program=spec['programs'][i], X=X,
                             attempt_file=value['file'], attempt_sha256=value['sha256']) for X in spec['final_scales'])
        elif spec['programs'][i]['claim'] == 'critical':
            jobs.append(dict(phase='dual', program=spec['programs'][i]))
    R.write(d / 'candidate_seal.json', dict(training_sha256=R.sha(d / 'training.json'), jobs=jobs))
    candidate_hash = R.sha(d / 'candidate_seal.json')
    follow = run_jobs([dict(directory=str(d), phase=j['phase'], index=i, candidate_seal_sha256=candidate_hash)
                       for i, j in enumerate(jobs)], worker='run_cell_gram_search:worker', **spec['parallel'])
    if R.sha(d / 'candidate_seal.json') != candidate_hash:
        raise ValueError('candidate plan changed')
    R.write(d / 'followup.json', follow); validate(d)
    R.write(d / 'receipt.json', dict(files_sha256={str(p.relative_to(d)): R.sha(p) for p in sorted(d.rglob('*.json'))},
                                   source_count=len(R.read(d / 'source_seal.json')), refitted=False, **FLAGS))
    print(R.digest(R.read(d / 'receipt.json')))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('command', choices=['freeze', 'run']); p.add_argument('directory')
    args = p.parse_args()
    (freeze if args.command == 'freeze' else run)(args.directory)
