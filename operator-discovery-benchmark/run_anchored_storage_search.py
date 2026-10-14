"""Frozen anchored-storage signed search with exact recovery-aware admission."""
import argparse
import ast
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import run_detector as R
from detector_parallel import run_jobs
from detector_workflow_guard import require_verified_runtime
import cancellation_anchored_storage as P

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
PROBE = BASE / 'complete-gram-storage-probe-001'
FLAGS = dict(global_bound_proved=False, RH_proved=False)
PROGRAM = dict(target='mu', q=6, C=32, claim='critical', constraint='zero_cubic',
               dictionary_mode='extended', allow_constant_slack=True)
LIMITS = dict(R.DEFAULT_LIMITS, time_limit=180, max_columns=2048, max_monomials=100000)
SOLVER_LIMITS = dict(LIMITS, max_exact_work=450000000, max_exact_cells=4000000,
                     max_checkpoint_bytes=8388608, row_normalization=True)
DUAL_LIMITS = dict(time_limit=180, max_rows=2500, max_variables=60000, max_work=450000000,
                   max_cells=4000000, max_preprocessing_operations=200000000,
                   max_preprocessing_cells=4000000, max_checkpoint_bytes=8388608,
                   max_denominator=2**4096, max_coefficient_bits=4096,
                   max_columns=2048, max_monomials=100000, max_operations=200000000,
                   max_horizon=80, max_degree=12)
PARALLEL = dict(workers=1, worker_memory_bytes=6*1024**3, memory_budget_bytes=6*1024**3,
                timeout_seconds=600, max_jobs=8, max_result_bytes=65536)
TESTS = ['test_check_cancellation_complete_gram_program', 'test_cancellation_anchored_storage',
         'test_cancellation_anchored_storage_synthesis', 'test_cancellation_anchored_storage_dual',
         'test_check_cancellation_anchored_storage', 'test_run_anchored_storage_search',
         'test_check_anchored_storage_search']
INPUTS = ['cancellation-arithmetic-results/publication-007/manifest.json',
          'cancellation-arithmetic-results/publication-007/report.json',
          'anchored_storage_uniform_scope.txt'] + [
          'cancellation-arithmetic-results/complete-gram-storage-probe-001/' + name
          for name in ['protocol.json', 'result.json', 'receipt.json', 'verification.json']]



def sources():
    pending = ['run_anchored_storage_search', 'check_anchored_storage_search', *TESTS]; seen = set()
    while pending:
        name = pending.pop(); path = ROOT / (name + '.py')
        if name in seen or not path.is_file():
            continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split('.')[0])
    return sorted(name + '.py' for name in seen)


def validate_inputs():
    for name, h in R.read(BASE / 'publication-007/manifest.json')['files'].items():
        if R.sha(ROOT / name) != h:
            raise ValueError('published evidence changed: ' + name)
    review = R.read(PROBE / 'verification.json')
    if review.get('all_passed') is not True:
        raise ValueError('replayed anchored storage diagnostic required')
    for name, h in review['input_sha256'].items():
        if R.sha(PROBE / name) != h:
            raise ValueError('completion probe admission changed: ' + name)
    result = R.read(PROBE / 'result.json')
    if result['status'] != 'witness_invalid_for_anchored_storage_cone':
        raise ValueError('anchored storage witness diagnostic required')
    if result['larger_cone_feasibility_proved'] is not False or result['uniform_innovation_bound_proved'] is not False:
        raise ValueError('diagnostic is not an estimate')



def freeze(directory):
    require_verified_runtime(); validate_inputs()
    for name in ['check_anchored_storage_search', *TESTS]:
        if not (ROOT / (name + '.py')).is_file():
            raise FileNotFoundError(name)
    d = Path(directory).resolve(); d.mkdir(parents=True, exist_ok=False)
    (d / 'frozen_source').mkdir(); (d / 'jobs').mkdir(); hashes = {}
    for name in sources():
        (d / 'frozen_source' / name).write_bytes((ROOT / name).read_bytes()); hashes[name] = R.sha(ROOT / name)
    protocol = dict(schema=1, program=PROGRAM, training_scales=[1,2,3,5], final_scales=[8,13],
                    language=P.SPEC, gram_specs=P.gram_specs(), storage_operator=P.SPEC,
                    dictionary=P.C.descriptors(), limits=LIMITS, solver_limits=SOLVER_LIMITS,
                    dual_limits=DUAL_LIMITS, parallel=PARALLEL, tests=TESTS,
                    strategy='exact storage-cone dual pruning first; otherwise primal; only admitted anchored primal transfers',
                    unsigned_calibration='K=0 embeds prior supplied unsigned calibration; no repeated unsigned optimization',
                    recovery_scope='R=e_prefix e_prefix^T+K; fixed PSD K; uniform innovation still unproved',
                    final_refit=False, no_actual_signed_response_inputs=True,
                    evaluation_scope='historical development scales, not unseen arithmetic data',
                    **FLAGS)
    R.write(d / 'protocol.json', protocol); R.write(d / 'source_seal.json', hashes)
    R.write(d / 'input.json', dict(input_sha256={n: R.sha(ROOT / n) for n in INPUTS}))
    R.write(d / 'seal.json', dict(protocol_sha256=R.sha(d / 'protocol.json'),
                                 source_seal_sha256=R.sha(d / 'source_seal.json'), input_sha256=R.sha(d / 'input.json')))
    return d


def validate(directory):
    d = Path(directory); seal = R.read(d / 'seal.json')
    for name in ['protocol', 'source_seal', 'input']:
        if seal[name+'_sha256'] != R.sha(d / (name+'.json')):
            raise ValueError('complete search seal changed: '+name)
    source = R.read(d / 'source_seal.json')
    if set(source) != set(sources()):
        raise ValueError('complete executed source closure')
    for name, h in source.items():
        if R.sha(ROOT / name) != h or R.sha(d / 'frozen_source' / name) != h:
            raise ValueError('frozen source changed: '+name)
    inputs = R.read(d / 'input.json')['input_sha256']
    if set(inputs) != set(INPUTS):
        raise ValueError('complete prior evidence binding')
    for name, h in inputs.items():
        if R.sha(ROOT / name) != h:
            raise ValueError('bound input changed: '+name)
    validate_inputs()


def worker(job):
    require_verified_runtime(); d = Path(job['directory']); validate(d)
    if (d / 'receipt.json').exists():
        raise FileExistsError('sealed run is immutable')
    import check_cancellation_anchored_storage as CHECK
    from cancellation_anchored_storage_synthesis import synthesize, instantiate_certificate
    from cancellation_anchored_storage_dual import propose
    spec = R.read(d / 'protocol.json'); phase = job['phase']; index = job['index']
    start = time.monotonic(); cpu = time.process_time()
    out = dict(phase=phase, index=index, program=spec['program'], refitted=False, **FLAGS)
    try:
        scales = [spec['final_scales'][index]] if phase == 'final' else spec['training_scales']
        if phase not in ['dual', 'primal', 'final']:
            raise ValueError('known phase')
        if phase == 'final' and R.sha(d / 'candidate.json') != job['candidate_sha256']:
            raise ValueError('fixed candidate seal')
        built = [P.build(spec['program'], X) for X in scales]
        instances = [b['instance'] for b in built]; blocks = [b['gram_blocks'] for b in built]
        storage = [b['storage_blocks'] for b in built]
        out.update(scales=scales, ordinary_case_hashes=list(map(R.digest, instances)),
                   factor_archive_hashes=[R.digest(b['factor_archive']) for b in built],
                   divisor_archive_hashes=[R.digest(b['divisor_archive']) for b in built],
                   cell_archive_hashes=[R.digest(b['cell_archive']) for b in built],
                   gram_archive_hashes=[R.digest(b['gram_archive']) for b in built],
                   dictionary_sha256=R.digest(spec['dictionary']), gram_specs=spec['gram_specs'])
        if phase != 'final':
            aux = P.auxiliary(); instances.append(aux['instance']); blocks.append(aux['gram_blocks']); storage.append(aux['storage_blocks'])
        out.update(case_hashes=list(map(R.digest, instances)), gram_block_hashes=list(map(R.digest, blocks)), storage_block_hashes=list(map(R.digest, storage)))
        def checkpoint(value):
            name = f'jobs/{phase}-{index:03d}-proposal.json'; temporary = d / (name+'.tmp')
            R.write(temporary, value); os.replace(temporary, d / name)
            out['proposal_checkpoint'] = dict(file=name, sha256=R.sha(d / name))
        if phase == 'dual':
            result = propose(instances, blocks, storage, gram_specs=spec['gram_specs'], on_checkpoint=checkpoint, **spec['dual_limits'])
        elif phase == 'primal':
            result = synthesize(instances, blocks, storage, gram_specs=spec['gram_specs'], on_checkpoint=checkpoint, **spec['solver_limits'])
        else:
            candidate = R.read(d / 'candidate.json'); path = d / candidate['attempt_file']
            if R.sha(path) != candidate['attempt_sha256']:
                raise ValueError('fixed accepted primal binding')
            accepted = R.read(path)['synthesis']; weights = accepted['weights']; grams = accepted['grams']
            record = instantiate_certificate(instances[0], weights, grams, blocks[0], storage[0], **spec['limits'])
            result = dict(status='finite_PSD_certificate', weights=weights, grams=grams, gram_specs=spec['gram_specs'],
                          source_hashes=out['case_hashes'], gram_block_hashes=out['gram_block_hashes'], storage_block_hashes=out['storage_block_hashes'],
                          certificates=[record], constant_slacks=[record['constant_slack']], **FLAGS)
            out.update(weights_sha256=R.digest(weights), grams_sha256=R.digest(grams))
        if result['status'] == 'exact_separator':
            check = CHECK.verify_dual(instances, blocks, storage, spec['gram_specs'], result)
        elif result['status'] == 'finite_PSD_certificate':
            check = CHECK.verify_primal(instances, blocks, storage, spec['gram_specs'], result)
        else:
            check = dict(verified=False, status=result['status'], **FLAGS)
        out.update(status=result['status'], synthesis=result, independent_check=check)
    except (OverflowError, TimeoutError, MemoryError, ImportError) as error:
        out.update(status='missing_resource', reason=str(error) or type(error).__name__)
    except (ValueError, TypeError, KeyError, RuntimeError, ZeroDivisionError) as error:
        out.update(status='rejected', reason=str(error) or type(error).__name__)
    out['cost'] = dict(elapsed_seconds=time.monotonic()-start, cpu_seconds=time.process_time()-cpu,
                       peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                       observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())), pid=os.getpid())
    validate(d); name = f'jobs/{phase}-{index:03d}.json'; R.write(d / name, out)
    return dict(file=name, sha256=R.sha(d / name), status=out['status'], cost=out['cost'], **FLAGS)


def terminal_status(d, execution):
    row = execution['results'][0]
    if row['status'] != 'available':
        return row['status']
    value = row['value']; path = d / value['file']
    if R.sha(path) != value['sha256']:
        raise ValueError('ordered result binding')
    record = R.read(path)
    if record['status'] in ['exact_separator', 'finite_PSD_certificate'] and record['independent_check']['verified'] is not True:
        raise ValueError('exact independent admission required')
    return record['status']


def run(directory):
    require_verified_runtime(); d = Path(directory).resolve(); validate(d)
    if (d / 'tests.json').exists():
        raise FileExistsError('search already started')
    test = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=ROOT,
                          capture_output=True, text=True, timeout=180)
    R.write(d / 'tests.json', dict(returncode=test.returncode, stdout=test.stdout, stderr=test.stderr))
    if test.returncode:
        raise ValueError('pre-score calibration failed')
    def execute(phase):
        result = run_jobs([dict(directory=str(d), phase=phase, index=0)], worker='run_anchored_storage_search:worker', **PARALLEL)
        R.write(d / (phase+'_execution.json'), result); return result
    dual = execute('dual'); dual_status = terminal_status(d, dual)
    decision = dict(dual_status=dual_status, run_primal=dual_status != 'exact_separator', final_scales=[])
    if decision['run_primal']:
        primal = execute('primal'); status = terminal_status(d, primal); decision['primal_status'] = status
        if status == 'finite_PSD_certificate':
            value = primal['results'][0]['value']
            candidate = dict(attempt_file=value['file'], attempt_sha256=value['sha256'], final_scales=[8,13])
            R.write(d / 'candidate.json', candidate); candidate_sha = R.sha(d / 'candidate.json')
            final = run_jobs([dict(directory=str(d), phase='final', index=i, candidate_sha256=candidate_sha) for i in range(2)],
                             worker='run_anchored_storage_search:worker', **PARALLEL)
            R.write(d / 'final_execution.json', final); decision['final_scales'] = [8,13]
            if R.sha(d / 'candidate.json') != candidate_sha:
                raise ValueError('candidate changed during fixed transfer')
    R.write(d / 'decision.json', decision); validate(d)
    R.write(d / 'receipt.json', dict(files_sha256={str(p.relative_to(d)): R.sha(p) for p in sorted(d.rglob('*.json'))},
                                   source_count=len(R.read(d / 'source_seal.json')), refitted=False, **FLAGS))
    print(decision)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['freeze','run']); parser.add_argument('directory')
    args = parser.parse_args(); (freeze if args.command == 'freeze' else run)(args.directory)
