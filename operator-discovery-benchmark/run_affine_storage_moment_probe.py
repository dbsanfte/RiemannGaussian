"""Freeze and replay the complete unit extension of an admitted storage dual."""
import argparse
import ast
import json
import os
import resource
import subprocess
import sys
import time
from pathlib import Path

import run_detector as R
from detector_parallel import run_jobs
from detector_workflow_guard import require_verified_runtime
import check_cancellation_complete_gram_program as B
import affine_storage_moment_probe as A

ROOT = Path(__file__).resolve().parent
BASE = ROOT/'cancellation-arithmetic-results'
PARENT = BASE/'anchored-storage-leaf-replay-001'
PUBLICATION = BASE/'publication-008'
FLAGS = dict(A.FLAGS)
TESTS = ['test_affine_storage_moment_probe', 'test_check_affine_storage_moment_probe']
PROGRAM = dict(target='mu', q=6, C=32, claim='critical', constraint='zero_cubic',
               dictionary_mode='extended', allow_constant_slack=True)
SCALES = [1, 2, 3, 5]
LIMITS = dict(max_horizon=80, max_operations=200000000, max_terms=100000,
              max_coefficient_bits=4096)
PARALLEL = dict(workers=1, worker_memory_bytes=6*1024**3, memory_budget_bytes=6*1024**3,
                timeout_seconds=1200, max_jobs=1, max_result_bytes=65536)


def sources():
    pending = ['run_affine_storage_moment_probe', 'check_affine_storage_probe_run', *TESTS]
    seen = set()
    while pending:
        name = pending.pop(); path = ROOT/(name+'.py')
        if name in seen or not path.is_file():
            continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def bind(base, hashes):
    for n, h in hashes.items():
        if R.sha(base/n) != h:
            raise ValueError('immutable affine input '+str(base/n))


def input_names():
    paths = [PARENT/n for n in ['result.json', 'protocol.json', 'source_seal.json',
             'receipt.json', 'independent_verification.json']]
    paths += [PUBLICATION/n for n in ['manifest.json', 'report.json']]
    paths += [ROOT/n for n in ['anchored_storage_uniform_scope.txt',
                              'anchored_storage_resource_authorization.txt']]
    return sorted(str(p.relative_to(ROOT)) for p in paths)


def parent_bindings():
    bind(ROOT, R.read(PUBLICATION/'manifest.json')['files'])
    bind(PARENT, R.read(PARENT/'receipt.json')['files_sha256'])
    source = R.read(PARENT/'source_seal.json')
    bind(ROOT, source); bind(PARENT/'frozen_source', source)
    review = R.read(PARENT/'independent_verification.json')
    if review.get('all_passed') is not True or review.get('result_status') != 'exact_separator' or review['proof'].get('verified') is not True:
        raise ValueError('independently admitted complete anchored separator')
    bind(PARENT, review['input_sha256'])
    prior = R.read(PARENT/'result.json')
    if prior['status'] != 'exact_separator' or prior['synthesis'].get('certified') is not True or prior['program'] != PROGRAM or prior['scales'] != SCALES:
        raise ValueError('unchanged declared parent witness')
    if any(prior.get(k) is not False for k in ['RH_proved', 'global_bound_proved']):
        raise ValueError('finite parent scope')
    return prior


def protocol():
    return dict(schema=1, grammar=A.SPEC, program=PROGRAM, scales=SCALES,
                build_limits=LIMITS, parallel=PARALLEL, cooperative_seconds=360,
                tests=TESTS, no_new_floating_search=True,
                source_selection='all unit pairs in all three complete anchored groups; no selection from signed response data',
                existing_atom_count=14, extended_atom_count=15,
                native_reconstruction_work=0,
                decisions=dict(witness_invalid_for_affine_cone='consider a new full15 certificate search; feasibility remains unproved',
                               witness_extends_to_affine_cone='the same separator excludes the fixed affine cone on the declared grid',
                               unknown_missing_coordinates='retain unknown; do not impute unsupported moments'),
                **FLAGS)


def freeze(directory):
    require_verified_runtime(); parent_bindings()
    d = Path(directory).resolve(); d.mkdir(parents=True, exist_ok=False)
    (d/'frozen_source').mkdir(); hashes = {}
    for n in sources():
        (d/'frozen_source'/n).write_bytes((ROOT/n).read_bytes()); hashes[n] = R.sha(ROOT/n)
    test = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS],
                          cwd=ROOT, capture_output=True, text=True, timeout=120)
    R.write(d/'tests.json', dict(returncode=test.returncode, stdout=test.stdout, stderr=test.stderr))
    if test.returncode:
        raise ValueError('affine full-product calibration failed')
    R.write(d/'protocol.json', protocol()); R.write(d/'source_seal.json', hashes)
    R.write(d/'input.json', dict(input_sha256={n:R.sha(ROOT/n) for n in input_names()}))
    R.write(d/'seal.json', {n+'_sha256':R.sha(d/(n+'.json')) for n in ['protocol', 'source_seal', 'input', 'tests']})
    return dict(directory=str(d), frozen_sources=len(hashes), scored=False)


def validate(directory):
    d = Path(directory); seal = R.read(d/'seal.json')
    for n in ['protocol', 'source_seal', 'input', 'tests']:
        if seal[n+'_sha256'] != R.sha(d/(n+'.json')):
            raise ValueError('sealed affine preregistration '+n)
    source = R.read(d/'source_seal.json')
    if set(source) != set(sources()):
        raise ValueError('complete affine source closure')
    bind(ROOT, source); bind(d/'frozen_source', source)
    inputs = R.read(d/'input.json')['input_sha256']
    if set(inputs) != set(input_names()):
        raise ValueError('all admitted parent bindings')
    bind(ROOT, inputs)
    if R.read(d/'protocol.json') != protocol() or R.read(d/'tests.json')['returncode'] != 0:
        raise ValueError('declared affine grammar and successful prescore calibration')
    return parent_bindings()


def geometry(prior):
    built = [B.build_blocks(X, **LIMITS) for X in SCALES]
    blocks = [b['blocks'] for b in built]+[dict(full_child=[], full_parent=[])]
    horizons = [4*X-1 for X in SCALES]+[1]
    metadata = dict(gram_block_hashes=list(map(R.digest, blocks)),
                    gram_archive_hashes=[R.digest(b['archive']) for b in built])
    for key, value in metadata.items():
        if prior[key] != value:
            raise ValueError('unchanged complete source '+key)
    return blocks, horizons, metadata


def worker(job):
    require_verified_runtime(); d = Path(job['directory']); prior = validate(d)
    if (d/'result.json').exists():
        raise FileExistsError('exclusive affine result')
    start = time.monotonic(); cpu = time.process_time()
    blocks, horizons, metadata = geometry(prior)
    probe = A.moments(blocks, horizons, prior['synthesis'])
    if time.monotonic()-start > 360:
        raise TimeoutError('affine diagnostic cooperative time bound')
    result = dict(status=probe['status'], probe=probe, program=PROGRAM, scales=SCALES,
                  horizons=horizons, grammar_sha256=R.digest(A.SPEC),
                  parent_result_sha256=R.sha(PARENT/'result.json'),
                  no_new_floating_search=True, **metadata, **FLAGS)
    result['cost'] = dict(elapsed_seconds=time.monotonic()-start,
                         cpu_seconds=time.process_time()-cpu,
                         peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                         pid=os.getpid(), observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())))
    validate(d); R.write(d/'result.json', result)
    return dict(file='result.json', sha256=R.sha(d/'result.json'), status=result['status'],
                cost=result['cost'], **FLAGS)


def run(directory):
    require_verified_runtime(); d = Path(directory).resolve(); validate(d)
    with (d/'run_started.json').open('x') as stream:
        json.dump(dict(protocol_sha256=R.sha(d/'protocol.json')), stream)
    execution = run_jobs([dict(directory=str(d))], worker='run_affine_storage_moment_probe:worker', **PARALLEL)
    R.write(d/'execution.json', execution); validate(d)
    R.write(d/'receipt.json', dict(files_sha256={str(p.relative_to(d)):R.sha(p) for p in sorted(d.rglob('*.json'))},
                                 source_count=len(R.read(d/'source_seal.json')), no_new_floating_search=True, **FLAGS))
    return dict(process_status=execution['results'][0]['status'], result=execution['results'][0].get('value'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['freeze', 'run']); parser.add_argument('directory')
    args = parser.parse_args()
    print(json.dumps((freeze if args.command == 'freeze' else run)(args.directory)))
