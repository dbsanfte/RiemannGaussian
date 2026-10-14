"""Independent archive and full-polynomial audit of the affine unit diagnostic."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import check_cancellation_complete_gram_program as B
import check_cancellation_anchored_storage as K
import check_cancellation_shared_gram as I
import check_affine_storage_moment_probe as C

ROOT = Path(__file__).resolve().parent
BASE = ROOT/'cancellation-arithmetic-results'
PARENT = BASE/'anchored-storage-leaf-replay-001'
PUBLICATION = BASE/'publication-008'
TESTS = ['test_affine_storage_moment_probe', 'test_check_affine_storage_moment_probe']
FLAGS = dict(global_bound_proved=False, RH_proved=False, larger_cone_feasibility_proved=False)
PROGRAM = dict(target='mu', q=6, C=32, claim='critical', constraint='zero_cubic',
               dictionary_mode='extended', allow_constant_slack=True)
SCALES = [1, 2, 3, 5]
LIMITS = dict(max_horizon=80, max_operations=200000000, max_terms=100000, max_coefficient_bits=4096)
PARALLEL = dict(workers=1, worker_memory_bytes=6*1024**3, memory_budget_bytes=6*1024**3,
                timeout_seconds=1200, max_jobs=1, max_result_bytes=65536)
GRAMMAR = dict(version='affine-anchored-unit-probe-v1', base=K.SPEC, dimension=15,
               atoms=['unit']+K.SPEC['atoms'], prefix_anchor_index=1,
               constant_vector=['1']+['0']*5+['-1/2']*9,
               selection='prepend the constant unit to every complete regional and storage state; retain every pair',
               storage_increment='child minus four parent; signed transport',
               auxiliary_blocks='empty', missing_policy='unknown after exact coefficient cancellation',
               new_floating_search=False)


def read(p):
    return json.loads(p.read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def bind(base, hashes):
    for name, h in hashes.items():
        if sha(base/name) != h:
            raise ValueError('affine audit binding '+str(base/name))


def source_names():
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


def audit(directory):
    d = Path(directory).resolve(); output = d/'independent_verification.json'
    if output.exists():
        raise FileExistsError('exclusive affine audit')
    source = read(d/'source_seal.json')
    if set(source) != set(source_names()):
        raise ValueError('complete frozen affine source closure')
    bind(ROOT, source); bind(d/'frozen_source', source)
    for name in ['protocol', 'source_seal', 'input', 'tests']:
        if read(d/'seal.json')[name+'_sha256'] != sha(d/(name+'.json')):
            raise ValueError('sealed prescore affine '+name)
    inputs = read(d/'input.json')['input_sha256']
    paths = [PARENT/n for n in ['result.json', 'protocol.json', 'source_seal.json', 'receipt.json', 'independent_verification.json']]
    paths += [PUBLICATION/n for n in ['manifest.json', 'report.json']]
    paths += [ROOT/n for n in ['anchored_storage_uniform_scope.txt', 'anchored_storage_resource_authorization.txt']]
    if set(inputs) != {str(p.relative_to(ROOT)) for p in paths}:
        raise ValueError('complete parent admission and authorization binding')
    bind(ROOT, inputs); bind(ROOT, read(PUBLICATION/'manifest.json')['files'])
    bind(PARENT, read(PARENT/'receipt.json')['files_sha256'])
    parent_source = read(PARENT/'source_seal.json')
    bind(ROOT, parent_source); bind(PARENT/'frozen_source', parent_source)
    review = read(PARENT/'independent_verification.json'); bind(PARENT, review['input_sha256'])
    if review.get('all_passed') is not True or review['result_status'] != 'exact_separator' or review['proof']['verified'] is not True:
        raise ValueError('admitted complete full14 separator')
    prior = read(PARENT/'result.json')
    if prior['status'] != 'exact_separator' or prior['synthesis'].get('certified') is not True or prior['program'] != PROGRAM or prior['scales'] != SCALES:
        raise ValueError('declared unchanged complete prior witness')
    protocol = read(d/'protocol.json')
    for key, value in dict(grammar=GRAMMAR, program=PROGRAM, scales=SCALES, build_limits=LIMITS,
                          parallel=PARALLEL, cooperative_seconds=360, tests=TESTS,
                          no_new_floating_search=True, existing_atom_count=14, extended_atom_count=15,
                          native_reconstruction_work=0, **FLAGS).items():
        if protocol.get(key) != value:
            raise ValueError('known complete affine protocol '+key)
    if read(d/'tests.json')['returncode'] != 0:
        raise ValueError('successful prescore affine calibration')
    receipt = read(d/'receipt.json')
    actual = {str(p.relative_to(d)):sha(p) for p in d.rglob('*.json') if p.name != 'receipt.json'}
    if receipt['files_sha256'] != actual or receipt['source_count'] != len(source):
        raise ValueError('complete terminal affine evidence')
    if read(d/'run_started.json') != dict(protocol_sha256=sha(d/'protocol.json')):
        raise ValueError('single immutable affine execution')
    execution = read(d/'execution.json'); cost = execution['cost']
    runtime = dict(workers=1, requested_workers=1, worker_memory_bytes=6*1024**3,
                   memory_budget_bytes=6*1024**3, worker_memory_limit_enforced=True,
                   numerical_threads_per_worker=1, serial_fallback=False)
    for key, value in runtime.items():
        if type(cost.get(key)) is not type(value) or cost[key] != value:
            raise ValueError('actual isolated affine resources '+key)
    if len(execution['results']) != 1 or execution['results'][0]['index'] != 0:
        raise ValueError('one complete diagnostic job')
    row = execution['results'][0]; proof = None; status = row['status']
    if status == 'available':
        value = row['value']
        if value['file'] != 'result.json' or value['sha256'] != sha(d/'result.json'):
            raise ValueError('isolated affine result binding')
        result = read(d/'result.json'); status = result['status']
        if result['cost'] != value['cost'] or status != value['status'] or result['program'] != PROGRAM or result['scales'] != SCALES:
            raise ValueError('actual affine job and resources')
        if result['cost']['elapsed_seconds'] > 360 or result['cost']['observed_threads_at_completion'] != 1:
            raise ValueError('declared affine time and thread envelope')
        if result['grammar_sha256'] != I.digest(GRAMMAR) or result['parent_result_sha256'] != sha(PARENT/'result.json') or result['no_new_floating_search'] is not True or any(result.get(k) is not False for k in FLAGS):
            raise ValueError('finite exact parent witness diagnostic')
        built = [B.build_blocks(X, **LIMITS) for X in SCALES]
        blocks = [b['blocks'] for b in built]+[dict(full_child=[], full_parent=[])]
        horizons = [4*X-1 for X in SCALES]+[1]
        metadata = dict(gram_block_hashes=list(map(I.digest, blocks)),
                        gram_archive_hashes=[I.digest(b['archive']) for b in built])
        if result['horizons'] != horizons:
            raise ValueError('all source horizons including empty auxiliary')
        for key, value in metadata.items():
            if result[key] != value or prior[key] != value:
                raise ValueError('all independently rebuilt source atoms '+key)
        proof = C.verify(blocks, horizons, prior['synthesis'], result['probe'])
        if proof['status'] != status:
            raise ValueError('no diagnostic status promotion')
    elif status not in ['missing_resource', 'error'] or (d/'result.json').exists():
        raise ValueError('honest diagnostic resource or execution failure')
    admission = dict(all_passed=True, result_status=status, proof=proof,
                     source_count=len(source), no_new_floating_search=True,
                     input_sha256={n:sha(d/n) for n in ['protocol.json', 'source_seal.json', 'input.json',
                                    'tests.json', 'seal.json', 'execution.json', 'receipt.json']}, **FLAGS)
    with output.open('x') as stream:
        json.dump(admission, stream, sort_keys=True, indent=2); stream.write('\n')
    return admission


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('directory')
    result = audit(parser.parse_args().directory)
    print(json.dumps(dict(all_passed=result['all_passed'], result_status=result['result_status'])))
