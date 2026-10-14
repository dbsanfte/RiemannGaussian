"""Replay the bounded source-identity calibration and every FORMAL_EQ certificate."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import time

import check_parametric_arithmetic_identity as C
import primitive_state_parametric_sources as S

ROOT = Path(__file__).resolve().parent
FLAGS = dict(S.FLAGS)
TESTS = ['test_parametric_arithmetic_identity', 'test_check_parametric_arithmetic_identity',
         'test_parametric_identity_soundness', 'test_primitive_state_parametric_sources',
         'test_run_parametric_source_identities', 'test_check_parametric_source_identities_run']
LIMITS = dict(C.LIMITS, max_operations=1000000, max_receipt_bytes=65536)
RESOURCES = dict(memory_bytes=2*1024**3, cooperative_seconds=300, max_work=450000000,
                 producer_reserve=74000000, worker_checker_reserve=74000000,
                 whole_audit_reserve=100000000, binding_io_reserve=100000000, test_reserve=25000000,
                 total_work_reserve=373000000, max_source_bytes=2097152,
                 max_recipe_bytes=4194304, max_metadata_bytes=65536, max_check_bytes=8192)


def require(test, message):
    if not test:
        raise ValueError(message)


def sources():
    pending = ['run_parametric_source_identities', 'check_parametric_source_identities_run', *TESTS]
    found = set()
    while pending:
        name = pending.pop()
        path = ROOT / (name + '.py')
        if name in found or not path.is_file():
            continue
        found.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                pending.extend(alias.name.split('.')[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split('.')[0])
    return sorted(name + '.py' for name in found)


def audit(directory, *, write=False, max_operations=100000000, time_limit=300):
    require(type(max_operations) is int and 0 < max_operations <= 100000000, 'bounded whole-audit work')
    require(type(time_limit) is int and 0 < time_limit <= 300, 'bounded whole-audit deadline')
    d = Path(directory).resolve()
    if write and (d / 'independent_verification.json').exists():
        raise FileExistsError('independent calibration review already exists')
    started = time.monotonic()
    deadline = started + time_limit
    operations = 0
    def charge(n):
        nonlocal operations
        operations += n
        if operations > max_operations:
            raise OverflowError('whole parametric audit work')
        if time.monotonic() > deadline:
            raise TimeoutError('whole parametric audit deadline')
    def read(path, cap=65536):
        size = path.stat().st_size
        require(size <= cap, 'bounded reviewed artifact')
        charge(2*(size//64+1))
        return json.loads(path.read_bytes())
    def sha(path):
        charge(path.stat().st_size//64+1)
        h = hashlib.sha256()
        with path.open('rb') as stream:
            for part in iter(lambda: stream.read(1048576), b''):
                h.update(part)
        return h.hexdigest()
    def scoped(value):
        for key in FLAGS:
            require(value.get(key) is False, 'no theorem promotion ' + key)
    seal = read(d / 'seal.json')
    require(set(seal) == {'source_seal.json', 'recipes.json', 'protocol.json'}, 'complete frozen calibration seal')
    for name, value in seal.items():
        require(sha(d / name) == value, 'immutable frozen input ' + name)
    source = read(d / 'source_seal.json')
    require(set(source) == set(sources()), 'complete frozen calibration source closure')
    require(sum((ROOT / name).stat().st_size for name in source) <= RESOURCES['max_source_bytes'], 'bounded source bytes')
    require({str(p.relative_to(d / 'frozen_source')) for p in (d / 'frozen_source').rglob('*') if p.is_file()} == set(source), 'complete frozen source tree')
    for name, value in source.items():
        require(sha(ROOT / name) == value == sha(d / 'frozen_source' / name), 'bound original/frozen source ' + name)
    catalogue = read(d / 'recipes.json', RESOURCES['max_recipe_bytes'])
    charge(8*sum((ROOT / name).stat().st_size for name in S.LEDGER.SOURCE_BINDINGS))
    require(catalogue == S.recipes(), 'same reviewed complete symbolic recipes')
    protocol = read(d / 'protocol.json')
    expected = dict(schema='parametric-source-identities-run-v1', mode='calibration of supplied identities; not autonomous discovery',
                    recipes_hash=catalogue['recipes_hash'], recipe_count=74, tests=TESTS, kernel_limits=LIMITS, resources=RESOURCES,
                    scope='universal formal equality for each explicitly bound symbolic recipe',
                    source_adapter_compiler_equivalence_formally_proved=False, finite_samples_used_as_universal_proof=False,
                    ratio_semantics='exact quotient when denominator nonzero; zero otherwise; actual source denominators positive', **FLAGS)
    require(protocol == expected, 'fixed independently specified universal calibration protocol')
    require(read(d / 'run_started.json') == dict(protocol_sha256=sha(d / 'protocol.json')), 'exclusive frozen startup')
    tests = read(d / 'tests.json')
    match = re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$', tests.get('stdout', '') + tests.get('stderr', ''))
    require(tests.get('returncode') == 0 and match is not None, 'completed prescore kernel/source calibration')
    receipt = read(d / 'receipt.json')
    scoped(receipt)
    root_names = {'source_seal.json', 'recipes.json', 'protocol.json', 'seal.json', 'run_started.json', 'tests.json', 'execution.json'}
    expected_files = root_names | {f'jobs/{i:03d}/{name}.json' for i in range(74) for name in ('proof', 'check')}
    actual = {str(p.relative_to(d)) for p in d.rglob('*') if p.is_file() and p.relative_to(d).parts[0] != 'frozen_source'
              and str(p.relative_to(d)) not in ('receipt.json', 'independent_verification.json')}
    require(actual == set(receipt.get('files_sha256', {})) == expected_files, 'complete exact terminal artifact inventory')
    require(receipt.get('source_count') == len(source), 'terminal frozen source count')
    for name, value in receipt['files_sha256'].items():
        require(sha(d / name) == value, 'complete terminal hash ' + name)
    execution = read(d / 'execution.json')
    scoped(execution)
    require(execution.get('schema') == protocol['schema'] and execution.get('completed') is True
            and execution.get('resources') == RESOURCES, 'complete bounded calibration execution')
    cost = execution.get('cost', {})
    require(type(cost.get('elapsed_seconds')) in (int, float) and 0 <= cost['elapsed_seconds'] <= 300
            and cost.get('address_space_limit_bytes') == 2*1024**3, 'observed declared process limits')
    results = []
    for i, recipe in enumerate(catalogue['recipes']):
        certificate = read(d / f'jobs/{i:03d}/proof.json', 65536)
        checked = C.verify_certificate(certificate, deadline=deadline,
                                       **dict(LIMITS, max_operations=min(1000000, max_operations-operations)),
                                       expected_source_bindings=S.LEDGER.SOURCE_BINDINGS,
                                       expected_recipe_ids=[recipe['id']], expected_context=S.proof_context(recipe),
                                       expected_function_bindings={r['name']: r['definition_hash'] for r in recipe['functions']},
                                       expected_lhs_tree=S.proof_tree(recipe['lhs']), expected_rhs_tree=S.proof_tree(recipe['rhs']))
        charge(checked['audit_operations'])
        require(read(d / f'jobs/{i:03d}/check.json', 8192) == checked, 'same independently replayed formal certificate')
        results.append(dict(index=i, recipe_id=recipe['id'], producer_status=certificate['status'],
                            FORMAL_EQ_verified=checked['FORMAL_EQ_verified'],
                            producer_operations=certificate['counts']['operations'], checker_operations=checked['audit_operations']))
    require(execution.get('results') == results and execution.get('formal_identities_verified') == sum(r['FORMAL_EQ_verified'] for r in results), 'complete outcome/count binding')
    for name, value in source.items():
        require(sha(ROOT / name) == value == sha(d / 'frozen_source' / name), 'post-replay immutable source')
    for name, value in receipt['files_sha256'].items():
        require(sha(d / name) == value, 'post-replay artifact integrity')
    input_hashes = {name: sha(d / name) for name in ['source_seal.json', 'recipes.json', 'protocol.json', 'seal.json', 'tests.json', 'execution.json', 'receipt.json']}
    charge(1)
    result = dict(schema='parametric-source-identities-independent-review-v1', all_passed=True,
                  source_count=len(source), tests_passed=int(match.group(1)), recipe_count=74,
                  formal_identities_verified=sum(r['FORMAL_EQ_verified'] for r in results),
                  results=results, audit_operations=operations, elapsed_seconds=time.monotonic()-started,
                  limits=dict(max_operations=max_operations, time_limit=time_limit), input_sha256=input_hashes,
                  formal_source_roots_independently_checked=True,
                  full_source_compiler_equivalence_formally_proved=False,
                  finite_sampling_used_as_universal_proof=False, **FLAGS)
    if write:
        with (d / 'independent_verification.json').open('xb') as stream:
            stream.write(C.encoded(result))
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = audit(args.directory, write=args.write)
    print(json.dumps({k: result[k] for k in ('all_passed', 'recipe_count', 'formal_identities_verified', 'tests_passed', 'audit_operations')}, sort_keys=True))
