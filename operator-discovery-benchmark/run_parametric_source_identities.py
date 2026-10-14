"""Freeze and run a bounded universal-identity calibration on actual source recipes."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

import parametric_arithmetic_identity as P
import check_parametric_arithmetic_identity as C
import primitive_state_parametric_sources as S

ROOT = Path(__file__).resolve().parent
SCHEMA = 'parametric-source-identities-run-v1'
TESTS = ['test_parametric_arithmetic_identity', 'test_check_parametric_arithmetic_identity',
         'test_parametric_identity_soundness', 'test_primitive_state_parametric_sources',
         'test_run_parametric_source_identities', 'test_check_parametric_source_identities_run']
LIMITS = dict(P.LIMITS, max_operations=1000000, max_receipt_bytes=65536)
FLAGS = dict(S.FLAGS)
RESOURCES = dict(memory_bytes=2*1024**3, cooperative_seconds=300, max_work=450000000,
                 producer_reserve=74000000, worker_checker_reserve=74000000,
                 whole_audit_reserve=100000000, binding_io_reserve=100000000, test_reserve=25000000,
                 total_work_reserve=373000000, max_source_bytes=2097152,
                 max_recipe_bytes=4194304, max_metadata_bytes=65536, max_check_bytes=8192)
SELF = 'run_parametric_source_identities.py'
AUDITOR = 'check_parametric_source_identities_run.py'


def require(test, message):
    if not test:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for part in iter(lambda: stream.read(1048576), b''):
            h.update(part)
    return h.hexdigest()


def read(path, cap=65536):
    path = Path(path)
    require(path.stat().st_size <= cap, 'bounded archive read')
    return json.loads(path.read_bytes())


def write(path, value, cap=65536):
    raw = P.encoded(value)
    require(len(raw) <= cap, 'bounded exclusive artifact')
    with Path(path).open('xb') as stream:
        stream.write(raw)


def sources():
    pending = [SELF[:-3], AUDITOR[:-3], *TESTS]
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
    return sorted(name + '.py' for name in seen)


def protocol(catalogue):
    require(catalogue['recipe_count'] == 74, 'fixed calibration recipe inventory')
    return dict(schema=SCHEMA, mode='calibration of supplied identities; not autonomous discovery',
                recipes_hash=catalogue['recipes_hash'], recipe_count=74, tests=TESTS,
                kernel_limits=LIMITS, resources=RESOURCES,
                scope='universal formal equality for each explicitly bound symbolic recipe',
                source_adapter_compiler_equivalence_formally_proved=False,
                finite_samples_used_as_universal_proof=False,
                ratio_semantics='exact quotient when denominator nonzero; zero otherwise; actual source denominators positive',
                **FLAGS)


def freeze(directory):
    require(not sys.flags.optimize, 'assertions enabled for calibration')
    for name in [SELF, AUDITOR, *[n + '.py' for n in TESTS]]:
        require((ROOT / name).is_file(), 'complete calibration implementation ' + name)
    catalogue = S.recipes()
    names = sources()
    require(sum((ROOT / name).stat().st_size for name in names) <= RESOURCES['max_source_bytes'], 'source byte preflight')
    d = Path(directory).resolve()
    d.mkdir(exist_ok=False)
    (d / 'frozen_source').mkdir()
    (d / 'jobs').mkdir()
    for name in names:
        (d / 'frozen_source' / name).write_bytes((ROOT / name).read_bytes())
    write(d / 'source_seal.json', {name: sha(ROOT / name) for name in names})
    write(d / 'recipes.json', catalogue, RESOURCES['max_recipe_bytes'])
    write(d / 'protocol.json', protocol(catalogue))
    write(d / 'seal.json', {name: sha(d / name) for name in ('source_seal.json', 'recipes.json', 'protocol.json')})


def validate(directory):
    d = Path(directory)
    seal = read(d / 'seal.json')
    require(set(seal) == {'source_seal.json', 'recipes.json', 'protocol.json'}, 'complete preregistration seal')
    for name, value in seal.items():
        require(sha(d / name) == value, 'immutable preregistration ' + name)
    source = read(d / 'source_seal.json')
    require(set(source) == set(sources()), 'complete source closure')
    require({str(p.relative_to(d / 'frozen_source')) for p in (d / 'frozen_source').rglob('*') if p.is_file()} == set(source), 'complete frozen source inventory')
    for name, value in source.items():
        require(sha(ROOT / name) == value == sha(d / 'frozen_source' / name), 'immutable source ' + name)
    catalogue = read(d / 'recipes.json', RESOURCES['max_recipe_bytes'])
    require(catalogue == S.recipes(), 'same reviewed actual source recipes')
    require(read(d / 'protocol.json') == protocol(catalogue), 'same fixed protocol')
    return catalogue


def check_certificate(recipe, certificate, deadline):
    return C.verify_certificate(certificate, deadline=deadline, **LIMITS,
                                expected_source_bindings=S.LEDGER.SOURCE_BINDINGS,
                                expected_recipe_ids=[recipe['id']], expected_context=S.proof_context(recipe),
                                expected_function_bindings={r['name']: r['definition_hash'] for r in recipe['functions']},
                                expected_lhs_tree=S.proof_tree(recipe['lhs']), expected_rhs_tree=S.proof_tree(recipe['rhs']))


def run(directory):
    require(not sys.flags.optimize, 'assertions enabled for calibration')
    d = Path(directory).resolve()
    catalogue = validate(d)
    write(d / 'run_started.json', dict(protocol_sha256=sha(d / 'protocol.json')))
    memory = RESOURCES['memory_bytes']
    resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
    started, cpu = time.monotonic(), time.process_time()
    deadline = started + RESOURCES['cooperative_seconds']
    tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=ROOT,
                           capture_output=True, text=True, timeout=60)
    write(d / 'tests.json', dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr))
    require(tests.returncode == 0, 'prescore calibration tests passed')
    results = []
    for index, recipe in enumerate(catalogue['recipes']):
        require(time.monotonic() <= deadline, 'whole calibration deadline')
        folder = d / 'jobs' / f'{index:03d}'
        folder.mkdir()
        certificate = S.produce_certificate(recipe, limits=LIMITS, deadline=deadline)
        write(folder / 'proof.json', certificate, LIMITS['max_receipt_bytes'])
        checked = check_certificate(recipe, certificate, deadline)
        write(folder / 'check.json', checked, RESOURCES['max_check_bytes'])
        results.append(dict(index=index, recipe_id=recipe['id'], producer_status=certificate['status'],
                            FORMAL_EQ_verified=checked['FORMAL_EQ_verified'],
                            producer_operations=certificate['counts']['operations'], checker_operations=checked['audit_operations']))
    validate(d)
    require(time.monotonic() <= deadline, 'final calibration deadline')
    record = dict(schema=SCHEMA, completed=True, results=results, resources=RESOURCES,
                  formal_identities_verified=sum(r['FORMAL_EQ_verified'] for r in results),
                  cost=dict(elapsed_seconds=time.monotonic()-started, cpu_seconds=time.process_time()-cpu,
                            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                            address_space_limit_bytes=resource.getrlimit(resource.RLIMIT_AS)[0]), **FLAGS)
    write(d / 'execution.json', record)
    inventory = {str(p.relative_to(d)): sha(p) for p in sorted(d.rglob('*'))
                 if p.is_file() and p.relative_to(d).parts[0] != 'frozen_source'}
    write(d / 'receipt.json', dict(files_sha256=inventory, source_count=len(sources()), **FLAGS))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['freeze', 'run'])
    parser.add_argument('directory')
    args = parser.parse_args()
    (freeze if args.action == 'freeze' else run)(args.directory)
