"""Freeze, synthesize shared arithmetic templates, and transfer without refitting."""
import argparse
import hashlib
import itertools
import json
import subprocess
import sys
from pathlib import Path

import scipy

import grouped_arithmetic_templates as templates
import grouped_arithmetic_synthesis as synthesis
import check_grouped_arithmetic as independent

ROOT = Path(__file__).resolve().parent
CODE = [
    'grouped_arithmetic_language.py', 'test_grouped_arithmetic_language.py',
    'grouped_arithmetic_proof.txt', 'grouped_arithmetic_synthesis.py',
    'test_grouped_arithmetic_synthesis.py', 'grouped_arithmetic_templates.py',
    'test_grouped_arithmetic_templates.py', 'check_grouped_arithmetic.py',
    'test_check_grouped_arithmetic.py', 'run_grouped_arithmetic.py',
    'test_run_grouped_arithmetic.py', 'check_grouped_arithmetic_run.py',
    'test_check_grouped_arithmetic_run.py', 'arithmetic_cycle_language.py',
    'arithmetic_cycle_synthesis.py', 'check_arithmetic_cycle_certificate.py',
    'arithmetic_cycle_uniform_extension_design.txt', 'critical_defect_proof.txt',
    'signed_arithmetic_proof.txt', 'arithmetic_cycle_synthesis_scope.txt',
]
TESTS = [Path(n).stem for n in CODE if n.startswith('test_')]
LIMITS = dict(max_columns=1024, max_monomials=20000, max_operations=200000000,
              max_coefficient_bits=2048, max_horizon=4096, max_degree=12,
              max_denominator=1000000, time_limit=30)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    with Path(path).open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True)
        f.write('\n')


def programs():
    critical = [dict(target=t, q=q, C=c, claim='critical', allow_constant_slack=True)
                for t, q, c in itertools.product(('mu', 'c'), (2, 6), (8, 32))]
    return critical + [dict(target=t, q=2, C=1, claim='unsigned_calibration',
                            allow_constant_slack=False) for t in ('mu', 'c')]


def freeze(directory):
    directory = Path(directory)
    if directory.exists():
        raise FileExistsError('new run directory required')
    for name in CODE:
        if not (ROOT / name).is_file():
            raise FileNotFoundError(name)
    directory.mkdir(parents=True)
    (directory / 'frozen_source').mkdir()
    hashes = {}
    for name in CODE:
        data = (ROOT / name).read_bytes()
        with (directory / 'frozen_source' / name).open('xb') as f:
            f.write(data)
        hashes[name] = hashlib.sha256(data).hexdigest()
    protocol = dict(
        schema=1, programs=programs(), training_scales=[1, 2, 4, 5],
        final_fixed_scale=8, final_odd_choices=[9, 11], limits=LIMITS,
        dictionary=templates.descriptors(), tests=TESTS,
        selection='all ten declared programs retained, including failures',
        training='one shared square/relation weight vector across all training scales',
        final='same weight vector, no refit; exact complete polynomial matching',
        scalar_residual='Critical programs permit only an exactly computed nonnegative constant residual after all nonconstant coefficients cancel. No per-index structural weights are fitted at evaluation.',
        prime_provenance='factor witnesses specify actual arithmetic; no signed response table enters synthesis',
        historical_coefficient_overlap=True, unseen_prime_holdout=False,
        runtime=dict(python=sys.version, scipy=scipy.__version__),
        solver_byte_replay_guaranteed=False,
        prior_verification=dict(path='arithmetic-cycle-results/pilot-001/independent_verification.json',
                                sha256=sha(ROOT / 'arithmetic-cycle-results/pilot-001/independent_verification.json')),
        global_critical_bound_proved=False, RH_proved=False,
    )
    write(directory / 'protocol.json', protocol)
    write(directory / 'source_seal.json', dict(hashes=hashes))
    write(directory / 'seal.json', dict(protocol_sha256=sha(directory / 'protocol.json'),
                                      source_seal_sha256=sha(directory / 'source_seal.json')))


def validate_sources(directory):
    source = read(directory / 'source_seal.json')
    seal = read(directory / 'seal.json')
    if seal != dict(protocol_sha256=sha(directory / 'protocol.json'),
                    source_seal_sha256=sha(directory / 'source_seal.json')):
        raise ValueError('protocol/source seal changed')
    if set(source['hashes']) != set(CODE):
        raise ValueError('frozen source coverage')
    for name, value in source['hashes'].items():
        if sha(ROOT / name) != value or sha(directory / 'frozen_source' / name) != value:
            raise ValueError('source changed: ' + name)


def build(program, X):
    return templates.build_instance(X=X, **{k: v for k, v in program.items() if k != 'allow_constant_slack'})


def train(program, scales, limits):
    built = [build(program, X) for X in scales]
    if any((b['square_ids'], b['relation_ids']) != (built[0]['square_ids'], built[0]['relation_ids']) for b in built):
        raise ValueError('shared descriptor ordering changed')
    instances = [b['instance'] for b in built]
    result = synthesis.synthesize(instances, allow_constant_slack=program['allow_constant_slack'], **limits)
    check = independent.verify_joint_result(instances, result, allow_constant_slack=program['allow_constant_slack'])
    dual = None
    dual_check = None
    if result['status'] == 'no_certificate_found':
        dual = synthesis.find_separator(instances, allow_constant_slack=program['allow_constant_slack'], **limits)
        if dual.get('certified') is True:
            dual_check = independent.verify_joint_dual(instances, dual, allow_constant_slack=program['allow_constant_slack'])
    return dict(program=program, instances=built, synthesis=result, independent_check=check,
                dual=dual, independent_dual_check=dual_check,
                global_critical_bound_proved=False, RH_proved=False)


def transfer(training, scales, limits):
    program = training['program']
    result = training['synthesis']
    if result['status'] != 'finite_certificate':
        return dict(program=program, status='no_candidate', observations=[], refitted=False)
    observations = []
    for X in scales:
        built = build(program, X)
        try:
            cert = synthesis.instantiate_certificate(built['instance'], result['weights'],
                                                       allow_constant_slack=program['allow_constant_slack'], **limits)
            check = independent.verify_joint([built['instance']], **result['weights'],
                                              allow_constant_slack=program['allow_constant_slack'])
            independent.verify_certificate(cert)
            observations.append(dict(X=X, instance=built, status='finite_certificate', certificate=cert,
                                     independent_check=check))
        except (OverflowError, TimeoutError, MemoryError) as exc:
            observations.append(dict(X=X, instance=built, status='missing_resource', reason=str(exc)))
        except ValueError as exc:
            observations.append(dict(X=X, instance=built, status='template_mismatch', reason=str(exc)))
    return dict(program=program, status='evaluated', observations=observations,
                weights_sha256=digest(result['weights']), refitted=False)


def run(directory):
    directory = Path(directory)
    if (directory / 'training.json').exists():
        raise FileExistsError('training archive exists')
    validate_sources(directory)
    protocol = read(directory / 'protocol.json')
    testing = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=ROOT,
                             capture_output=True, text=True, timeout=120)
    if testing.returncode:
        raise ValueError('frozen tests failed: ' + testing.stdout + testing.stderr)
    write(directory / 'tests.json', dict(returncode=testing.returncode, stdout=testing.stdout,
                                       stderr=testing.stderr))
    attempts = []
    for program in protocol['programs']:
        attempt = train(program, protocol['training_scales'], protocol['limits'])
        attempts.append(attempt)
        print(json.dumps(dict(program=program, status=attempt['synthesis']['status'],
                              exact_separator=bool(attempt['dual'] and attempt['dual'].get('certified')))), flush=True)
    write(directory / 'training.json', dict(attempts=attempts, shared_weights=True, no_actual_signed_responses=True))
    selection_hash = digest(dict(programs=protocol['programs'], dictionary=protocol['dictionary'],
                                 training_scales=protocol['training_scales']))
    write(directory / 'candidate_seal.json', dict(training_sha256=sha(directory / 'training.json'),
                                                 protocol_sha256=sha(directory / 'protocol.json'),
                                                 selection_sha256=selection_hash))
    odd = protocol['final_odd_choices'][int(selection_hash, 16) % 2]
    scales = [protocol['final_fixed_scale'], odd]
    write(directory / 'final_cases.json', dict(scales=scales,
                                              candidate_seal_sha256=sha(directory / 'candidate_seal.json'),
                                              no_refitting=True))
    final = [transfer(a, scales, protocol['limits']) for a in attempts]
    write(directory / 'final.json', dict(results=final, no_refitting=True,
                                         global_critical_bound_proved=False, RH_proved=False))
    validate_sources(directory)
    write(directory / 'producer_receipt.json', dict(
        training_sha256=sha(directory / 'training.json'), final_sha256=sha(directory / 'final.json'),
        tests_sha256=sha(directory / 'tests.json'), source_seal_sha256=sha(directory / 'source_seal.json'),
        all_programs_retained=len(attempts), global_critical_bound_proved=False, RH_proved=False))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('command', choices=['freeze', 'run'])
    parser.add_argument('directory')
    args = parser.parse_args()
    (freeze if args.command == 'freeze' else run)(args.directory)
