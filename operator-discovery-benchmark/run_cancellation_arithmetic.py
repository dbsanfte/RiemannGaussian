"""Frozen balanced AST search, baseline ablation and necessary cubic filter."""
import argparse
import itertools
import json
import subprocess
import sys
from pathlib import Path

import scipy
import grouped_arithmetic_templates as baseline
import grouped_arithmetic_synthesis as structural
import cancellation_arithmetic_templates as extended
import cancellation_arithmetic_synthesis as synthesis
import cancellation_cubic_gate as gate
import cancellation_budget as budget
import check_grouped_arithmetic as independent
from run_grouped_arithmetic import digest, sha, read, write

ROOT = Path(__file__).resolve().parent
CODE = [
    'run_cancellation_arithmetic.py', 'test_run_cancellation_arithmetic.py',
    'cancellation_arithmetic_templates.py', 'test_cancellation_arithmetic_templates.py',
    'cancellation_arithmetic_language.py', 'cancellation_arithmetic_synthesis.py',
    'test_cancellation_arithmetic_synthesis.py', 'cancellation_cubic_gate.py',
    'test_cancellation_cubic_gate.py', 'cancellation_budget.py', 'test_cancellation_budget.py',
    'cancellation_search_analytic_scope.txt', 'cancellation_cubic_gate_independent_review.txt',
    'check_cancellation_arithmetic_run.py', 'test_check_cancellation_arithmetic_run.py',
    'grouped_arithmetic_templates.py', 'grouped_arithmetic_language.py',
    'grouped_arithmetic_synthesis.py', 'check_grouped_arithmetic.py',
    'run_grouped_arithmetic.py', 'check_grouped_arithmetic_run.py',
    'arithmetic_cycle_language.py', 'arithmetic_cycle_synthesis.py',
    'check_arithmetic_cycle_certificate.py', 'grouped_arithmetic_mu_cubic_budget_review.txt',
    'grouped_arithmetic_proof.txt', 'critical_defect_proof.txt',
]
TESTS = [Path(n).stem for n in CODE if n.startswith('test_')]
LIMITS = dict(max_columns=1024, max_monomials=30000, max_operations=200000000,
              max_coefficient_bits=2048, max_horizon=4096, max_degree=12,
              max_denominator=1000000, time_limit=30)


def programs():
    critical = [dict(target='mu', q=q, C=C, claim='critical', allow_constant_slack=True,
                     dictionary_mode=mode, constraint=constraint)
                for (mode, constraint), q, C in itertools.product(
                    (('baseline', 'none'), ('extended', 'none'), ('extended', 'zero_cubic')),
                    (2, 3, 6), (2, 8, 32))]
    return critical + [dict(target='mu', q=2, C=1, claim='unsigned_calibration',
                            allow_constant_slack=False, dictionary_mode=mode, constraint='none')
                       for mode in ('baseline', 'extended')]


def dictionary(program):
    return (baseline if program['dictionary_mode'] == 'baseline' else extended).descriptors()


def build(program, X):
    module = baseline if program['dictionary_mode'] == 'baseline' else extended
    b = module.build_instance(program['target'], X, program['q'], program['C'], program['claim'])
    budget.audit_added_zero_scalars(b['instance'])
    return b


def constraints(program):
    if program['constraint'] == 'none': return []
    if program['constraint'] != 'zero_cubic' or program['target'] != 'mu' or program['q'] <= 1:
        raise ValueError('cubic constraint domain')
    return [gate.build_constraint(dictionary(program))['instance']]


def freeze(directory):
    directory = Path(directory)
    if directory.exists(): raise FileExistsError('new run directory required')
    for name in CODE:
        if not (ROOT/name).is_file(): raise FileNotFoundError(name)
    directory.mkdir(parents=True)
    (directory/'frozen_source').mkdir()
    hashes = {}
    for name in CODE:
        data = (ROOT/name).read_bytes()
        (directory/'frozen_source'/name).write_bytes(data)
        hashes[name] = sha(ROOT/name)
    protocol = dict(schema=1, programs=programs(), training_scales=[1, 2, 3, 5],
        final_fixed_scale=7, final_odd_choices=[9, 11], limits=LIMITS, dual_time_limit=10,
        dictionaries=dict(baseline=baseline.descriptors(), extended=extended.descriptors()), tests=TESTS,
        selection='all 29 programs retained; paired baseline/extension comparisons plus necessary-gate ablation',
        objective='structural L1; scalar slack has zero cost; not scalar-budget optimality',
        constraints='zero_cubic auxiliary row encodes exact shared-weight gamma=0, not an arithmetic observation',
        final='same structural weights, no refit, complete original target',
        arithmetic_provenance='actual prime/factor predicates and supplied arithmetic identities; no signed coefficient response table in learner',
        historical_coefficient_overlap=True, unseen_prime_holdout=False,
        runtime=dict(python=sys.version, scipy=scipy.__version__), solver_byte_replay_guaranteed=False,
        global_critical_bound_proved=False, RH_proved=False)
    write(directory/'protocol.json', protocol)
    write(directory/'source_seal.json', dict(hashes=hashes))
    write(directory/'seal.json', dict(protocol_sha256=sha(directory/'protocol.json'),
                                     source_seal_sha256=sha(directory/'source_seal.json')))


def validate_sources(directory):
    directory = Path(directory)
    if read(directory/'seal.json') != dict(protocol_sha256=sha(directory/'protocol.json'),
                                         source_seal_sha256=sha(directory/'source_seal.json')):
        raise ValueError('seal changed')
    hashes = read(directory/'source_seal.json')['hashes']
    if set(hashes) != set(CODE): raise ValueError('source coverage')
    for name, h in hashes.items():
        if sha(ROOT/name) != h or sha(directory/'frozen_source'/name) != h:
            raise ValueError('source changed: '+name)


def _train(program, scales, limits, dual_time_limit=10):
    built = [build(program, X) for X in scales]
    ds = dictionary(program)
    if any(b['square_ids'] != [d['id'] for d in ds['square']] or
           b['relation_ids'] != [d['id'] for d in ds['relation']] for b in built):
        raise ValueError('shared dictionary order')
    ordinary = [b['instance'] for b in built]
    auxiliary = constraints(program)
    instances = ordinary + auxiliary
    flag = program['allow_constant_slack']
    result = synthesis.synthesize(instances, allow_constant_slack=flag, **limits)
    checked = independent.verify_joint_result(instances, result, allow_constant_slack=flag)
    dual = dual_check = None
    if result['status'] == 'no_certificate_found':
        dual_limits = dict(limits, time_limit=dual_time_limit)
        dual = structural.find_separator(instances, allow_constant_slack=flag, **dual_limits)
        if dual.get('certified'):
            dual_check = independent.verify_joint_dual(instances, dual, allow_constant_slack=flag)
    accepted = result['status'] == 'finite_certificate'
    return dict(program=program, case_hashes=[digest(i) for i in ordinary],
                ast_hashes=[digest(b.get('ast_archive', [])) for b in built],
                auxiliary_hashes=[digest(i) for i in auxiliary],
                added_scalar_audits=[budget.audit_added_zero_scalars(i) for i in ordinary],
                synthesis=result, independent_check=checked, dual=dual, independent_dual_check=dual_check,
                budgets=[budget.extract(i, result['weights']) for i in ordinary] if accepted else [],
                gamma=str(gate.gamma(result['weights'], ds)) if accepted else None,
                global_critical_bound_proved=False, RH_proved=False)


def train(program, scales, limits, dual_time_limit=10):
    try:
        return _train(program, scales, limits, dual_time_limit)
    except (OverflowError, TimeoutError, MemoryError) as e:
        return dict(program=program, requested_scales=list(scales), external_resource_failure=True,
                    case_hashes=[], ast_hashes=[], auxiliary_hashes=[], added_scalar_audits=[],
                    synthesis=dict(status='missing_resource', reason=str(e) or type(e).__name__,
                                   scope='joint preparation or verification failed; no certificate admitted',
                                   global_bound_proved=False, RH_proved=False),
                    independent_check=None, dual=None, independent_dual_check=None,
                    budgets=[], gamma=None, global_critical_bound_proved=False, RH_proved=False)


def transfer(training, scales, limits):
    program, result = training['program'], training['synthesis']
    if result['status'] != 'finite_certificate':
        return dict(program=program, status='no_candidate', observations=[], refitted=False)
    out = []
    for X in scales:
        row = dict(X=X, case_sha256=None, ast_sha256=None, scalar_budget=None, added_scalar_audit=None)
        try:
            b = build(program, X)
            row.update(case_sha256=digest(b['instance']), ast_sha256=digest(b.get('ast_archive', [])),
                       scalar_budget=budget.extract(b['instance'], result['weights']),
                       added_scalar_audit=budget.audit_added_zero_scalars(b['instance']))
        except (OverflowError, TimeoutError, MemoryError) as e:
            row.update(status='missing_resource', reason=str(e) or type(e).__name__, external_resource_failure=True)
            out.append(row)
            continue
        try:
            cert = structural.instantiate_certificate(b['instance'], result['weights'],
                    allow_constant_slack=program['allow_constant_slack'], **limits)
            check = independent.verify_joint([b['instance']], **result['weights'],
                    allow_constant_slack=program['allow_constant_slack'])
            independent.verify_certificate(cert)
            row.update(status='finite_certificate', certificate=cert, independent_check=check)
        except (OverflowError, TimeoutError, MemoryError) as e:
            row.update(status='missing_resource', reason=str(e) or type(e).__name__)
        except ValueError as e:
            row.update(status='template_mismatch', reason=str(e))
        out.append(row)
    return dict(program=program, status='evaluated', observations=out,
                weights_sha256=digest(result['weights']), refitted=False)


def run(directory):
    directory = Path(directory)
    if (directory/'attempts').exists(): raise FileExistsError('run already started; inspect saved attempts')
    validate_sources(directory)
    protocol = read(directory/'protocol.json')
    testing = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=ROOT,
                             capture_output=True, text=True, timeout=120)
    write(directory/'tests.json', dict(returncode=testing.returncode, stdout=testing.stdout, stderr=testing.stderr))
    if testing.returncode: raise ValueError('frozen tests failed: '+testing.stdout+testing.stderr)
    (directory/'attempts').mkdir()
    attempts = []
    for index, program in enumerate(protocol['programs']):
        result = train(program, protocol['training_scales'], protocol['limits'], protocol['dual_time_limit'])
        write(directory/'attempts'/f'{index:03d}.json', result)
        attempts.append(result)
        print(json.dumps(dict(index=index, program=program, status=result['synthesis']['status'],
                              gamma=result['gamma'], separator=bool(result['dual'] and result['dual'].get('certified')))), flush=True)
    write(directory/'training.json', dict(attempts=attempts, no_actual_signed_responses=True))
    selection = digest(dict(programs=protocol['programs'], dictionaries=protocol['dictionaries'],
                            training_scales=protocol['training_scales']))
    write(directory/'candidate_seal.json', dict(training_sha256=sha(directory/'training.json'),
        protocol_sha256=sha(directory/'protocol.json'), selection_sha256=selection))
    scales = [protocol['final_fixed_scale'], protocol['final_odd_choices'][int(selection, 16)%2]]
    write(directory/'final_cases.json', dict(scales=scales, candidate_seal_sha256=sha(directory/'candidate_seal.json'), no_refitting=True))
    final = []
    for index, attempt in enumerate(attempts):
        result = transfer(attempt, scales, protocol['limits'])
        final.append(result)
        print(json.dumps(dict(final_index=index, outcomes=[r['status'] for r in result['observations']])), flush=True)
    write(directory/'final.json', dict(results=final, no_refitting=True, global_critical_bound_proved=False, RH_proved=False))
    validate_sources(directory)
    write(directory/'producer_receipt.json', dict(all_programs_retained=len(attempts),
        **{name+'_sha256': sha(directory/(name+'.json')) for name in ('training', 'final', 'tests', 'source_seal')},
        global_critical_bound_proved=False, RH_proved=False))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('command', choices=('freeze', 'run'))
    parser.add_argument('directory')
    args = parser.parse_args()
    (freeze if args.command == 'freeze' else run)(args.directory)
