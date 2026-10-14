"""Frozen full shared Gram extension, with exact admission and retained failures."""
import argparse
import json
import subprocess
import sys
from pathlib import Path

import cvxpy
import clarabel
import scipy
import run_cancellation_arithmetic as R
import cancellation_gram_synthesis as S
import cancellation_gram_diagonal_dual as D
import cancellation_budget as B
import cancellation_cubic_gate as gate
import check_cancellation_gram as I

EXTRA = [
    'run_cancellation_gram_probe.py', 'check_cancellation_gram_run.py',
    'cancellation_gram_synthesis.py', 'test_cancellation_gram_synthesis.py',
    'cancellation_gram_language.py', 'test_cancellation_gram_language.py',
    'cancellation_gram_diagonal_dual.py', 'test_cancellation_gram_diagonal_dual.py',
    'check_cancellation_gram.py', 'test_check_cancellation_gram.py',
    'test_check_cancellation_gram_run.py', 'test_run_cancellation_gram_probe.py',
    'cancellation_gram_independent_review.txt',
    'exact_dual_support_reconstruction.py', 'cancellation_dual_column_search.py',
]
TESTS = ['test_cancellation_gram_language', 'test_cancellation_gram_synthesis',
         'test_cancellation_gram_diagonal_dual', 'test_check_cancellation_gram',
         'test_check_cancellation_gram_run', 'test_run_cancellation_gram_probe']
LIMITS = dict(R.LIMITS, time_limit=120, max_coefficient_bits=4096, max_horizon=80)
DUAL_LIMITS = dict(time_limit=60, max_denominator=2**4096, max_rows=1200,
                   max_variables=40000, max_work=30000000, max_horizon=80)
FLAGS = dict(global_bound_proved=False, RH_proved=False)


def write(path, obj):
    # Reject nonfinite JSON instead of silently publishing NaN/Infinity.
    data = json.dumps(obj, sort_keys=True, indent=2, allow_nan=False) + '\n'
    with Path(path).open('x') as f:
        f.write(data)


def freeze(parent):
    parent = Path(parent)
    R.validate_sources(parent)
    if not R.read(parent/'independent_verification.json')['all_passed']:
        raise ValueError('verified parent required')
    out = parent/'gram-probe-001'
    if out.exists():
        raise FileExistsError('new Gram run required')
    programs = [dict(R.read(parent/'training.json')['attempts'][i]['program']) for i in [26, 28]]
    for program in programs:
        program['allow_constant_slack'] = True
    for name in EXTRA:
        if not (R.ROOT/name).is_file():
            raise FileNotFoundError(name)
    out.mkdir()
    (out/'frozen_source').mkdir()
    hashes = {}
    for name in EXTRA:
        (out/'frozen_source'/name).write_bytes((R.ROOT/name).read_bytes())
        hashes[name] = R.sha(R.ROOT/name)
    protocol = dict(schema=1, programs=programs, training_scales=[1, 2, 3, 5],
        final_scales=[11, 13], limits=LIMITS, dual_limits=DUAL_LIMITS,
        tests=TESTS, atoms=list(S.ATOMS), regions=list(S.REGIONS),
        parent_training_sha256=R.sha(parent/'training.json'),
        parent_verification_sha256=R.sha(parent/'independent_verification.json'),
        parent_source_seal_sha256=R.sha(parent/'source_seal.json'),
        objective='structural scalar L1 plus shared Gram traces, scalar slack cost zero',
        conditioning='posthoc language response to prior cone obstruction; no independent discovery claim',
        representation='two common 5 by 5 rational PSD matrices, fixed across all ordinary scales; auxiliary Gram blocks empty',
        dual_rule='if critical primal is not accepted, one sufficient dual search forces all 20 Gram offdiagonal moments zero',
        arithmetic_provenance='actual factor and prime predicates; supplied arithmetic relations; no signed response table in learner',
        final='fixed learned scalar weights and both matrices, no refit; complete original target',
        calibration='extended supplied unsigned bound, constant slack allowed explicitly',
        historical_coefficient_overlap=True, unseen_prime_holdout=False,
        runtime=dict(python=sys.version, scipy=scipy.__version__, cvxpy=cvxpy.__version__, clarabel=clarabel.__version__),
        solver_byte_replay_guaranteed=False, **FLAGS)
    write(out/'protocol.json', protocol)
    write(out/'source_seal.json', dict(hashes=hashes))
    write(out/'seal.json', dict(protocol_sha256=R.sha(out/'protocol.json'), source_seal_sha256=R.sha(out/'source_seal.json')))


def validate(parent):
    parent = Path(parent)
    R.validate_sources(parent)
    out = parent/'gram-probe-001'
    expected = dict(protocol_sha256=R.sha(out/'protocol.json'), source_seal_sha256=R.sha(out/'source_seal.json'))
    if R.read(out/'seal.json') != expected:
        raise ValueError('Gram seal changed')
    hashes = R.read(out/'source_seal.json')['hashes']
    if set(hashes) != set(EXTRA):
        raise ValueError('Gram source coverage')
    for name, h in hashes.items():
        if R.sha(R.ROOT/name) != h or R.sha(out/'frozen_source'/name) != h:
            raise ValueError('Gram source changed: '+name)
    protocol = R.read(out/'protocol.json')
    for name in ['training', 'verification', 'source_seal']:
        path = parent/('independent_verification.json' if name == 'verification' else name+'.json')
        if protocol['parent_'+name+'_sha256'] != R.sha(path):
            raise ValueError('Gram parent input changed')
    return protocol


def train(program, scales, limits):
    row = dict(program=program, case_hashes=[], gamma=None, budgets=[], independent_check=None, **FLAGS)
    try:
        ordinary = [R.build(program, X)['instance'] for X in scales]
        instances = ordinary + R.constraints(program)
        row['case_hashes'] = list(map(R.digest, instances))
        result = S.synthesize(instances, scales, **limits)
        row['synthesis'] = result
        if result['status'] == 'finite_PSD_certificate':
            row['independent_check'] = I.verify_primal(instances, scales, result)
            row['gamma'] = str(gate.gamma(result['weights'], R.dictionary(program)))
            row['budgets'] = [B.extract(inst, result['weights']) for inst in ordinary]
        return row
    except (OverflowError, TimeoutError, MemoryError) as e:
        row.update(synthesis=dict(status='missing_resource', reason=str(e) or type(e).__name__, **FLAGS),
                   gamma=None, budgets=[], independent_check=None, external_resource_failure=True)
        return row


def transfer(attempt, scales, limits):
    result, program = attempt['synthesis'], attempt['program']
    accepted = result['status'] == 'finite_PSD_certificate'
    final = dict(status='evaluated' if accepted else 'no_candidate', observations=[], refitted=False, **FLAGS)
    if not accepted:
        return final
    final['weights_sha256'] = R.digest(result['weights'])
    final['grams_sha256'] = R.digest(result['grams'])
    for X in scales:
        row = dict(X=X, case_sha256=None, scalar_budget=None)
        try:
            instance = R.build(program, X)['instance']
            row.update(case_sha256=R.digest(instance), scalar_budget=B.extract(instance, result['weights']))
            # The independent atom constructor also avoids preparing an unused full SDP at final scales.
            cert = S.instantiate_certificate(instance, result['weights'], result['grams'], I.atom_blocks(X), **limits)
            wrapper = dict(status='finite_PSD_certificate', weights=result['weights'], grams=result['grams'],
                           certificates=[cert], constant_slacks=[row['scalar_budget']['scalar_slack']])
            checked = I.verify_primal([instance], [X], wrapper)
            row.update(status='finite_PSD_certificate', certificate=cert, independent_check=checked)
        except (OverflowError, TimeoutError, MemoryError) as e:
            row.update(status='missing_resource', reason=str(e) or type(e).__name__)
        except ValueError as e:
            row.update(status='template_mismatch', reason=str(e))
        final['observations'].append(row)
        print(json.dumps(dict(final_X=X, status=row['status'])), flush=True)
    return final


def run(parent):
    parent = Path(parent)
    out = parent/'gram-probe-001'
    protocol = validate(parent)
    if (out/'tests.json').exists():
        raise FileExistsError('Gram run already started')
    tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=R.ROOT,
                           capture_output=True, text=True, timeout=120)
    write(out/'tests.json', dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr))
    if tests.returncode:
        raise ValueError('Gram tests failed')
    (out/'attempts').mkdir()
    attempts = []
    for index, program in enumerate(protocol['programs']):
        attempt = train(program, protocol['training_scales'], protocol['limits'])
        write(out/'attempts'/f'{index:03d}.json', attempt)
        attempts.append(attempt)
        print(json.dumps(dict(index=index, claim=program['claim'], status=attempt['synthesis']['status'], gamma=attempt['gamma'])), flush=True)
    write(out/'training.json', dict(attempts=attempts, no_actual_signed_responses=True, **FLAGS))
    write(out/'candidate_seal.json', dict(training_sha256=R.sha(out/'training.json'), protocol_sha256=R.sha(out/'protocol.json')))
    final = [transfer(attempt, protocol['final_scales'], protocol['limits']) for attempt in attempts]
    write(out/'final.json', dict(results=final, refitted=False, **FLAGS))
    if attempts[0]['synthesis']['status'] == 'finite_PSD_certificate':
        dual = dict(status='not_requested', certified=False, **FLAGS)
        dual_check = None
    else:
        program = protocol['programs'][0]
        try:
            instances = [R.build(program, X)['instance'] for X in protocol['training_scales']] + R.constraints(program)
            dual = D.propose(instances, protocol['training_scales'], allow_constant_slack=True, **protocol['dual_limits'])
            dual_check = I.verify_dual(instances, protocol['training_scales'], dual) if dual.get('certified') else None
        except (OverflowError, TimeoutError, MemoryError) as e:
            dual = dict(status='missing_resource', certified=False, reason=str(e) or type(e).__name__, **FLAGS)
            dual_check = None
    write(out/'dual.json', dict(trigger='critical primal not accepted', result=dual, independent_check=dual_check, **FLAGS))
    print(json.dumps(dict(dual_status=dual['status'], dual_certified=dual.get('certified', False))), flush=True)
    validate(parent)
    write(out/'producer_receipt.json', dict(**{name+'_sha256':R.sha(out/(name+'.json')) for name in
        ['training', 'final', 'dual', 'tests', 'candidate_seal', 'source_seal']}, original_results_unchanged=True, **FLAGS))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('command', choices=['freeze', 'run'])
    parser.add_argument('parent')
    args = parser.parse_args()
    (freeze if args.command == 'freeze' else run)(args.parent)
