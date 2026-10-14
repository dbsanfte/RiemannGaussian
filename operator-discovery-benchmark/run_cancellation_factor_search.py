"""Frozen factor/coprime closure search for the complete signed energy defect."""
import argparse
import json
import subprocess
import sys
from pathlib import Path
import run_cancellation_arithmetic as R
import run_cancellation_gram_probe as PREVIOUS
import run_cancellation_factor_calibration as CALIBRATION
import cancellation_factor_search_language as F
import cancellation_gram_synthesis as S
import cancellation_gram_diagonal_dual as D
import cancellation_cubic_gate as gate
import cancellation_budget as budget
import check_cancellation_gram as I

NEW = ['run_cancellation_factor_search.py', 'test_run_cancellation_factor_search.py',
       'cancellation_factor_search_language.py', 'test_cancellation_factor_search_language.py',
       'check_cancellation_factor_search.py', 'test_check_cancellation_factor_search.py',
       'check_cancellation_factor_search_run.py', 'cancellation_factor_closure_scope.txt',
       'cancellation_factor_search_prefreeze_review.txt']
SOURCES = sorted(set(R.CODE + PREVIOUS.EXTRA + CALIBRATION.OWN + NEW))
TESTS = ['test_cancellation_factor_search_language', 'test_check_cancellation_factor_search',
         'test_run_cancellation_factor_search']
LIMITS = dict(PREVIOUS.LIMITS, time_limit=180)
DUAL_LIMITS = dict(PREVIOUS.DUAL_LIMITS, time_limit=120, max_rows=1400,
                   max_variables=60000, max_work=200000000)
FLAGS = dict(global_bound_proved=False, RH_proved=False)
write = PREVIOUS.write


def inputs(parent):
    return dict(parent_gram_verification=parent/'gram-probe-001/independent_verification.json',
                parent_gram_uniform=parent/'gram-probe-001/uniform_scope_independent_review.json',
                factor_calibration=parent.parent/'factor-calibration-001/root_verification.json',
                previous_manifest=parent.parent/'publication-002/manifest.json')


def freeze(parent):
    parent = Path(parent)
    PREVIOUS.validate(parent)
    out = parent/'factor-probe-001'
    if out.exists():
        raise FileExistsError('new factor search required')
    for name in SOURCES:
        if not (R.ROOT/name).is_file():
            raise FileNotFoundError(name)
    if not R.read(inputs(parent)['parent_gram_verification'])['all_passed']:
        raise ValueError('verified Gram parent required')
    if not R.read(inputs(parent)['factor_calibration'])['all_passed']:
        raise ValueError('verified factor calibration required')
    for name, h in R.read(inputs(parent)['previous_manifest'])['files'].items():
        if R.sha(R.ROOT/name) != h:
            raise ValueError('previous publication source changed')
    out.mkdir()
    (out/'frozen_source').mkdir()
    hashes = {}
    for name in SOURCES:
        (out/'frozen_source'/name).write_bytes((R.ROOT/name).read_bytes())
        hashes[name] = R.sha(R.ROOT/name)
    protocol = dict(schema=1, programs=R.read(parent/'gram-probe-001/protocol.json')['programs'],
        training_scales=[1, 2, 3, 5], final_scales=[7, 11], limits=LIMITS, dual_limits=DUAL_LIMITS,
        tests=TESTS, factor_catalog=F.template_catalog(), dictionary=F.descriptors(),
        inputs_sha256={k:R.sha(p) for k,p in inputs(parent).items()},
        conditioning='new fixed language after prior exact obstruction; supplied closure, not independent discovery',
        selection='all 44 declared fractional-cut/kernel templates retained; no score-based choice',
        source_scale='N=4X-1, complete ordered coprime factor domain ab<=N',
        target='unchanged full original signed energy defect',
        auxiliary='same gamma=0 necessary constraint with zero coefficients for new groups; no arithmetic observation',
        final='identical scalar weights and both five-atom Gram matrices; no refit',
        dual_rule='if critical primal is not accepted, run one prescribed exact full-Gram separator search',
        historical_coefficient_overlap=True, unseen_prime_holdout=False,
        no_actual_signed_responses=True, solver_byte_replay_guaranteed=False,
        runtime=R.read(parent/'gram-probe-001/protocol.json')['runtime'], **FLAGS)
    write(out/'protocol.json', protocol)
    write(out/'source_seal.json', dict(hashes=hashes))
    write(out/'seal.json', dict(protocol_sha256=R.sha(out/'protocol.json'), source_seal_sha256=R.sha(out/'source_seal.json')))


def validate(parent):
    parent = Path(parent)
    PREVIOUS.validate(parent)
    out = parent/'factor-probe-001'
    if R.read(out/'seal.json') != dict(protocol_sha256=R.sha(out/'protocol.json'), source_seal_sha256=R.sha(out/'source_seal.json')):
        raise ValueError('factor source/protocol seal changed')
    hashes = R.read(out/'source_seal.json')['hashes']
    if set(hashes) != set(SOURCES):
        raise ValueError('factor source coverage')
    for n,h in hashes.items():
        if R.sha(R.ROOT/n) != h or R.sha(out/'frozen_source'/n) != h:
            raise ValueError('factor source changed: '+n)
    protocol = R.read(out/'protocol.json')
    if protocol['inputs_sha256'] != {k:R.sha(p) for k,p in inputs(parent).items()}:
        raise ValueError('factor input binding changed')
    return protocol


def build(program, X):
    return F.build_instance(program['target'], X, program['q'], program['C'], program['claim'])


def constraints(program):
    return [gate.build_constraint(F.descriptors())['instance']] if program['constraint']=='zero_cubic' else []


def train(program, scales, limits):
    row = dict(program=program, case_hashes=[], factor_archive_hashes=[], dictionary_sha256=R.digest(F.descriptors()),
               scalar_audits=[], gamma=None, budgets=[], independent_check=None, **FLAGS)
    try:
        built = [build(program, X) for X in scales]
        ordinary = [b['instance'] for b in built]
        instances = ordinary + constraints(program)
        row.update(case_hashes=list(map(R.digest, instances)),
                   factor_archive_hashes=[R.digest(b['factor_archive']) for b in built],
                   scalar_audits=[budget.audit_added_zero_scalars(i) for i in ordinary])
        result = S.synthesize(instances, scales, **limits)
        row['synthesis'] = result
        if result['status']=='finite_PSD_certificate':
            row['independent_check'] = I.verify_primal(instances, scales, result)
            row['gamma'] = str(gate.gamma(result['weights'], F.descriptors()))
            row['budgets'] = [budget.extract(i, result['weights']) for i in ordinary]
        return row
    except (OverflowError, TimeoutError, MemoryError) as e:
        row.update(synthesis=dict(status='missing_resource', reason=str(e) or type(e).__name__, **FLAGS),
                   external_resource_failure=True, gamma=None, budgets=[], independent_check=None)
        return row


def transfer(attempt, scales, limits):
    result, program = attempt['synthesis'], attempt['program']
    accepted = result['status']=='finite_PSD_certificate'
    final = dict(status='evaluated' if accepted else 'no_candidate', observations=[], refitted=False, **FLAGS)
    if not accepted:
        return final
    final.update(weights_sha256=R.digest(result['weights']), grams_sha256=R.digest(result['grams']))
    for X in scales:
        row = dict(X=X, case_sha256=None, factor_archive_sha256=None, scalar_budget=None,
                   dictionary_sha256=R.digest(F.descriptors()))
        try:
            b = build(program, X)
            instance = b['instance']
            # Calculate all metadata before publishing a non-null preparation binding.
            values = dict(case_sha256=R.digest(instance), factor_archive_sha256=R.digest(b['factor_archive']),
                          scalar_budget=budget.extract(instance, result['weights']))
            row.update(values)
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
    out = parent/'factor-probe-001'
    protocol = validate(parent)
    if (out/'tests.json').exists():
        raise FileExistsError('factor search already started')
    tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=R.ROOT,
                           capture_output=True, text=True, timeout=120)
    write(out/'tests.json', dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr))
    if tests.returncode:
        raise ValueError('factor search tests failed')
    (out/'attempts').mkdir()
    attempts = []
    for j, program in enumerate(protocol['programs']):
        attempt = train(program, protocol['training_scales'], protocol['limits'])
        write(out/'attempts'/f'{j:03d}.json', attempt)
        attempts.append(attempt)
        print(json.dumps(dict(index=j, status=attempt['synthesis']['status'], gamma=attempt['gamma'])), flush=True)
    write(out/'training.json', dict(attempts=attempts, no_actual_signed_responses=True, **FLAGS))
    write(out/'candidate_seal.json', dict(training_sha256=R.sha(out/'training.json'), protocol_sha256=R.sha(out/'protocol.json')))
    write(out/'final.json', dict(results=[transfer(a, protocol['final_scales'], protocol['limits']) for a in attempts], refitted=False, **FLAGS))
    check = None
    if attempts[0]['synthesis']['status']=='finite_PSD_certificate':
        dual = dict(status='not_requested', certified=False, **FLAGS)
    else:
        try:
            program = protocol['programs'][0]
            instances = [build(program, X)['instance'] for X in protocol['training_scales']] + constraints(program)
            dual = D.propose(instances, protocol['training_scales'], allow_constant_slack=True, **protocol['dual_limits'])
            if dual.get('certified'):
                check = I.verify_dual(instances, protocol['training_scales'], dual)
        except (OverflowError, TimeoutError, MemoryError) as e:
            dual = dict(status='missing_resource', certified=False, reason=str(e) or type(e).__name__, **FLAGS)
    write(out/'dual.json', dict(trigger='critical primal not accepted', result=dual, independent_check=check, **FLAGS))
    print(json.dumps(dict(dual_status=dual['status'], dual_certified=dual.get('certified', False))), flush=True)
    validate(parent)
    write(out/'producer_receipt.json', dict(**{n+'_sha256':R.sha(out/(n+'.json')) for n in
        ['training', 'final', 'dual', 'tests', 'candidate_seal', 'source_seal']}, original_results_unchanged=True, **FLAGS))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('command', choices=['freeze', 'run'])
    parser.add_argument('parent')
    args = parser.parse_args()
    (freeze if args.command=='freeze' else run)(args.parent)
