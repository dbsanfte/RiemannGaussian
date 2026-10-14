"""One sealed, outcome-conditioned round of exact dual-guided square expansion."""
import argparse
import copy
import json
import subprocess
import sys
from pathlib import Path
import run_cancellation_arithmetic as R
import cancellation_dual_column_search as C
import cancellation_arithmetic_synthesis as S
import cancellation_cubic_gate as gate
import cancellation_budget as budget
import grouped_arithmetic_synthesis as finite
import check_grouped_arithmetic as G

EXTRA = ['run_cancellation_adaptive_probe.py', 'cancellation_dual_column_search.py',
         'test_cancellation_dual_column_search.py', 'cancellation_dual_column_search_independent_review.txt']
LIMITS = dict(R.LIMITS, time_limit=60, max_coefficient_bits=4096, max_denominator=1000000000000)


def freeze(parent):
    parent = Path(parent); R.validate_sources(parent)
    if not R.read(parent/'independent_verification.json')['all_passed']: raise ValueError('parent audit required')
    dual = parent/'dual-probe-002'
    if not R.read(dual/'independent_verification.json')['all_passed']: raise ValueError('exact dual audit required')
    out = parent/'adaptive-probe-001'
    if out.exists(): raise FileExistsError('new adaptive round required')
    for n in EXTRA:
        if not (R.ROOT/n).exists(): raise FileNotFoundError(n)
    out.mkdir(); (out/'frozen_source').mkdir(); hashes = {}
    for n in EXTRA:
        (out/'frozen_source'/n).write_bytes((R.ROOT/n).read_bytes()); hashes[n] = R.sha(R.ROOT/n)
    spec = dict(attempt_index=26, limits=LIMITS, descriptors=C.enumerate_descriptors(), max_new_groups=8,
        proposal_limits=dict(max_operations=20000000, max_horizon=127), final_scales=[11, 13],
        parent_training_sha256=R.sha(parent/'training.json'), parent_verification_sha256=R.sha(parent/'independent_verification.json'),
        dual_result_sha256=R.sha(dual/'result.json'), dual_verification_sha256=R.sha(dual/'independent_verification.json'),
        selection='all120 directions retained; exact negative dots sorted by dot/(1+coefficient^2), canonical ID ties; first8',
        conditioning='posthoc response to a verified obstruction; source and rule sealed before this batch scores; not independent unknown-operator discovery',
        final='same selected dictionary and learned weights; no refit; historical arithmetic coefficients overlap',
        global_bound_proved=False, RH_proved=False)
    R.write(out/'spec.json', spec); R.write(out/'source_seal.json', dict(hashes=hashes))
    R.write(out/'seal.json', dict(spec_sha256=R.sha(out/'spec.json'), source_seal_sha256=R.sha(out/'source_seal.json')))


def validate(parent):
    parent = Path(parent); R.validate_sources(parent); out = parent/'adaptive-probe-001'
    if R.read(out/'seal.json') != dict(spec_sha256=R.sha(out/'spec.json'), source_seal_sha256=R.sha(out/'source_seal.json')):
        raise ValueError('adaptive seal changed')
    hashes = R.read(out/'source_seal.json')['hashes']
    if set(hashes) != set(EXTRA): raise ValueError('adaptive source coverage')
    for n,h in hashes.items():
        if R.sha(R.ROOT/n) != h or R.sha(out/'frozen_source'/n) != h: raise ValueError('adaptive source changed')
    spec = R.read(out/'spec.json')
    for key,path in [('parent_training', parent/'training.json'), ('parent_verification', parent/'independent_verification.json'),
                     ('dual_result', parent/'dual-probe-002/result.json'), ('dual_verification', parent/'dual-probe-002/independent_verification.json')]:
        if spec[key+'_sha256'] != R.sha(path): raise ValueError('adaptive input changed')
    return spec


def augmented(program, X, selected):
    b = R.build(program, X)
    for candidate in selected:
        desc = candidate['descriptor']
        b['instance']['square_groups'].append(C.build_group(desc, X, b['instance']['horizon']))
        b['square_ids'].append(desc['id'])
    ds = copy.deepcopy(R.dictionary(program)); ds['square'].extend(c['descriptor'] for c in selected)
    b['dictionary_sha256'] = R.digest(ds)
    return b


def run(parent):
    parent = Path(parent); out = parent/'adaptive-probe-001'; spec = validate(parent)
    if (out/'tests.json').exists(): raise FileExistsError('adaptive round already started')
    test = subprocess.run([sys.executable, '-B', '-m', 'unittest', 'test_cancellation_dual_column_search'],
                           cwd=R.ROOT, capture_output=True, text=True, timeout=30)
    R.write(out/'tests.json', dict(returncode=test.returncode, stdout=test.stdout, stderr=test.stderr))
    if test.returncode: raise ValueError('adaptive utility tests failed')
    attempt = R.read(parent/'training.json')['attempts'][spec['attempt_index']]
    program = attempt['program']; scales = R.read(parent/'protocol.json')['training_scales']
    ordinary = [R.build(program, X)['instance'] for X in scales]; aux = R.constraints(program)
    if list(map(R.digest, ordinary+aux)) != attempt['case_hashes']+attempt['auxiliary_hashes']:
        raise ValueError('adaptive source cases')
    dual = R.read(parent/'dual-probe-002/result.json')['dual']
    proposals = C.propose(ordinary+aux, dual, scales, spec['max_new_groups'], **spec['proposal_limits'])
    R.write(out/'proposals.json', proposals)
    selected = proposals['selected']
    ds = copy.deepcopy(R.dictionary(program)); ds['square'].extend(c['descriptor'] for c in selected)
    ordinary = [augmented(program, X, selected)['instance'] for X in scales]
    auxiliary = [gate.build_constraint(ds)['instance']]
    instances = ordinary+auxiliary
    R.write(out/'selection_seal.json', dict(proposals_sha256=R.sha(out/'proposals.json'), selected_sha256=R.digest(selected),
        dictionary_sha256=R.digest(ds), case_hashes=list(map(R.digest, instances))))
    result = S.synthesize(instances, allow_constant_slack=True, **spec['limits'])
    check = G.verify_joint_result(instances, result, allow_constant_slack=True)
    accepted = result['status'] == 'finite_certificate'
    training = dict(program=program, synthesis=result, independent_check=check,
        case_hashes=list(map(R.digest, instances)), gamma=str(gate.gamma(result['weights'], ds)) if accepted else None,
        budgets=[budget.extract(i, result['weights']) for i in ordinary] if accepted else [],
        global_bound_proved=False, RH_proved=False)
    R.write(out/'training.json', training)
    R.write(out/'candidate_seal.json', dict(training_sha256=R.sha(out/'training.json'), selection_seal_sha256=R.sha(out/'selection_seal.json')))
    print(json.dumps(dict(enumerated=len(proposals['candidates']), negative=sum(c['negative'] for c in proposals['candidates']),
                         selected=len(selected), training_status=result['status'], gamma=training['gamma'])), flush=True)
    final = []
    if accepted:
        for X in spec['final_scales']:
            row = dict(X=X, case_sha256=None, scalar_budget=None)
            try:
                b = augmented(program, X, selected); instance = b['instance']
                row.update(case_sha256=R.digest(instance), scalar_budget=budget.extract(instance, result['weights']))
            except (OverflowError, TimeoutError, MemoryError) as e:
                row.update(status='missing_resource', reason=str(e) or type(e).__name__); final.append(row); continue
            try:
                cert = finite.instantiate_certificate(instance, result['weights'], allow_constant_slack=True, **spec['limits'])
                checked = G.verify_joint([instance], **result['weights'], allow_constant_slack=True)
                G.verify_certificate(cert)
                row.update(status='finite_certificate', certificate=cert, independent_check=checked)
            except (OverflowError, TimeoutError, MemoryError) as e:
                row.update(status='missing_resource', reason=str(e) or type(e).__name__)
            except ValueError as e:
                row.update(status='template_mismatch', reason=str(e))
            final.append(row); print(json.dumps(dict(final_X=X, status=row['status'])), flush=True)
    R.write(out/'final.json', dict(status='evaluated' if accepted else 'no_candidate', observations=final, refitted=False,
                                  global_bound_proved=False, RH_proved=False))
    validate(parent)
    R.write(out/'producer_receipt.json', dict(**{name+'_sha256':R.sha(out/(name+'.json')) for name in
        ('proposals', 'training', 'final', 'tests', 'selection_seal', 'candidate_seal')},
        original_results_unchanged=True, global_bound_proved=False, RH_proved=False))


if __name__ == '__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('command', choices=('freeze','run')); parser.add_argument('parent')
    args=parser.parse_args(); (freeze if args.command=='freeze' else run)(args.parent)
