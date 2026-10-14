"""Complete only unfinished control cases under the user's small-limit extension.

The original 450m ceiling was insufficient. Keep that receipt and protocol
unchanged; explicitly amend only the verification work ceiling to at most +7%.
Every spent operation, including the interrupted case, remains in the ledger.
"""
from fractions import Fraction as Q
import json
from pathlib import Path
import resource
import sys
import time

import check_permuted_arithmetic_circuits as C
import permuted_circuit_discovery as D
import run_permuted_circuit_discovery as R

EXTENDED_CEILING = 481500000


def pending_cases(expected, checkpoints, meter):
    """Accept an exact completed prefix; never reevaluate its cases."""
    if len(checkpoints) > len(expected):
        raise ValueError('checkpoint prefix exceeds declared cases')
    previous = -1
    for row, checkpoint in zip(expected, checkpoints):
        meter.charge(8)
        if any(type(checkpoint.get(k)) is not type(row[k]) or checkpoint[k] != row[k]
               for k in ('id', 'source', 'horizon', 'status')):
            raise ValueError('checkpoint is not the exact declared case prefix')
        if checkpoint.get('kind') != 'completed_evaluation' or checkpoint.get('finite_verified') is not True:
            raise ValueError('only fully verified completed cases may be skipped')
        current = checkpoint['counts']['operations']
        if type(current) is not int or current < previous:
            raise ValueError('monotone retained audit counters')
        previous = current
    return expected[len(checkpoints):]


def complete(directory):
    directory = Path(directory).resolve()
    R.frozen_source(directory)
    stopped = R.read(directory / 'independent_verification.json')
    receipt, tests = R.read(directory / 'receipt.json'), R.read(directory / 'tests.json')
    cases, final = R.read(directory / 'discovery_cases.json'), R.read(directory / 'final_responses.json')
    catalog, selected = R.read(directory / 'candidate_batch.json'), R.read(directory / 'final_batch.json')
    raw = (directory / 'independent_checkpoints.jsonl').read_bytes()
    if len(raw) > R.CAP:
        raise OverflowError('bounded original checkpoints')
    checkpoints = [json.loads(line) for line in raw.splitlines()]
    prior = (tests['work']['total'] + sum(v['operations'] for v in receipt['stage_counts'].values())
             + sum(w['counts']['operations'] for w in receipt['final_workers']) + stopped['counts']['operations'])
    if (stopped['status'] != 'UNKNOWN' or stopped.get('error_type') != 'OverflowError'
            or stopped.get('reason') != 'shared exact evaluator operation cap'
            or stopped['cumulative_operations'] != prior or stopped['evaluations_verified'] != len(checkpoints)
            or stopped['certificates_checked'] != len(catalog) or stopped['missing_or_invalid'] != 0
            or prior > R.TOTAL or EXTENDED_CEILING * 100 > R.TOTAL * 107
            or stopped['previously_consumed'] != prior - stopped['counts']['operations']
            or any(c['counts']['operations'] > stopped['counts']['operations']
                   or c['cumulative_operations'] != stopped['previously_consumed'] + c['counts']['operations']
                   for c in checkpoints)
            or tests['work'] != R.synthetic_receipt(tests['stdout'])):
        raise ValueError('explicit unchanged stopped audit and all prior work required')
    start = time.monotonic()
    deadline = time.monotonic() + max(0, R.SECONDS - (time.time() - R.read(directory / 'run_started.json')['epoch']))
    meter = R._meter(EXTENDED_CEILING - prior, deadline)
    expected = cases + final
    pending = pending_cases(expected, checkpoints, meter)
    if (len(pending) != 2 or [(r['source'], r['id']) for r in pending] != [('partial_prime_13', 33), ('partial_prime_13', 42)]
            or any(r['status'] != 'available' for r in expected)):
        raise ValueError('this continuation is restricted to the two unfinished final controls')
    plan = dict(schema='permuted-audit-work-extension-v1', original_ceiling=R.TOTAL,
                revised_ceiling=EXTENDED_CEILING, maximum_increase_percent=7,
                authorization='User: I think we can expand the work limits a little if we are going over by only 7%.',
                original_resource_rule_explicitly_amended=True,
                original_ceiling_met=False, original_receipt_unchanged=True,
                prior_cumulative_operations=prior, available_additional_work=EXTENDED_CEILING - prior,
                completed_evaluations_not_repeated=len(checkpoints),
                unfinished_cases=[dict(id=r['id'], source=r['source'], horizon=r['horizon']) for r in pending],
                scope='two unfinished final control evaluations and metadata; catalogue, responses, selection and arithmetic code unchanged',
                research_attempts=1, original_interrupted_work_still_charged=True,
                continuation_development_checks='metadata-only tests charged to the original root scaffolding reserve')
    # These exclusive files freeze the continuation before any source evaluation.
    with (directory / 'audit_completion_source.py').open('xb') as handle:
        handle.write(Path(__file__).read_bytes())
    with (directory / 'audit_completion_test_source.py').open('xb') as handle:
        handle.write((R.ROOT / 'test_complete_permuted_circuit_audit.py').read_bytes())
    R.write(directory / 'audit_work_extension.json', plan)
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, hard))
    completed = []
    result = dict(status='INCOMPLETE', finite_arithmetic_verified=False,
                  recovery_certificates_checked=False, original_ceiling_met=False,
                  revised_ceiling=EXTENDED_CEILING, original_receipt_unchanged=True, **D.FLAGS)
    try:
        if catalog != D.generate_catalog(meter, C):
            raise ValueError('unchanged catalogue and independently reconstructed normalizations')
        for record in catalog:
            C.verify(record['certificate'], meter)
        analysis = R.independent_analysis(catalog, cases, meter)
        selection = R.independent_selection(analysis, meter)
        if (analysis != R.read(directory / 'discovery_analysis.json')
                or selection != R.read(directory / 'selection.json')
                or selected != [dict(record=catalog[i], constants=analysis[i]['constants']) for i in selection['selected_ids']]
                or R.read(directory / 'proof_queue.json') != [D.obligation(r['record']) for r in selected if r['record']['id']]):
            raise ValueError('unchanged fits, selection and proof obligations')
        cursor = 0
        for w in receipt['final_workers']:
            worker = R.read(directory / ('final_source_' + w['source'] + '.json'))
            if ({k: v for k, v in worker.items() if k != 'rows'} != w
                    or worker['rows'] != final[cursor:cursor + len(selected)]
                    or w['allocated'] != R.FINAL_BUDGETS[w['source']]
                    or not 0 <= w['counts']['operations'] <= w['allocated']):
                raise ValueError('unchanged disjoint final source receipt')
            cursor += len(selected)
        if cursor != len(final):
            raise ValueError('complete final batch')
        for i, row in enumerate(final):
            item = selected[i % len(selected)]; name = D.SOURCES[i // len(selected)]
            if (row['id'] != item['record']['id'] or row['source'] != name
                    or row['horizon'] != D.FINAL_HORIZONS[name] or row['scales'] != D.FINAL_SCALES[name]
                    or row['constants'] != item['constants']):
                raise ValueError('complete final program/source/scale binding')
            scores = []
            for case in row['cases']:
                for q in D.LEVELS:
                    k = 1
                    while k ** q < case['X']:
                        meter.charge(q); k += 1
                    bound = meter.number(Q(item['constants'][str(q)]) * k)
                    scores.append(dict(X=case['X'], q=q, bound=str(bound), passed=Q(case['energy']) <= bound,
                                       dyadic=case['X'] & (case['X'] - 1) == 0))
            if row['scores'] != scores:
                raise ValueError('independent final scores without refitting')
        values = C.source('partial_prime_13', D.FINAL_HORIZONS['partial_prime_13'], meter)
        records = {r['record']['id']: r['record'] for r in selected}
        for row in pending:
            state = C.evaluate(records[row['id']]['program'], values, meter)
            if (C.moments(state, row['scales'], meter) != row['cases']
                    or C.initial_cost(state, meter) != row['initial_cost'] or 'decomposition' in row):
                raise ValueError('remaining complete control arithmetic differs')
            checked = dict(id=row['id'], source=row['source'], horizon=row['horizon'], status='available',
                           kind='completed_evaluation', finite_verified=True, counts=meter.counts(),
                           cumulative_operations=prior + meter.operations)
            completed.append(checked)
            R.append_checkpoint(directory / 'independent_completion_checkpoints.jsonl', checked)
        result.update(status='FINITE_EVALUATIONS_VERIFIED_WITH_WORK_EXTENSION', finite_arithmetic_verified=True,
                      recovery_certificates_checked=True, all_expected_evaluations_available=True,
                      selected_ids=selection['selected_ids'],
                      scope='same independent arithmetic; original301 completed cases retained; only two unfinished controls reevaluated; metadata rechecked; all theorem gates unproved')
    except (ValueError, TypeError, KeyError, OverflowError, TimeoutError, MemoryError, ZeroDivisionError) as error:
        result.update(reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        result.update(evaluations_verified=len(checkpoints) + len(completed), certificates_checked=len(catalog),
                      completed_cases=completed, counts=meter.counts(), cumulative_operations=prior + meter.operations,
                      original_cumulative_operations=prior, elapsed_seconds=time.monotonic() - start)
        R.write(directory / 'independent_completion.json', result)
        resource.setrlimit(resource.RLIMIT_AS, (soft, hard))
    return result


if __name__ == '__main__':
    print(D.canonical(complete(sys.argv[1])))
