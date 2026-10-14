"""Append-only completion of the stopped audit, without repeating checked moments.

The original per-phase allocation was exhausted. This explicit addendum uses
the UNUSED total study allowance, retains the original receipt, and checks only
uncompleted moment rows. This does not claim the original allocation sufficed.
"""
from fractions import Fraction as Q
from pathlib import Path
import resource
import sys
import time

import check_reversible_divisor_circuits as C
import run_reversible_circuit_discovery as R
import reversible_circuit_discovery as D


def complete(directory):
    directory = Path(directory).resolve()
    R.frozen_source(directory)
    stopped = R.read(directory / 'independent_verification.json')
    receipt = R.read(directory / 'receipt.json')
    tests = R.read(directory / 'tests.json')
    rows = R.read(directory / 'final_responses.json')
    selected = R.read(directory / 'final_batch.json')
    if (stopped['status'] != 'UNKNOWN' or stopped.get('error_type') != 'OverflowError'
            or stopped.get('reason') != 'shared exact evaluator operation cap'
            or stopped['counts']['operations'] != R.ALLOCATIONS['independent']
            or stopped['certificates_checked'] != 65 or stopped['cases_verified'] != 616
            or len(rows) != 27 or any(row['status'] != 'available' for row in rows)):
        raise ValueError('this addendum is restricted to the recorded stopped audit')
    # Original audit's counter increments only AFTER exact moments AND finite
    # head agree. Its sequential order is520 discovery moments, then4 per row.
    completed_rows = (stopped['cases_verified'] - 65 * 8) // len(D.FINAL)
    if completed_rows != 24:
        raise ValueError('declared checkpoint binding')
    prior = (tests['work']['total'] + stopped['counts']['operations']
             + sum(v['operations'] for v in receipt['stage_counts'].values())
             + sum(w['counts']['operations'] for w in receipt['final_workers']))
    remaining = 450000000 - prior
    if remaining <= 0:
        raise ValueError('no remaining original total allowance')
    plan = dict(schema='reversible-circuit-audit-allocation-addendum-v1',
                reason='original independent phase allocation exhausted with three final control rows incomplete',
                original_receipt='independent_verification.json', prior_cumulative_operations=prior,
                remaining_original_total_allowance=remaining, total_ceiling_unchanged=450000000,
                first_uncompleted_final_row=completed_rows,
                rows_to_complete=[dict(id=r['id'], source=r['source']) for r in rows[completed_rows:]],
                previously_checked_moments_recomputed=False, numerical_candidates_or_responses_changed=False,
                scores_and_receipt_metadata_rechecked=True,
                original_phase_allocation_changed=True,
                actual_research_runs=1, audit_is_continued_not_restarted=True)
    code = Path(__file__).read_bytes()
    with (directory / 'audit_completion_source.py').open('xb') as handle:
        handle.write(code)
    R.write(directory / 'audit_allocation_addendum.json', plan)
    meter = C.Meter(remaining, deadline=time.monotonic() + 7200)
    start = time.monotonic(); completed = []
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, hard))
    result = dict(status='INCOMPLETE', original_phase_allocation_changed=True,
                  original_receipt_unchanged=True, **D.FLAGS)
    try:
        if R.read(directory / 'protocol.json') != R.protocol():
            raise ValueError('unchanged original research protocol')
        if tests['work'] != R.synthetic_receipt(tests['stdout']):
            raise ValueError('all prior synthetic work remains charged')
        if [w['source'] for w in receipt['final_workers']] != R.SOURCES:
            raise ValueError('ordered parallel source partitions')
        if sum(w['allocated'] for w in receipt['final_workers']) != R.ALLOCATIONS['final']:
            raise ValueError('original disjoint final allocations')
        for i, name in enumerate(R.SOURCES):
            worker = R.read(directory / ('final_source_' + name + '.json'))
            if ({k: v for k, v in worker.items() if k != 'rows'} != receipt['final_workers'][i]
                    or worker['rows'] != rows[i * len(selected):(i + 1) * len(selected)]
                    or not 0 <= worker['counts']['operations'] <= worker['allocated']):
                raise ValueError('unchanged complete source receipt')
        # Score calculation may have hit the cap after the last successful
        # moment counter increment; recheck cheap metadata without reevaluation.
        for index, row in enumerate(rows):
            item = selected[index % len(selected)]
            if (row['id'] != item['record']['id'] or row['source'] != R.SOURCES[index // len(selected)]
                    or row['constants'] != item['constants']
                    or row['scores'] != R._independent_scores(row['cases'], row['constants'], meter)):
                raise ValueError('complete final source/program/frozen-score binding')
        values = C.source('partial_prime_13', 2 * max(D.FINAL) - 1, meter)
        for index in range(completed_rows, len(rows)):
            row = rows[index]; record = selected[index % len(selected)]['record']
            if row['source'] != 'partial_prime_13':
                raise ValueError('uncompleted control source')
            output = C.evaluate(record['program'], values, meter)
            if C.moments(output, D.FINAL, meter) != row['cases']:
                raise ValueError('uncompleted exact moments disagree')
            head = Q(0)
            for n in range(1, 32):
                head = meter.number(head + Q(output[n] * output[n], n * n))
            if str(head) != row['initial_cost']:
                raise ValueError('uncompleted initial cost disagrees')
            completed.append(dict(id=row['id'], source=row['source'], moments=len(D.FINAL)))
        meter.charge(sum(len(D.canonical(x)) // 16 + 1 for x in (rows, selected, tests, stopped, receipt, plan)))
        result.update(status='FINITE_EVALUATION_VERIFIED_WITH_ALLOCATION_ADDENDUM',
                      finite_arithmetic_verified=True, recovery_certificates_checked=True,
                      original_checked_moments=stopped['cases_verified'],
                      total_moments_verified=stopped['cases_verified'] + sum(r['moments'] for r in completed),
                      certificates_checked=stopped['certificates_checked'],
                      cumulative_operations=prior + meter.operations,
                      scope='same independent evaluator; three uncompleted control rows only, plus cheap receipt/score binding; original phase allocation explicitly amended within original total budget')
    except (ValueError, TypeError, KeyError, OverflowError, TimeoutError, MemoryError) as error:
        result.update(reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        result.update(completed_rows=completed, counts=meter.counts(), elapsed_seconds=time.monotonic() - start,
                      peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        R.write(directory / 'independent_completion.json', result)
        resource.setrlimit(resource.RLIMIT_AS, (soft, hard))
    return result


if __name__ == '__main__':
    print(D.canonical(complete(sys.argv[1])))
