"""Freeze geometry-only floor-bound synthesis, then audit all067 source heads."""
import os
for _thread_variable in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_thread_variable] = '1'

from fractions import Fraction as Q
import json
import multiprocessing as mp
from pathlib import Path
import resource
import time

import mobius_floor_control_068 as SEARCH
import check_mobius_floor_control_068 as CHECK
import run_mobius_signed_lag_067 as PRIOR
from run_fractional_prime_kernel_051 import write, emit, check_receipt

ROOT = PRIOR.ROOT
OUT = PRIOR.OUT/'floor_control_followup_001'
FILES = ['mobius_floor_control_068.py', 'test_mobius_floor_control_068.py',
    'mobius_floor_control_search_068_development.json', 'check_mobius_floor_control_068.py',
    'test_check_mobius_floor_control_068.py', 'mobius_floor_control_checker_068_development.json',
    'MOBIUS_FLOOR_CONTROL_CHECK_SCOPE_068.txt', 'MOBIUS_FLOOR_CONTROL_REVIEW_068.txt',
    'run_mobius_floor_control_068.py', 'mobius_floor_control_protocol_068.txt']
SPEC = {'sources': 'all36 completed067 cases, grouped by12 distinct N,y pairs',
    'head_stop': 'ceil(H/2)-1; synthesize each distinct row only once per endpoint',
    'learner_inputs': ['N', 'y', 'max_j', 'parameters', 'exponents', 'horizon_limit'],
    'learner_actual_mu_signs_or_target_values': False,
    'unsigned_squarefree_mask': 'multiples of all integer squares; complete floor identity supplied',
    'exponents': SEARCH.DEFAULT_EXPONENTS, 'extra_empty_dictionary_baseline': True,
    'dictionary': 'distinct joined endpoint quotients through floor(N^theta); rank-spread cap',
    'horizon_limit': SEARCH.MAX_HORIZONS, 'coefficient_grid': SEARCH.GRID,
    'coefficient_box': '4*endpoint_denominator*max(1,horizon_count)',
    'solver': 'HiGHS dual simplex;30s per solve; rounded feasible proposals replayed exactly',
    'selection': 'exact upper price, nonzero coefficient count, dictionary size, stable order',
    'secondary_archive': 'best incomplete quotient-span price retained; incompleteness is not a nonencoding proof',
    'dual': 'rounded bounded multipliers with exact coefficient-box stationarity penalty',
    'complete_quotient_span': 'encoding-risk flag; no automatic proof promotion',
    'far_transfer': 'finite S_I-D_I-near_I from new row prices and saved exact067 diagnostics',
    'workers': 3, 'native_threads_per_worker': 1, 'maximum_aggregate_bytes': 16*1024**3,
    'work_cap_per_case_meter': 300_000_000_000, 'module_seconds': 7200,
    'fresh_holdout_claim': False, 'anticipated_winner': None, 'hashes_used': False,
    'uniform_full_head_bound_claim': False}


def validate_parent():
    counts = PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve067 '+name)
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if (report['independent_lag_certificates'] != 36 or not report['uniform_diagonal_bound_proved']
            or not report['uniform_short_lag_bound_proved'] or report['RH_proved']):
        raise ValueError('completed067 with paid surrounds and open signed bound')
    return counts+[len(PRIOR.FILES)]


def bind_lag(saved, sparse):
    source = PRIOR.bind_sparse(sparse)
    cert, verdict = saved['certificate'], saved['verification']
    if (not verdict['verified'] or not saved['same_raw_source_head']
            or not saved['all_lags_and_rows_verified'] or saved['RH_proved']
            or saved['uniform_far_correlation_bound_proved']):
        raise ValueError('verified same raw067 source')
    for field in ('N', 'y', 'H'):
        if saved[field] != source[field] or cert[field] != source[field] or verdict[field] != source[field]:
            raise ValueError('same067 source coordinates')
    if cert['parameters'] != source['parameters'] or verdict['parameters'] != source['parameters']:
        raise ValueError('same067 registered source parameters')
    if cert['head_stop'] != (source['H']+1)//2-1 or len(cert['endpoints']) != 2:
        raise ValueError('complete067 head and ratio endpoints')
    return source


def group_sources(records):
    groups = {}
    for name, saved in records:
        cert = saved['certificate']; key = (cert['N'], cert['y'])
        if key not in groups:
            groups[key] = dict(N=key[0], y=key[1], parameters=cert['parameters'], max_j=0, lag_files=[])
        group = groups[key]
        if group['parameters'] != cert['parameters']:
            raise ValueError('identical geometry within group')
        group['max_j'] = max(group['max_j'], cert['head_stop'])
        group['lag_files'].append(name)
    return [groups[k] for k in sorted(groups)]


def chosen(row, index=None):
    return row['models'][row['selected_model'] if index is None else row['plans'][index]['model_index']]


def incomplete_model(row):
    indices = {p['model_index'] for p in row['plans'] if not p['complete_endpoint_quotients']}
    if not indices: return None
    return min(indices, key=lambda i: (Q(row['models'][i]['bound']),
        sum(v != 0 for v in row['models'][i]['primal_numerators']), len(row['models'][i]['horizons']), i))


def summarize_case(saved, source, cert, verdict):
    head = saved['certificate']['head_stop']; endpoints = []
    for old, sparse, endpoint, checked in zip(saved['certificate']['endpoints'], source['endpoints'], cert['endpoints'], verdict['endpoints']):
        if not old['ratio'] == sparse['ratio'] == endpoint['ratio'] == checked['ratio']:
            raise ValueError('same ratio order across source and control')
        rows = endpoint['rows'][:head]; checks = checked['rows'][:head]
        actual = [Q(r['actual_coefficient']) for r in checks]
        if actual != [Q(r['coefficient']) for r in sparse['rows'][:head]]:
            raise ValueError('every new raw coefficient matches admitted066 source')
        price = [Q(chosen(r)['bound']) for r in rows]
        baseline = sum((Q(chosen(r, 0)['bound']) for r in rows), Q(0))
        total = sum(price, Q(0)); measured = sum(map(abs, actual), Q(0))
        if not measured <= total <= baseline:
            raise ValueError('valid selected head control and retained baseline')
        plans = []
        for index, exponent in enumerate([None]+cert['exponent_requests']):
            models = [chosen(r, index) for r in rows]
            plans.append(dict(exponent=exponent,
                head_upper=str(sum((Q(m['bound']) for m in models), Q(0))),
                head_box_optimum_lower=str(sum((max(Q(0), Q(m['box_optimum_lower'])) for m in models), Q(0))),
                horizons=sum(len(m['horizons']) for m in models),
                nonzero_coefficients=sum(sum(v != 0 for v in m['primal_numerators']) for m in models),
                complete_span_rows=sum(r['plans'][index]['complete_endpoint_quotients'] for r in rows),
                truncated_rows=sum(r['plans'][index]['dictionary_truncated'] for r in rows),
                uniform_bound_proved=False))
        blocks = []
        for block in old['blocks']:
            L, U = block['start'], block['stop']; den = endpoint['denominator']
            direct = [Q(rows[j-1]['direct_scaled'], den) for j in range(L, U+1)]
            z = [actual[j-1]-d for j, d in zip(range(L, U+1), direct)]
            if (sum((a*a for a in z), Q(0)) != Q(block['moment'])
                    or [Q(v, den) for v in block['row_sums_scaled']] != z
                    or [Q(v) for v in block['direct_coefficients']] != direct):
                raise ValueError('same exact067 moment from new independently checked rows')
            S = sum(((price[j-1]+abs(d))**2 for j, d in zip(range(L, U+1), direct)), Q(0))
            if S < Q(block['moment']): raise ArithmeticError('row-price energy transfer')
            far = []
            for old_part in block['candidates']:
                upper = S-Q(block['diagonal'])-Q(old_part['near_signed'])
                if Q(old_part['far_signed']) > upper:
                    raise ArithmeticError('finite signed far upper from synthesized row controls')
                far.append(dict(exponent=old_part['exponent'], used_cutoff=old_part['used_cutoff'],
                    far_upper=str(upper), observed_far=old_part['far_signed'],
                    finite_positive_risk_upper=str(PRIOR.SEARCH.sqrt_upper((U-L+1)*max(Q(0), upper)))))
            blocks.append(dict(start=L, stop=U, synthesized_energy_upper=str(S),
                saved_diagonal=block['diagonal'], far_controls=far,
                finite_saved_near_subtraction=True, uniform_far_bound_proved=False))
        partial = [incomplete_model(r) for r in rows]
        endpoints.append(dict(ratio=endpoint['ratio'], head_stop=head,
            actual_head_variation=str(measured), empty_dictionary_head_upper=str(baseline),
            selected_head_upper=str(total), improvement_factor=str(baseline/total) if total else None,
            selected_head_box_gap=str(sum((Q(chosen(r)['box_gap']) for r in rows), Q(0))),
            selected_complete_span_rows=sum(any(p['model_index']==r['selected_model'] and p['complete_endpoint_quotients'] for p in r['plans']) for r in rows),
            selected_zero_residual_rows=sum(chosen(r)['residual_l1_numerator']==0 for r in rows),
            selected_exact_target_price_rows=sum(Q(chosen(r)['bound'])==abs(a) for r, a in zip(rows, actual)),
            incomplete_span_head_upper=(str(sum((Q(r['models'][i]['bound']) for r, i in zip(rows, partial)), Q(0)))
                                        if all(i is not None for i in partial) else None),
            all_exponent_plans=plans, dyadic_far_controls=blocks,
            uniform_head_bound_proved=False))
    return dict(N=cert['N'], y=cert['y'], H=saved['H'], theta=saved['theta'], endpoints=endpoints)


def evaluate_task(task):
    started = time.monotonic(); sources = []
    for name in task['lag_files']:
        saved = json.loads((PRIOR.OUT/name).read_text())
        sparse = json.loads((PRIOR.PRIOR.OUT/saved['source_sparse_file']).read_text())
        source = bind_lag(saved, sparse)
        if any(source[f] != task[f] for f in ('N', 'y', 'parameters')):
            raise ValueError('source group provenance')
        sources.append((name, saved, source))
    meter = SEARCH.Meter(cap=SPEC['work_cap_per_case_meter'], seconds=SPEC['module_seconds'])
    cm = CHECK.Meter(cap=SPEC['work_cap_per_case_meter'], seconds=SPEC['module_seconds'])
    # No signed source, lag moment, target, or prior price reaches construct().
    cert = SEARCH.construct(task['N'], task['y'], task['max_j'], task['parameters'],
        SPEC['exponents'], SPEC['horizon_limit'], meter)
    verdict = CHECK.verify_control(cert, cm)
    summaries = [summarize_case(saved, source, cert, verdict) for _, saved, source in sources]
    models = [m for e in cert['endpoints'] for r in e['rows'] for m in r['models']]
    return dict(N=task['N'], y=task['y'], max_j=task['max_j'], source_lag_files=task['lag_files'],
        certificate=cert, verification=verdict, original_source_binding_proved=True,
        source_cases=summaries, unique_models=len(models),
        lp_proposals=sum(bool(m['horizons']) for m in models),
        failed_lp_zero_fallbacks=sum(m['solver']['status']=='failed_zero_fallback' for m in models),
        solver_iterations=sum(m['solver']['iterations'] for m in models),
        producer_operations=meter.operations, checker_operations=cm.operations,
        prospective_algorithm_bytes=meter.peak_bytes_estimate,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        elapsed_seconds=time.monotonic()-started, uniform_head_bound_proved=False, RH_proved=False)


def feedback(results):
    return dict(schema='mobius-floor-control-feedback-v1',
        previous_goal_turn='067 substantive: exact signed lag compiler, diagonal and short-lag uniform payment',
        current_goal_turn='068 automatic floor-annihilator bound synthesis, exact upper/boxed lower certification and denominator barrier',
        source_scope='same admitted RAW source and original signed-prefix/RH objective',
        supplied_rule='sum_n mu(n) floor(X/n)=1; extract mu(1)=1, squareful zeros, then residual triangle',
        automatic_actions=['choose signed floor coefficients without mu signs',
            'search arbitrary rational scale depths', 'minimize an actual finite upper certificate',
            'certify exact box-capacity gaps', 'derive finite far-correlation uppers',
            'retain all trials and complete-span warnings'],
        next_obligation=dict(expression='sum_(j<head_stop+1) (abs(center_j)+sum_(squarefree n>=2)abs(residual_j(n)))',
            required_rate='O_epsilon(N^(1/2+epsilon)) for every epsilon>0',
            uniformity='all N, all prefixes y, H=floor(sqrtN), both ratio endpoints; constant independent N,y',
            method='learn a scale-dependent rule for horizons AND coefficients, then prove its full center and residual cost',
            alternatives=['signed residual energies or pairings instead of termwise absolute residuals',
                'direct uniform signed far-correlation control from067'],
            dependencies=['complete support', 'unit term', 'coefficient precision', 'dictionary capacity',
                'independent control of any center encoding the target'],
            not_closed_by=['small finite LP gap', 'zero residual with an unpaid target-valued center',
                'a fitted N exponent', 'absence of explicit mu-sign inputs']),
        excluded_family=dict(source='N=15k,y=16k,row1',
            mechanism='rational endpoint quotients with common ideal denominator L=O(N^rho),rho<1/4',
            price_lower='max(0,k/(5772L^2)-floor(sqrt20k)-2), once k>=120L^2',
            implication='fixed rational dictionaries have linear positive price even with current-scale horizon',
            scope='positive proof price only; no signed-row or RH lower bound'),
        rejected_development_rule='prefix truncation would freeze fixed quotient denominators; final rule spreads across full depth',
        capacity_and_precision_are_finite=True, complete_span_requires_separate_center_control=True,
        source_groups=len(results), uniform_head_bound_proved=False,
        uniform_far_correlation_bound_proved=False, uniform_core_bound_proved=False,
        RH_proved=False, research_goal_complete=False)


def aggregate_rss(pids):
    total = 0
    for pid in pids:
        try:
            parts = Path('/proc')/str(pid)/'status'
            for line in parts.read_text().splitlines():
                if line.startswith('VmRSS:'): total += int(line.split()[1])*1024
        except FileNotFoundError:
            pass
    return total


def main():
    if OUT.exists(): raise FileExistsError('preserve every068 attempt')
    started = time.monotonic(); counts = validate_parent()
    frozen = {name: (ROOT/name).read_bytes() for name in FILES}
    receipts = [json.loads(v) for k, v in frozen.items() if k.endswith('_development.json')]
    development = sum(check_receipt(r) for r in receipts)
    if any(r['final_status'] != 'PASS' for r in receipts): raise ValueError('new development gates passed')
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in frozen.items(): (OUT/'source_snapshot'/name).write_bytes(data)
    results, peak_sampled = [], 0
    try:
        write(OUT/'spec.json', dict(spec=SPEC, prior_frozen_counts=counts,
            new_frozen_files=len(FILES), frozen_before_scientific_bound_synthesis=True))
        records = [(p.name, json.loads(p.read_text())) for p in sorted(PRIOR.OUT.glob('lag_*.json'))]
        tasks = group_sources(records)
        if len(records) != 36 or len(tasks) != 12: raise ValueError('all36 sources,12 distinct geometry groups')
        del records
        emit('floor_control_started', source_cases=36, groups=12, workers=SPEC['workers'])
        # Spawn gives each HiGHS instance fresh native state after synthetic tests.
        with mp.get_context('spawn').Pool(SPEC['workers']) as pool:
            iterator = pool.imap_unordered(evaluate_task, tasks, chunksize=1)
            while len(results) < len(tasks):
                if time.monotonic()-started > SPEC['module_seconds']:
                    raise TimeoutError('whole068 module deadline')
                rss = aggregate_rss([os.getpid()]+[p.pid for p in pool._pool])
                peak_sampled = max(peak_sampled, rss)
                if rss > SPEC['maximum_aggregate_bytes']: raise MemoryError('aggregate observed worker RSS')
                try: result = iterator.next(timeout=1)
                except mp.TimeoutError: continue
                write(OUT/('control_'+str(result['N'])+'_'+str(result['y'])+'.json'), result)
                results.append(result)
                emit('floor_control_checked', N=result['N'], y=result['y'], completed=len(results), total=len(tasks),
                    lp_proposals=result['lp_proposals'], fallbacks=result['failed_lp_zero_fallbacks'])
        results.sort(key=lambda r: (r['N'], r['y']))
        cases = [c for r in results for c in r['source_cases']]
        write(OUT/'summary.json', dict(cases=cases, uniform_head_bound_proved=False))
        write(OUT/'mechanism_feedback.json', feedback(results))
        for name, data in frozen.items():
            if (ROOT/name).read_bytes() != data: raise ValueError('preserve frozen068 '+name)
        if validate_parent() != counts: raise ValueError('preserve ancestor source counts')
        parent_peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        worker_peak = max(r['worker_peak_rss_kib'] for r in results)
        peak_sum = 1024*(parent_peak+SPEC['workers']*worker_peak)
        if peak_sum > SPEC['maximum_aggregate_bytes']: raise MemoryError('conservative aggregate process peaks')
        rows = [row for r in results for e in r['certificate']['endpoints'] for row in e['rows']]
        report = dict(status='FINITE_BOUND_SYNTHESIS_VERIFIED_UNIFORM_SIGNED_CONTROL_OPEN',
            source_cases=len(cases), independent_control_certificates=len(results),
            distinct_endpoint_rows=len(rows), distinct_models=sum(r['unique_models'] for r in results),
            total_exponent_plans=sum(len(r['plans']) for r in rows),
            lp_proposals=sum(r['lp_proposals'] for r in results),
            failed_lp_zero_fallbacks=sum(r['failed_lp_zero_fallbacks'] for r in results),
            solver_iterations=sum(r['solver_iterations'] for r in results),
            rows_with_strict_certificate_improvement=sum(Q(chosen(r)['bound'])<Q(chosen(r,0)['bound']) for r in rows),
            selected_complete_span_rows=sum(any(p['model_index']==r['selected_model'] and p['complete_endpoint_quotients'] for p in r['plans']) for r in rows),
            selected_zero_residual_rows=sum(chosen(r)['residual_l1_numerator']==0 for r in rows),
            truncated_exponent_plans=sum(p['dictionary_truncated'] for r in rows for p in r['plans']),
            new_synthetic_tests=sum(r['unique_new_synthetic_tests'] for r in receipts),
            test_invocations=sum(sum(t['tests'] for t in r['runs']) for r in receipts),
            development_operations=development,
            producer_operations=sum(r['producer_operations'] for r in results),
            independent_checker_operations=sum(r['checker_operations'] for r in results),
            operation_count_scope='charged conservative proxies, including LP iterations; not hardware instruction counts',
            elapsed_seconds=time.monotonic()-started, parent_peak_rss_kib=parent_peak,
            largest_worker_peak_rss_kib=worker_peak, conservative_sum_of_process_peaks_bytes=peak_sum,
            sampled_aggregate_rss_peak_bytes=peak_sampled,
            largest_prospective_algorithm_bytes=max(r['prospective_algorithm_bytes'] for r in results),
            workers=SPEC['workers'], native_threads_per_worker=1,
            prior_frozen_counts=counts, new_frozen_source_count=len(FILES),
            learner_mobius_signs_accessed=False, exact_primal_and_boxed_dual_verified=True,
            same_raw_branch_source=True, old_scientific_studies_or_suites_replayed=False,
            hashes_used=False, fresh_holdout_claim=False, uniform_far_correlation_bound_proved=False,
            uniform_head_bound_proved=False, uniform_core_bound_proved=False, RH_proved=False, RH_refuted=False)
        write(OUT/'report.json', report)
        emit('floor_control_complete', status=report['status'], elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json', dict(type=type(exc).__name__, message=str(exc), completed_groups=len(results), RH_proved=False))
        raise


if __name__ == '__main__':
    main()
