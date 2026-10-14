"""Frozen mixed-scale signed recurrence search on every admitted068 head."""
import os
for _thread_variable in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_thread_variable] = '1'

from fractions import Fraction as Q
import json
import multiprocessing as mp
import resource
import time

import mobius_convolution_scale_069 as SEARCH
import check_mobius_convolution_scale_069 as CHECK
import run_mobius_floor_control_068 as PRIOR
from run_fractional_prime_kernel_051 import write, emit, check_receipt

ROOT = PRIOR.ROOT
OUT = PRIOR.OUT/'convolution_scale_followup_001'
FILES = ['mobius_convolution_scale_069.py', 'test_mobius_convolution_scale_069.py',
    'mobius_convolution_scale_search_069_development.json', 'check_mobius_convolution_scale_069.py',
    'test_check_mobius_convolution_scale_069.py', 'mobius_convolution_scale_checker_069_development.json',
    'MOBIUS_CONVOLUTION_SCALE_CHECK_SCOPE_069.txt', 'MOBIUS_CONVOLUTION_SCALE_REVIEW_069.txt',
    'run_mobius_convolution_scale_069.py', 'mobius_convolution_scale_protocol_069.txt']
SPEC = dict(source_groups='all12 completed068 groups; same36 admitted raw heads',
    requests=SEARCH.DEFAULT_REQUESTS, price_exponents=SEARCH.DEFAULT_PRICE_EXPONENTS,
    learned_coefficients='exact sparse affine solve of unit normalization and all multilinear face vanishings',
    support_gate='product_i(floor(R^theta_i)+1)>R; every cut<R except unit base R1',
    learner_mobius_signs_or_target_values=False,
    cost='complete signed polynomial in smaller ordinary M prefixes; separate conditional degree price',
    selection='first sigma C1 conditional price, query radius, monomial count, stable model order',
    archive='all models and a Pareto view of query radius versus conditional price',
    fake_witness='M1=1,Ms=0 for s>=2; formal scalar envelope only, not ordinary mu',
    degree_one_theorem='equal k cuts cost O_k(N^(1/2+1/(2k))) on square-root head',
    initial_prefix_premise='unpaid uniformly; finite C1 premise audited separately',
    workers=3, native_threads_per_worker=1, maximum_aggregate_bytes=16*1024**3,
    work_cap_per_case_meter=300_000_000_000, module_seconds=7200,
    fresh_holdout_claim=False, hashes_used=False, uniform_full_head_bound_claim=False)


def validate_parent():
    counts = PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve068 '+name)
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if (report['independent_control_certificates'] != 12 or report['source_cases'] != 36
            or not report['exact_primal_and_boxed_dual_verified'] or report['RH_proved']):
        raise ValueError('completed068 and open uniform arithmetic cost')
    return counts+[len(PRIOR.FILES)]


def bind_floor(saved):
    cert, verdict = saved['certificate'], saved['verification']
    if (not verdict['verified'] or not saved['original_source_binding_proved']
            or saved['RH_proved'] or saved['uniform_head_bound_proved']
            or verdict['uniform_head_bound_proved']):
        raise ValueError('same admitted068 raw head, uniform cost open')
    for field in ('N', 'y', 'max_j'):
        if saved[field] != cert[field] or verdict[field] != cert[field]:
            raise ValueError('same admitted source coordinates')
    if cert['parameters'] != verdict['parameters'] or len(cert['endpoints']) != 2:
        raise ValueError('same registered source and both ratios')
    return cert


def price(model, index=0):
    return sum(map(Q, model['conditional_prices'][index]['coefficients']))


def summarize(saved, cert, verdict, meter=None):
    meter = SEARCH.Meter() if meter is None else meter
    old = saved['certificate']; previous = saved['verification']
    for e, v, before in zip(cert['endpoints'], verdict['endpoints'], previous['endpoints']):
        if e['ratio'] != v['ratio'] or e['ratio'] != before['ratio']:
            raise ValueError('source ratio order')
        if ([row['actual_coefficient'] for row in v['rows']] !=
                [row['actual_coefficient'] for row in before['rows']]):
            raise ValueError('every newly compiled polynomial binds to admitted source')
    cases = []
    for prior_case in saved['source_cases']:
        H = prior_case['H']; stop = (H+1)//2-1
        if any(prior_case[k] != cert[k] for k in ('N', 'y')) or H != SEARCH.power(cert['N'], prior_case['theta'], meter):
            raise ValueError('exact declared H power and same source case')
        endpoints = []
        for endpoint, checked, old_endpoint, prior_summary in zip(cert['endpoints'], verdict['endpoints'],
                old['endpoints'], prior_case['endpoints']):
            rows = endpoint['rows'][:stop]; checks = checked['rows'][:stop]
            plans = []
            for plan_index, request in enumerate(cert['requests']):
                pairs = [(row['models'][row['plans'][plan_index]['model_index']],
                          check['models'][row['plans'][plan_index]['model_index']]) for row, check in zip(rows, checks)]
                plans.append(dict(exponents=request, degree=len(request),
                    maximum_mu_argument=max((m['mu_query_radius'] for m, _ in pairs), default=1),
                    polynomial_terms=sum(len(m['terms']) for m, _ in pairs),
                    scalar_box_witness_absolute_head=str(sum((abs(Q(m['scalar_box_witness']['value'])) for m, _ in pairs), Q(0))),
                    conditional_C1_head_prices=[str(sum((price(m, s) for m, _ in pairs), Q(0)))
                                               for s in range(len(cert['price_exponents']))],
                    finite_C1_premises=[all(v['finite_C1_prefix_premise'][s] for _, v in pairs)
                                        for s in range(len(cert['price_exponents']))],
                    unconditional_degree_one_head_upper=str(4*sum(sum(m['cutoffs']) for m, _ in pairs)),
                    uniform_degree_one_head_exponent=str(Q(prior_case['theta'])+
                        (1-Q(prior_case['theta']))*max(map(Q, request))),
                    uniform_higher_degree_bound_proved=False))
            # Query radius is a resource/exposure dimension, not a growth exponent.
            frontier = [i for i, a in enumerate(plans) if not any(
                b['maximum_mu_argument'] <= a['maximum_mu_argument'] and
                Q(b['conditional_C1_head_prices'][0]) <= Q(a['conditional_C1_head_prices'][0]) and
                (b['maximum_mu_argument'] < a['maximum_mu_argument'] or
                 Q(b['conditional_C1_head_prices'][0]) < Q(a['conditional_C1_head_prices'][0])) for b in plans)]
            selected = [r['models'][r['selected_model']] for r in rows]
            finite = [all(v['models'][r['selected_model']]['finite_C1_prefix_premise'][s] for r, v in zip(rows, checks))
                      for s in range(len(cert['price_exponents']))]
            upper = [sum((price(m, s) for m in selected), Q(0)) for s in range(len(cert['price_exponents']))]
            actual = sum((abs(Q(v['actual_coefficient'])) for v in checks), Q(0))
            if any(paid and actual > u for paid, u in zip(finite, upper)):
                raise ArithmeticError('finite conditional signed head price')
            if actual != Q(prior_summary['actual_head_variation']): raise ValueError('same original H cut')
            endpoints.append(dict(ratio=endpoint['ratio'], head_stop=stop, actual_head_variation=str(actual),
                prior068_certified_head_upper=prior_summary['selected_head_upper'],
                selected_conditional_C1_head_prices=list(map(str, upper)), finite_C1_premises=finite,
                selected_maximum_mu_argument=max((m['mu_query_radius'] for m in selected), default=1),
                original_row1_mu_radius=4*cert['N']//cert['parameters']['p'],
                all_plans=plans, pareto_plan_indices=frontier, uniform_head_bound_proved=False))
        cases.append(dict(N=cert['N'], y=cert['y'], H=H, theta=prior_case['theta'], endpoints=endpoints))
    return cases


def evaluate_task(name):
    started = time.monotonic(); saved = json.loads((PRIOR.OUT/name).read_text()); source = bind_floor(saved)
    meter = SEARCH.Meter(cap=SPEC['work_cap_per_case_meter'], seconds=SPEC['module_seconds'])
    cm = CHECK.Meter(cap=SPEC['work_cap_per_case_meter'], seconds=SPEC['module_seconds'])
    cert = SEARCH.construct(source['N'], source['y'], source['max_j'], source['parameters'],
        SPEC['requests'], SPEC['price_exponents'], meter)
    verdict = CHECK.verify_control(cert, cm)
    cases = summarize(saved, cert, verdict, meter)
    models = [m for e in cert['endpoints'] for r in e['rows'] for m in r['models']]
    return dict(source_floor_file=name, N=source['N'], y=source['y'], max_j=source['max_j'],
        certificate=cert, verification=verdict, original_source_binding_proved=True, source_cases=cases,
        distinct_models=len(models), signed_polynomial_terms=sum(len(m['terms']) for m in models),
        producer_operations=meter.operations, checker_operations=cm.operations,
        prospective_algorithm_bytes=meter.peak_bytes_estimate,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        elapsed_seconds=time.monotonic()-started, uniform_head_bound_proved=False, RH_proved=False)


def feedback(results):
    return dict(schema='mobius-convolution-scale-feedback-v1',
        previous_goal_turn='068 substantive: actual bound synthesis and exact boxed capacity audit',
        current_goal_turn='069 learned support-annihilating laws, exact smaller-scale signed prefix polynomials and scalar-domain exclusion',
        automatic_actions=['solve universal face coefficient constraints', 'compile exact rational cutoff support gates',
            'retain complete signed ordinary-prefix polynomial', 'derive conditional cost polynomial in C',
            'expose formal scalar-envelope countermodels', 'retain radius/cost Pareto candidates'],
        supplied_mathematics=['Dirichlet convolution and mu*One=delta', 'support product rule',
            'multivariate finite summation by parts', 'conditional scalar envelope and exact power enclosure'],
        paid_partial_rule='degree-one head for equal k cuts is O_k(N^(1/2+1/(2k))); direct floor mass<=12',
        main_unpaid_leaf='complete joined degree>=2 arithmetic interaction, with all constant/lower-degree cancellations retained',
        next_obligation=dict(priority='arithmetic constraints or coupled energies that distinguish actual smaller-scale mu from scalar-envelope countermodels',
            target='uniform signed value of the exact prefix polynomial, summed over raw head, Oepsilon(N^(1/2+epsilon))',
            uniformity='every N,y, H=floor(sqrtN), both ratio endpoints; every epsilon>0',
            induction_requirements=['strict smaller argument or a licensed unit base', 'source and all auxiliary states reproduced',
                'base cases and full coefficient/precision cost', 'one invariant constant including C^degree terms',
                'no assumption of the desired all-scale Mertens bound'],
            promising_new_inputs=['actual prime constraints growing with scale', 'complete local divisor relations',
                'signed coupled moment or storage inequalities instead of separate prefix envelopes'],
            rejected_shortcuts=['repeating the068 finite LP optimum', 'scalar-prefix-only norm recurrence in the reviewed fixed positive-cutoff families',
                'fixed finite prime conditioning claimed to supply all-scale arithmetic', 'smaller sign-query radius claimed as a growth bound']),
        scalar_box_obstruction=dict(source='N15k,y16k,j1,r1', degree=2,
            fake_prefix='M1=1; Ms=0 for s>=2', fake_value='ceil(k/2) when both cuts>=2',
            exact_actual_mu=False, scope='complete scalar-box range, not just separate triangle pricing; not RH refutation'),
        finite_prime_extension='fixed finite P, cuts>=prodP: fake d2 value 2k*prod_(p in P)(1-1/p)^2+O_P(1); only when envelope admits that fake',
        growing_degree_or_prime_sets_excluded=False, observed_groups=len(results),
        conditional_prefix_bounds_paid=False, uniform_head_bound_proved=False,
        uniform_far_correlation_bound_proved=False, uniform_core_bound_proved=False,
        RH_proved=False, research_goal_complete=False)


def main():
    if OUT.exists(): raise FileExistsError('preserve every069 attempt')
    started = time.monotonic(); counts = validate_parent()
    frozen = {name: (ROOT/name).read_bytes() for name in FILES}
    receipts = [json.loads(value) for name, value in frozen.items() if name.endswith('_development.json')]
    development = sum(check_receipt(r) for r in receipts)
    if any(r['final_status'] != 'PASS' for r in receipts): raise ValueError('new synthetic gates passed')
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in frozen.items(): (OUT/'source_snapshot'/name).write_bytes(data)
    results, sampled_peak = [], 0
    try:
        write(OUT/'spec.json', dict(spec=SPEC, prior_frozen_counts=counts, new_frozen_files=len(FILES),
            frozen_before_new_scientific_polynomial_evaluation=True))
        names = sorted(p.name for p in PRIOR.OUT.glob('control_*.json'))
        if len(names) != 12: raise ValueError('all12 completed068 groups')
        emit('convolution_scale_started', groups=len(names), workers=SPEC['workers'], requests=len(SPEC['requests']))
        with mp.get_context('spawn').Pool(SPEC['workers']) as pool:
            iterator = pool.imap_unordered(evaluate_task, names, chunksize=1)
            while len(results) < len(names):
                if time.monotonic()-started > SPEC['module_seconds']: raise TimeoutError('whole069 module deadline')
                rss = PRIOR.aggregate_rss([os.getpid()]+[p.pid for p in pool._pool]); sampled_peak = max(sampled_peak, rss)
                if rss > SPEC['maximum_aggregate_bytes']: raise MemoryError('aggregate observed worker RSS')
                try: result = iterator.next(timeout=1)
                except mp.TimeoutError: continue
                write(OUT/result['source_floor_file'].replace('control_', 'convolution_', 1), result); results.append(result)
                emit('convolution_scale_checked', N=result['N'], y=result['y'], completed=len(results), total=len(names),
                    models=result['distinct_models'], polynomial_terms=result['signed_polynomial_terms'])
        results.sort(key=lambda r: (r['N'], r['y'])); cases = [case for r in results for case in r['source_cases']]
        write(OUT/'summary.json', dict(cases=cases, conditional_prefix_bounds_paid=False, uniform_head_bound_proved=False))
        write(OUT/'mechanism_feedback.json', feedback(results))
        for name, data in frozen.items():
            if (ROOT/name).read_bytes() != data: raise ValueError('preserve frozen069 '+name)
        if validate_parent() != counts: raise ValueError('preserve ancestor source chain')
        parent_peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        worker_peak = max(r['worker_peak_rss_kib'] for r in results)
        peak_sum = 1024*(parent_peak+SPEC['workers']*worker_peak)
        if peak_sum > SPEC['maximum_aggregate_bytes']: raise MemoryError('conservative aggregate process peaks')
        rows = [row for r in results for e in r['certificate']['endpoints'] for row in e['rows']]
        models = [m for row in rows for m in row['models']]
        checked_models = [m for r in results for e in r['verification']['endpoints'] for row in e['rows'] for m in row['models']]
        report = dict(status='EXACT_SMALLER_SCALE_RECURRENCES_VERIFIED_SCALAR_PRICING_OBSTRUCTED_ARITHMETIC_COST_OPEN',
            source_cases=len(cases), independent_convolution_certificates=len(results), distinct_endpoint_rows=len(rows),
            learned_annihilator_degrees=sorted({len(v) for v in SPEC['requests']}),
            distinct_models=len(models), exponent_plans=sum(len(row['plans']) for row in rows),
            signed_polynomial_terms=sum(len(m['terms']) for m in models),
            formal_zero_variable_witness_nonzero_models=sum(m['constant_scaled']!=0 for m in models),
            constant_only_models=sum(not m['terms'] for m in models),
            all_C1_prefix_premises_hold=sum(all(m['finite_C1_prefix_premise']) for m in checked_models),
            new_synthetic_tests=sum(r['unique_new_synthetic_tests'] for r in receipts),
            test_invocations=sum(sum(t['tests'] for t in r['runs']) for r in receipts),
            development_operations=development, producer_operations=sum(r['producer_operations'] for r in results),
            independent_checker_operations=sum(r['checker_operations'] for r in results),
            elapsed_seconds=time.monotonic()-started, parent_peak_rss_kib=parent_peak,
            largest_worker_peak_rss_kib=worker_peak, sampled_aggregate_rss_peak_bytes=sampled_peak,
            conservative_sum_of_process_peaks_bytes=peak_sum,
            largest_prospective_algorithm_bytes=max(r['prospective_algorithm_bytes'] for r in results),
            workers=SPEC['workers'], native_threads_per_worker=1,
            prior_frozen_counts=counts, new_frozen_source_count=len(FILES),
            same_raw_branch_source=True, learner_mobius_signs_accessed=False,
            universal_convolution_identity_proved=True, uniform_degree_one_partial_bound_proved=True,
            unit_base_exception_R1=True, conditional_prefix_bounds_paid=False,
            old_scientific_studies_or_suites_replayed=False, hashes_used=False, fresh_holdout_claim=False,
            uniform_head_bound_proved=False, uniform_far_correlation_bound_proved=False,
            uniform_core_bound_proved=False, RH_proved=False, RH_refuted=False)
        write(OUT/'report.json', report)
        emit('convolution_scale_complete', status=report['status'], elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json', dict(type=type(exc).__name__, message=str(exc), completed_groups=len(results), RH_proved=False))
        raise


if __name__ == '__main__': main()
