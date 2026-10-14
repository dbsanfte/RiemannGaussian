"""Freeze and search source-bound, shared-prime quadratic envelopes."""
import os
for _native_thread_variable in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[_native_thread_variable]='1'

from fractions import Fraction as Q
from math import isqrt
import json
import multiprocessing as mp
import resource
import time

import mobius_quadratic_contraction_064 as SEARCH
import check_mobius_quadratic_source_064 as SOURCE
import check_mobius_quadratic_contraction_064 as CHECK
import run_mobius_prefix_repair_063 as PRIOR
from run_fractional_prime_kernel_051 import write,emit,check_receipt

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'prime_conditioning_followup_001'
FILES=['mobius_quadratic_contraction_064.py','test_mobius_quadratic_contraction_064.py',
       'mobius_quadratic_contraction_search_064_development.json',
       'check_mobius_quadratic_source_064.py','test_check_mobius_quadratic_source_064.py',
       'mobius_quadratic_source_checker_064_development.json','MOBIUS_QUADRATIC_SOURCE_CHECK_SCOPE_064.txt',
       'check_mobius_quadratic_contraction_064.py','test_check_mobius_quadratic_contraction_064.py',
       'mobius_quadratic_contraction_checker_064_development.json','MOBIUS_QUADRATIC_CONTRACTION_CHECK_SCOPE_064.txt',
       'MOBIUS_QUADRATIC_CONTRACTION_REVIEW_064.txt',
       'run_mobius_quadratic_contraction_064.py','mobius_quadratic_contraction_protocol_064.txt']
SPEC={'sources':'all36 saved063 selected factored quadratic repairs',
      'conditioning_rules':['none','registered','all actual primes <=floor(B^xi)'],
      'conditioning_powers':['1/3','2/5','3/7','1/2','4/7','2/3','5/7','3/4','7/8','1'],
      'exponents_are_enumeration_choices_not_a_grammar_whitelist':True,
      'deduplication':'identical literal prime lists, preserving every rule label',
      'diagnostics':['shared all-free-plus-one witness','actual all-free-minus-one replay',
                     'Fourier L2 lower guard','remaining prime degree'],
      'full_conditioning':'finite arithmetic calibration only; never ranked as a uniform solution',
      'new_LP_or_original_source_prefix_evaluation':False,
      'workers':3,'native_threads_per_worker':1,'maximum_aggregate_bytes':16*1024**3,
      'module_seconds':7200,'work_cap_per_meter':300_000_000_000,
      'uniform_growth_claim':False}


def validate_parent():
    counts=PRIOR.validate_parent();directory=PRIOR.OUT/'source_snapshot'
    if sorted(p.name for p in directory.iterdir())!=sorted(PRIOR.FILES):raise ValueError('complete063 snapshot')
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(directory/name).read_bytes():raise ValueError('preserve063 '+name)
    report=json.loads((PRIOR.OUT/'report.json').read_text())
    if report['new_whole_prefix_certificates_verified']!=288 or report['selected_factored_quadratic_replays']!=36:
        raise ValueError('063 complete finite proof archive')
    if report['uniform_core_bound_proved'] or report['RH_proved']:raise ValueError('063 uniform bound remains open')
    return counts+[len(PRIOR.FILES)]


def bind_saved_completion(saved,baseline_saved,meter):
    """Bind saved whole admission to the exact disjoint long/short merge.

    This reuses archived062/063 verdicts; it does not claim a new execution
    of their unchanged whole-source checks. New lift source admission is
    separately required for the same repair before using these budgets.
    """
    chosen=next(c for c in saved['candidates'] if c['rule']==saved['selected_rule'])
    generic=next(c for c in baseline_saved['candidates'] if c['kind']=='generic_indicator_inverse')
    base=generic['certificate'];whole=chosen['completion'];repair=chosen['repair'];lift=saved['selected_quadratic_lift']
    H=lift['H'];ratios=[str(Q(lift['parameters']['p'],lift['parameters']['q'])),'1']
    for key in ('parameters','N','y','H'):
        if whole[key]!=base[key] or base[key]!=lift[key]:raise ValueError('same original source and cutoff')
    if repair['rule']!=lift['rule'] or lift['rule']!=saved['selected_rule'] or repair['H']!=H:
        raise ValueError('same selected linear fill and short repair')
    if any(X<=H for X in base['horizons']):raise ValueError('disjoint strictly long source support')
    if base['ratios']!=ratios or whole['ratios']!=ratios:raise ValueError('same complete affine endpoints')
    if not generic['admitted'] or not generic['verification']['verified'] or not generic['verification']['finite_prefix_bound_proved']:
        raise ValueError('saved062 generic source admission')
    proof=chosen['whole_verification']
    if not proof['verified'] or not proof['finite_prefix_bound_proved'] or not proof['parameter_continuum_proved']:
        raise ValueError('saved063 whole completion admission')
    for key in ('parameters','N','y','H','horizons','ratios','budget'):
        if proof[key]!=whole[key]:raise ValueError('archived whole proof metadata binding')
    if not chosen['repair_verification']['verified'] or chosen['repair_verification']['coefficient_l1']!=repair['coefficient_l1']:
        raise ValueError('archived repair price binding')
    expected_horizons=sorted(set(base['horizons'])|{j for j in range(1,H+1)
        if any(Q(row[j-1]) for row in repair['coefficients'])})
    if whole['horizons']!=expected_horizons:raise ValueError('every source long and new short horizon')
    long_costs=[];whole_costs=[]
    for e in range(2):
        long={X:Q(c) for X,c in zip(base['horizons'],base['coefficients'][e])}
        short={j:Q(c) for j,c in enumerate(repair['coefficients'][e],1)}
        expected=[str(long.get(X,Q(0))+short.get(X,Q(0))) for X in expected_horizons]
        if whole['coefficients'][e]!=expected:raise ValueError('exact long plus short coefficient merge')
        long_cost=sum(map(abs,long.values()),Q(0));short_cost=sum(map(abs,short.values()),Q(0))
        if short_cost!=Q(repair['coefficient_l1'][e]):raise ValueError('complete short price')
        cost=long_cost+short_cost;endpoint=proof['endpoint_costs'][e]
        if endpoint!={'ratio':ratios[e],'coefficient_l1':str(cost),'short_residual_l1':'0','total':str(cost)}:
            raise ValueError('disjoint complete whole endpoint price')
        long_costs.append(long_cost);whole_costs.append(cost);meter.charge(48*len(expected_horizons))
    if str(max(whole_costs))!=whole['budget'] or whole['budget']!=saved['selected_budget'] or whole['budget']!=chosen['new_budget']:
        raise ValueError('selected actual whole budget')
    return chosen,long_costs


def evaluate_task(name):
    started=time.monotonic();saved=json.loads((PRIOR.OUT/name).read_text())
    baseline=json.loads((PRIOR.PRIOR.OUT/saved['source_base_file']).read_text())
    meter=SEARCH.Meter(cap=SPEC['work_cap_per_meter'],seconds=SPEC['module_seconds'])
    sm=SOURCE.Meter(cap=SPEC['work_cap_per_meter'],seconds=SPEC['module_seconds'])
    cm=CHECK.Meter(cap=SPEC['work_cap_per_meter'],seconds=SPEC['module_seconds'])
    lift=saved['selected_quadratic_lift']
    chosen=next(c for c in saved['candidates'] if c['rule']==saved['selected_rule'])
    source=SOURCE.verify_quadratic(lift,chosen['repair'],sm)
    chosen,long_costs=bind_saved_completion(saved,baseline,meter)
    result=SEARCH.discover(lift,meter,powers=SPEC['conditioning_powers'])
    actual=list(map(Q,chosen['repair']['coefficient_l1']));B=max(lift['H'],lift['K'])
    for candidate in result['candidates']:
        cert=candidate['certificate'];checked=CHECK.verify_contraction(lift,cert,cm)
        if candidate['fully_conditioned']!=checked['all_radius_primes_conditioned']:
            raise ValueError('independent full-conditioning classification')
        diagnostics=SEARCH.sign_diagnostics(cert,meter);costs=list(map(Q,checked['endpoint_l1']))
        small_gate=all(p in cert['conditioned_primes'] for p in result['primes_through_query_radius'] if p<=isqrt(B))
        for e,d in enumerate(diagnostics['endpoints']):
            if Q(d['actual_all_free_minus_one_l1'])!=actual[e]:raise ValueError('same actual repair after every conditioning')
            if Q(d['all_free_plus_one_l1'])>costs[e] or Q(d['fourier_l2_squared'])>costs[e]**2:
                raise ValueError('free-sign lower guards cannot exceed proved envelope')
            if costs[e]<actual[e]:raise ValueError('envelope must bound actual repair')
            if candidate['fully_conditioned'] and costs[e]!=actual[e]:raise ValueError('fully conditioned exact endpoint replay')
            if small_gate and d['maximum_remaining_prime_degree']>2:raise ValueError('square-root prime degree gate')
        totals=[a+b for a,b in zip(long_costs,costs)]
        candidate.update({'verification':checked,'diagnostics':diagnostics,
            'all_small_primes_through_sqrtB_conditioned':small_gate,
            'remaining_prime_count':len(result['primes_through_query_radius'])-len(cert['conditioned_primes']),
            'whole_prefix_endpoint_budgets':list(map(str,totals)),
            'whole_prefix_budget':str(max(totals)),
            'composed_fixed_source_prefix_bound_proved':True,'uniform_N_growth_proved':False})
    comparisons=0
    for a in result['candidates']:
        for b in result['candidates']:
            if set(a['certificate']['conditioned_primes'])<set(b['certificate']['conditioned_primes']):
                if any(Q(y)>Q(x) for x,y in zip(a['verification']['endpoint_l1'],b['verification']['endpoint_l1'])):
                    raise ValueError('conditioning must contract every endpoint price')
                comparisons+=1;meter.charge(16)
    result.update({'source_repair_file':name,'source_base_file':saved['source_base_file'],
        'theta':saved['theta'],'rule':saved['selected_rule'],'arithmetic_radius':B,
        'independent_quadratic_source_verification':source,
        'saved_whole_proof_reused_with_exact_merge_binding':True,
        'long_endpoint_l1':list(map(str,long_costs)),'actual_repair_endpoint_l1':list(map(str,actual)),
        'actual_selected_whole_budget':saved['selected_budget'],'old062_LP_budget':saved['old062_selected_budget'],
        'nested_conditioning_comparisons':comparisons,
        'producer_and_composition_operations':meter.operations,'source_checker_operations':sm.operations,
        'contraction_checker_operations':cm.operations,'elapsed_seconds':time.monotonic()-started,
        'prospective_algorithm_bytes':meter.peak_bytes_estimate,
        'worker_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
    return result


def feedback(params,parent):
    return {'schema':'mobius-quadratic-contraction-feedback-v1','source_parameters':params,
        'previous_goal_turn':'063 substantive: analytic repairs and shared quadratic arithmetic target',
        'current_goal_turn':'064 substantive: independent source admission and exact prime-conditioned bound synthesis',
        'parent_target':parent['parent_target'],'conditional_core_recovery':parent['conditional_core_recovery'],
        'bound_construction':{'algebra':'squareful inputs vanish; squarefree mu(m)mu(ell)=mu(m*ell/gcd(m,ell)^2)',
            'coalescing':'linear, quadratic and constant terms combined before absolute values',
            'conditioning':'substitute actual mu(p)=-1 for declared primes, coalesce again, price remaining character coefficients in L1',
            'general_proofs':['source factorization','conditioning contracts coefficient L1',
                'endpoint convexity covers all r in[p/q,1]','primes through sqrt(B) leave degree at most two'],
            'exact_rational_exponents':'any canonical rational in[0,1] within integer bit/work limits; no denominator whitelist',
            'new_machine_admission':'source checker AND independent contraction checker on the same legacy lift',
            'finite_prefix_composition':'reuse saved whole admission only after exact disjoint long/short merge and endpoint price binding'},
        'unpaid_leaf':{'formula':'max_(r=p/q,1) sum_(j,U)|sum_(F:F minus S=U)(-1)^|F intersect S| a_(j,F)(r)|',
            'required_growth':'O_kappa(N^(1/2+kappa)) for every kappa>0, every N and required prefix y',
            'fixed_rule_required':'specify H(N,y), fill P, and conditioning S(N,y)',
            'actual_prime_cutoffs_grow_with_N':True,'uniform_growth_proved':False},
        'obstruction_feedback':{'fixed_finite_conditioning_countermodel':'review proves T*log(T)^2 lower growth only for raw single-indicator repair, not joined W/core fills',
            'growing_conditioning_not_refuted':True,'full_conditioning':'exact finite arithmetic, still owes its all-scale growth theorem',
            'relaxation_diagnostics':'explicit common sign assignments and Fourier L2 guards are lower bounds on any free-sign envelope, not on the actual Mobius source'},
        'next_search_input':{'target':'structured joint norm or paid recurrence for the remaining large-prime quadratic coefficients',
            'candidate_mechanisms':['exact matrix/tensor factorization after small-prime conditioning',
                'cross-row signed pairings or common-sign dual bounds, retaining linear and constant terms',
                'convolution-constrained auxiliary constructions if free-sign guards expose excessive relaxation'],
            'ranking':'proved growth or closed dependencies first; finite envelope improvement and additional conditioning alone are not an exponent discovery'},
        'uniform_quadratic_variation_bound_proved':False,'uniform_core_bound_proved':False,
        'uniform_RH_strength_bound_proved':False,'RH_proved':False,'RH_refuted':False}


def main():
    if OUT.exists():raise FileExistsError('preserve every064 scientific attempt')
    started=time.monotonic();counts=validate_parent()
    parent=json.loads((PRIOR.OUT/'mechanism_feedback.json').read_text());params=parent['source_parameters']
    frozen={name:(ROOT/name).read_bytes() for name in FILES}
    receipts=[json.loads(data) for name,data in frozen.items() if name.endswith('_development.json')]
    development=sum(check_receipt(r) for r in receipts)
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,data in frozen.items():(OUT/'source_snapshot'/name).write_bytes(data)
    results=[]
    try:
        write(OUT/'spec.json',{'spec':SPEC,'parameters':params,'prior_frozen_counts':counts,
            'new_frozen_files':len(FILES),'frozen_before_scientific_contraction_search':True,'hashes_used':False})
        names=sorted(p.name for p in PRIOR.OUT.glob('repair_*.json'))
        if len(names)!=36:raise ValueError('all36 saved063 selected lifts')
        emit('quadratic_contraction_started',cases=len(names),conditioning_requests=2+len(SPEC['conditioning_powers']),workers=SPEC['workers'])
        with mp.get_context('fork').Pool(SPEC['workers']) as pool:
            for result in pool.imap_unordered(evaluate_task,names,chunksize=1):
                name='contraction_'+result['source_repair_file'].removeprefix('repair_')
                write(OUT/name,result);results.append(result)
                emit('quadratic_contraction_checked',N=result['N'],y=result['y'],H=result['H'],
                    rule=result['rule'],envelopes=len(result['candidates']),completed=len(results),total=len(names))
        results.sort(key=lambda r:(r['N'],r['y'],Q(r['theta'])))
        rows=[]
        for result in results:
            for candidate in result['candidates']:
                rows.append({**{k:result[k] for k in ('N','y','H','K','theta','rule','arithmetic_radius')},
                    **{k:candidate[k] for k in ('labels','fully_conditioned','remaining_prime_count',
                        'all_small_primes_through_sqrtB_conditioned','whole_prefix_budget','diagnostics')},
                    'conditioned_prime_count':len(candidate['certificate']['conditioned_primes']),
                    'repair_endpoint_l1':candidate['verification']['endpoint_l1'],
                    'actual_repair_endpoint_l1':result['actual_repair_endpoint_l1'],
                    'actual_selected_whole_budget':result['actual_selected_whole_budget'],
                    'raw_term_l1':result['raw_term_l1'],'unconditioned_l1':result['unconditioned_l1']})
        write(OUT/'summary.json',{'rows':rows,'finite_structural_comparison_only':True,'uniform_growth_proved':False})
        write(OUT/'mechanism_feedback.json',feedback(params,parent))
        validate_parent()
        if any((ROOT/name).read_bytes()!=data for name,data in frozen.items()):raise ValueError('preserve frozen064 sources')
        parent_peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        largest_worker=max(r['worker_peak_rss_kib'] for r in results)
        peak_sum_bound=1024*(parent_peak+SPEC['workers']*largest_worker)
        if peak_sum_bound>SPEC['maximum_aggregate_bytes']:raise MemoryError('conservative sum of process peaks exceeds aggregate budget')
        report={'status':'SOURCE_BOUND_PRIME_CONDITIONED_ENVELOPES_VERIFIED_UNIFORM_GROWTH_OPEN',
            'fixed_N_y_H_cases':len(results),'independent_quadratic_source_admissions':len(results),
            'conditioning_requests_before_deduplication':len(results)*(2+len(SPEC['conditioning_powers'])),
            'exact_contraction_certificates_verified':len(rows),
            'partially_conditioned_envelopes':sum(not r['fully_conditioned'] for r in rows),
            'fully_conditioned_finite_calibrations':sum(r['fully_conditioned'] for r in rows),
            'degree_at_most_two_envelopes':sum(r['all_small_primes_through_sqrtB_conditioned'] for r in rows),
            'nested_endpoint_monotonicity_comparisons':sum(r['nested_conditioning_comparisons'] for r in results),
            'cases_with_strict_unconditioned_coalescing_gain':sum(any(Q(a)<Q(b) for a,b in zip(r['unconditioned_l1'],r['raw_term_l1'])) for r in results),
            'development_operations':development,
            'new_synthetic_tests':sum(r.get('unique_new_synthetic_tests',max(run['tests'] for run in r['runs'])) for r in receipts),
            'recorded_development_test_invocations':sum(sum(run['tests'] for run in r['runs']) for r in receipts),
            'producer_and_composition_operations':sum(r['producer_and_composition_operations'] for r in results),
            'source_checker_operations':sum(r['source_checker_operations'] for r in results),
            'contraction_checker_operations':sum(r['contraction_checker_operations'] for r in results),
            'elapsed_seconds':time.monotonic()-started,'parent_peak_rss_kib':parent_peak,
            'largest_worker_peak_rss_kib':largest_worker,'conservative_sum_of_process_peaks_bytes':peak_sum_bound,
            'largest_prospective_algorithm_bytes':max(r['prospective_algorithm_bytes'] for r in results),
            'largest_checker_prospective_bytes':max(c['verification']['prospective_peak_storage_bytes'] for r in results for c in r['candidates']),
            'workers':SPEC['workers'],'native_threads_per_worker':1,'prior_frozen_counts':counts,
            'new_frozen_source_count':len(FILES),'hashes_used':False,'old_scientific_studies_or_LP_replayed':False,
            'new_full_prefix_source_checks_repeated':False,'original_source_prefix_sums_or_integrals_evaluated':False,
            'new_short_radius_arithmetic_and_symbolic_envelopes_evaluated':True,
            'quadratic_schema_independently_machine_admitted':True,
            'fixed_source_continuum_prefix_bounds_proved_by_composition':True,
            'uniform_quadratic_variation_bound_proved':False,'all_y_bound_proved':False,
            'uniform_core_bound_proved':False,'uniform_RH_strength_bound_proved':False,'RH_proved':False,'RH_refuted':False}
        write(OUT/'report.json',report);emit('quadratic_contraction_complete',status=report['status'],elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',{'type':type(exc).__name__,'message':str(exc),'completed_cases':len(results),
            'elapsed_seconds':time.monotonic()-started,'uniform_core_bound_proved':False,'RH_proved':False})
        raise


if __name__=='__main__':main()
