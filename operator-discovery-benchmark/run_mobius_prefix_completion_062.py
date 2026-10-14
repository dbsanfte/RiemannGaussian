"""Frozen geometry-only construction search for the unpaid061 prefix."""
import os
for _native_thread_variable in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[_native_thread_variable]='1'

from fractions import Fraction as Q
import json
import multiprocessing as mp
import resource
import time

import mobius_prefix_completion_062 as SEARCH
import check_mobius_prefix_completion_062 as CHECK
import run_mobius_fractional_flow_061 as PRIOR
from mobius_transport_search_059 import floor_power
from run_fractional_prime_kernel_051 import write,emit,check_receipt

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'prefix_completion_followup_001'
FILES=['mobius_prefix_completion_062.py','test_mobius_prefix_completion_062.py',
       'mobius_prefix_completion_search_062_development.json',
       'check_mobius_prefix_completion_062.py','test_check_mobius_prefix_completion_062.py',
       'mobius_prefix_completion_checker_062_development.json','MOBIUS_PREFIX_COMPLETION_CHECK_SCOPE_062.txt',
       'MOBIUS_PREFIX_COMPLETION_REVIEW_062.txt',
       'run_mobius_prefix_completion_062.py','mobius_prefix_completion_protocol_062.txt']
SPEC={'scales':[256,1024,4096,7249],'prefix_fractions_of_D':['1/3','1/2','2/3'],
      'short_cutoff_powers':['3/7','1/2','4/7'],
      'constructions':['generic_indicator_inverse','joint_lp','joint_lp_zero_moment'],
      'ratio_endpoints':'[p/q,1], affine coefficients between endpoints',
      'lp_max_seconds_per_endpoint':120,'rationalization_max_denominator':1_000_000,
      'workers':3,'native_threads_per_worker':1,'maximum_aggregate_bytes':16*1024**3,
      'actual_source_mu_signs_or_prefix_values_used':False,
      'finite_exponent_fit_or_uniform_growth_claim':False}


def validate_parent():
    counts=PRIOR.validate_parent();directory=PRIOR.OUT/'source_snapshot'
    if sorted(p.name for p in directory.iterdir())!=sorted(PRIOR.FILES):raise ValueError('complete061 snapshot')
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(directory/name).read_bytes():raise ValueError('preserve061 '+name)
    report=json.loads((PRIOR.OUT/'report.json').read_text())
    if not report['head_bound_proved'] or not report['exit_residual_bound_proved'] or report['uniform_core_bound_proved'] or report['RH_proved']:
        raise ValueError('061 paid regions and unpaid joined interior binding')
    return counts+[len(PRIOR.FILES)]


def evaluate_task(task):
    N,y,theta,params=task;started=time.monotonic()
    meter=SEARCH.Meter(cap=300_000_000_000,seconds=7200)
    cm=CHECK.Meter(cap=300_000_000_000,seconds=7200)
    H=max(1,floor_power(N,theta,meter))
    result=SEARCH.search_one(N,y,H,params,meter)
    for candidate in result['candidates']:
        if candidate['admitted']:
            candidate['verification']=CHECK.verify_completion(candidate['certificate'],cm)
    result.update({'theta':theta,'producer_operations':meter.operations,
        'checker_operations':cm.operations,'elapsed_seconds':time.monotonic()-started,
        'worker_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'prospective_algorithm_bytes':meter.peak_bytes_estimate})
    return result


def feedback(params,parent):
    return {'schema':'mobius-prefix-completion-feedback-v1','source_parameters':params,
        'previous_goal_turn':'061 substantive: fractional source transport and paid uniform head/exit regions',
        'current_goal_turn':'062 substantive: automated complete-floor coefficient search and independent exact continuum bounds at fixed N,y',
        'target':parent['core'],
        'construction':'f_d(r)=1[d<=y]*(W(N/(p*d))-r*W(N/(q*d))); reconstruct with sum_j c_j(r)*floor(X_j/d) for all coprime d>H; price every short residual',
        'finite_theorem':'|S_N(y,t)|<=U(N,y,H)*(1+log2(4N))^k for every real0<t<1; coefficient vectors interpolate affinely overr=(p/q)^t in[p/q,1]',
        'source_arithmetic_rule':'sum_d mu_M(d)*floor(X/d)=Psi_M(X), complete horizon and unit retained',
        'budget':'max_(r=p/q,1) [sum_j|c_j(r)|+sum_(d<=H,gcd(d,R)=1)|f_d(r)-sum_j c_j(r)*floor(X_j/d)|]',
        'conditional_core_recovery':{'premise':'U(N,y,H)<=U(N) for EVERY required integer y and EVERY N>=2, allowing a construction and H depending on N,y',
            'conclusion':'C_core(N)<=3R/(k+1-alpha)*U(N)*(1+log2(4N))^(k+1)',
            'required_budget_growth':'U(N)=O_kappa(N^(1/2+kappa)) for every rational kappa>0',
            'premise_proved':False,'conditional_rule_machine_admitted':False},
        'reviewed_generic_progress':{'indicator_primitive':'1[d<=T]=sum_(ell<=floor(T/(H+1))) mu(ell)*floor(T/(ell*d)), only for d>H',
            'ordinary_inverse_mu_not_masked':True,
            'coefficient_rate':'O(N/H * (1+log(4N/H))) before endpoint channel joining',
            'sqrt_cutoff':'H=floor(sqrtN) makes the complete-convolution contribution O(sqrtN*(1+log2(4N))^(k+1))',
            'short_residual_bound_paid':False,'source_only_analytical_review':True},
        'next_search_input':{'target':'a uniform complete budget bound, especially the exact signed short residual after moving-floor reconstruction',
            'formula':'R_d(r)=f_d(r)-sum_j c_j(r)*floor(X_j/d), d<=H; retain mu_M(d)*R_d(r) jointly before any replacement by its L1 budget',
            'candidate_mechanisms':['recursive signed residual completions with strictly decreasing dependency scale and paid boundary terms',
                'coefficient families with provable first-moment and higher cancellation plus bounded total variation',
                'bilinear inverse/source Mobius correlations with all diagonal and current-scale terms retained'],
            'no_free_short_sum':'H terms do not imply O(H) when residual amplitudes grow',
            'no_free_zero_moment':'sum c_j*X_j=0 only gives |completion(d)|<=sum|c_j|, hence residual L1<=H*(2+sum|c_j|)',
            'no_finite_to_uniform_inference':True,'no_assumed_Mertens_or_RH':True},
        'finite_certificates_are_new_provable_bounds':True,
        'finite_optimality_of_LP_not_proved':True,'all_y_coverage_proved':False,
        'uniform_budget_growth_proved':False,'uniform_core_bound_proved':False,
        'uniform_RH_strength_bound_proved':False,'uniform_full_source_bound_proved':False,
        'RH_proved':False,'RH_refuted':False}


def main():
    if OUT.exists():raise FileExistsError('preserve every062 attempt')
    started=time.monotonic();counts=validate_parent()
    parent=json.loads((PRIOR.OUT/'mechanism_feedback.json').read_text());params=parent['source_parameters']
    frozen={name:(ROOT/name).read_bytes() for name in FILES}
    development=sum(check_receipt(json.loads(data)) for name,data in frozen.items() if name.endswith('_development.json'))
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,data in frozen.items():(OUT/'source_snapshot'/name).write_bytes(data)
    results=[]
    try:
        write(OUT/'spec.json',{'spec':SPEC,'parameters':params,'prior_frozen_counts':counts,
            'new_frozen_files':len(FILES),'frozen_before_new_scientific_completion_search':True,'hashes_used':False})
        tasks=[]
        for N in SPEC['scales']:
            D=4*N//params['p']
            for fraction in SPEC['prefix_fractions_of_D']:
                v=Q(fraction);y=D*v.numerator//v.denominator
                for theta in SPEC['short_cutoff_powers']:tasks.append((N,y,theta,params))
        emit('prefix_completion_started',cases=len(tasks),workers=SPEC['workers'])
        with mp.get_context('fork').Pool(SPEC['workers']) as pool:
            for result in pool.imap_unordered(evaluate_task,tasks,chunksize=1):
                name='completion_'+str(result['N'])+'_'+str(result['y'])+'_'+result['theta'].replace('/','_')+'.json'
                write(OUT/name,result);results.append(result)
                emit('prefix_completion_checked',N=result['N'],y=result['y'],H=result['H'],
                    selected=result['selected_kind'],budget=result['selected_budget'],
                    completed=len(results),total=len(tasks))
        results.sort(key=lambda r:(r['N'],r['y'],Q(r['theta'])))
        rows=[]
        for result in results:
            for candidate in result['candidates']:
                row={'N':result['N'],'y':result['y'],'H':result['H'],'theta':result['theta'],
                     'kind':candidate['kind'],'admitted':candidate['admitted']}
                if candidate['admitted']:
                    verdict=candidate['verification'];row.update({'budget':verdict['budget'],
                        'horizons':len(candidate['certificate']['horizons']),
                        'endpoint_costs':verdict['endpoint_costs'],
                        'budget_over_sqrtN_float':float(Q(verdict['budget']))/(result['N']**0.5)})
                else:row['reason']=candidate['reason']
                rows.append(row)
        write(OUT/'summary.json',{'rows':rows,'descriptive_scaling_only':True,'all_y_or_uniform_N_claim':False})
        write(OUT/'mechanism_feedback.json',feedback(params,parent))
        validate_parent()
        if any((ROOT/name).read_bytes()!=data for name,data in frozen.items()):raise ValueError('preserve frozen062 sources')
        admitted=sum(row['admitted'] for row in rows)
        report={'status':'EXACT_FINITE_JOINT_PREFIX_CONTROLS_DISCOVERED_UNIFORM_BUDGET_OPEN',
            'scales':SPEC['scales'],'fixed_N_y_H_cases':len(results),'construction_candidates':len(rows),
            'exact_certificates_independently_verified':admitted,'rejected_proposals':len(rows)-admitted,
            'new_synthetic_tests':28,'development_operations':development,
            'producer_operations':sum(r['producer_operations'] for r in results),
            'independent_checker_operations':sum(r['checker_operations'] for r in results),
            'elapsed_seconds':time.monotonic()-started,
            'parent_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'largest_worker_peak_rss_kib':max(r['worker_peak_rss_kib'] for r in results),
            'largest_prospective_algorithm_bytes':max(r['prospective_algorithm_bytes'] for r in results),
            'workers':SPEC['workers'],'native_threads_per_worker':1,'prior_frozen_counts':counts,
            'new_frozen_source_count':len(FILES),'hashes_used':False,'old_suites_or_studies_replayed':False,
            'actual_source_mu_signs_or_prefix_values_used':False,'finite_LP_optimality_proved':False,
            'parameter_continuum_prefix_bounds_proved':True,'all_y_bound_proved':False,
            'uniform_budget_growth_proved':False,'uniform_core_bound_proved':False,
            'uniform_RH_strength_bound_proved':False,'uniform_full_source_bound_proved':False,
            'RH_proved':False,'RH_refuted':False}
        write(OUT/'report.json',report)
        emit('prefix_completion_complete',status=report['status'],elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',{'type':type(exc).__name__,'message':str(exc),
            'completed_cases':len(results),'elapsed_seconds':time.monotonic()-started,
            'uniform_core_bound_proved':False,'RH_proved':False})
        raise


if __name__=='__main__':main()
