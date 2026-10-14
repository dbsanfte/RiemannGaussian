"""Frozen inference, proof and new joint-prefix flow diagnostics for061."""
import os
for _native_thread_variable in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[_native_thread_variable]='1'

from fractions import Fraction as Q
import json
import multiprocessing as mp
import resource
import time

import mobius_fractional_flow_061 as SEARCH
import check_mobius_fractional_flow_061 as CHECK
import run_mobius_mass_conservation_060 as PRIOR
from mobius_mass_conservation_060 import exact_smooth_mass
from mobius_transport_search_059 import source_kernel_expressions
from run_fractional_prime_kernel_051 import write,emit,check_receipt

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'fractional_flow_followup_001'
FILES=['mobius_fractional_flow_061.py','test_mobius_fractional_flow_061.py',
       'mobius_fractional_flow_search_061_development.json',
       'check_mobius_fractional_flow_061.py','test_check_mobius_fractional_flow_061.py',
       'mobius_fractional_flow_checker_061_development.json','MOBIUS_FRACTIONAL_FLOW_CHECK_SCOPE_061.txt',
       'MOBIUS_FRACTIONAL_FLOW_REVIEW_061.txt',
       'run_mobius_fractional_flow_061.py','mobius_fractional_flow_protocol_061.txt']
SPEC={'cutoff_max_denominator':12,'extra_rational_cutoffs':['1/257','2/11','3/11'],
      'target_component_power':'1/2','quadrature_degree_per_root_cell':16,
      'workers':3,'native_threads_per_worker':1,'maximum_aggregate_bytes':16*1024**3,
      'source_values_used_for_selection':False,'finite_growth_claims_tested':False}


def validate_parent():
    counts=PRIOR.validate_parent();directory=PRIOR.OUT/'source_snapshot'
    if sorted(p.name for p in directory.iterdir())!=sorted(PRIOR.FILES):raise ValueError('complete060 snapshot')
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(directory/name).read_bytes():raise ValueError('preserve060 '+name)
    report=json.loads((PRIOR.OUT/'report.json').read_text())
    if not report['uniform_final_copy_leftover_bound_proved'] or report['uniform_full_source_bound_proved'] or report['RH_proved']:
        raise ValueError('060 paid component and open full source binding')
    return counts+[len(PRIOR.FILES)]


def evaluate_task(payload):
    N,cert=payload;params=cert['parameters']
    meter=SEARCH.Meter(cap=300_000_000_000,seconds=7200)
    saved=json.loads((PRIOR.PRIOR.OUT/('final_'+str(N)+'.json')).read_text())
    tokens=saved['independent']['tokens'];old_source=saved['source']
    if old_source['request']!={'N':N,**params}:raise ValueError('saved source parameter binding')
    fields=('d','profile','sign','kernel_sign','mu')
    if [{k:t[k] for k in fields} for t in old_source['tokens']]!=tokens:
        raise ValueError('saved independent token metadata')
    result=SEARCH.evaluate_saved_tokens(N,params,cert['kernels'],tokens,cert['head_theta'],cert['exit_rho'],
        SPEC['quadrature_degree_per_root_cell'],meter)
    # Independently replay every prefix from the two original integer floors.
    # This reuses independently checked ordinary-mu metadata; no sieve is run.
    total=[0,0]
    for token,row in zip(tokens,result['prefix_table']['rows']):
        if token['d']!=row['d']:raise ValueError('complete increasing cofactor prefixes')
        for j,base in enumerate((params['p'],params['q'])):
            divisor=base*token['d']
            W=(4*N)//divisor-3*((2*N)//divisor)+2*(N//divisor)
            total[j]+=token['mu']*W*(1 if j==0 else -1)
        if total!=row['coefficients']:raise ValueError('direct joint arithmetic prefix agreement')
        meter.charge(64)
    if len(tokens)!=len(result['prefix_table']['rows']):raise ValueError('every token prefix retained')
    smooth=[exact_smooth_mass(c['identity'],N,meter) for c in cert['columns']]
    if smooth!=list(map(Q,total)):raise ValueError('complete terminal columns equal exact smooth counts')
    result['exact_prefix_and_terminal_audit']={'verified':True,'prefixes':len(tokens),
        'terminal_columns':[str(x) for x in smooth],'new_mu_sieve_evaluated':False}
    result['saved_source_signed_sum_float']=old_source['signed_sum']
    result['saved_source_absolute_sum_float']=old_source['absolute_sum']
    result['floating_triangle_consistent']=(abs(old_source['signed_sum'])<=result['total_float']+1e-10
        and result['total_float']<=old_source['absolute_sum']+1e-10)
    if not result['floating_triangle_consistent']:raise ArithmeticError('descriptive quadrature consistency failed')
    result['floating_consistency_is_not_an_interval_certificate']=True
    result['operations']=meter.operations
    result['prospective_algorithm_bytes']=meter.peak_bytes_estimate
    result['worker_peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return result


def mechanism_feedback(cert,verification,parent):
    return {'schema':'mobius-fractional-flow-feedback-v1','source_parameters':cert['parameters'],
        'previous_goal_turn':'060 substantive: inferred conservation and uniform final-copy-leftover bounds',
        'current_goal_turn':'061 substantive: parameterized fractional transport, exact exponent selection, and uniform cofactor head/exit bounds',
        'source':'same058 joined ordinary-mu middle; unit, every actual prime factor, floor signs and unequal exits retained',
        'construction':'positive profile masses h_i(t) inferred from source kernel columns; common decreasing carrier d^-t',
        'certificate':cert,'independent_verification':verification,
        'recovery':'|J(N)|<=C_core(N)+head_C*N^theta+exit_C*N^(2*rho-1)+endpoint_C*(1+log2(4N))^k',
        'core':{'definition':'rgamma(1-alpha)*integral_eps^tau G_M(t)*t^(-alpha)*integral_a^b |p^-t*A_N(y)-q^-t*B_N(y)|*y^(-t-1) dy dt',
            'A_N(y)':'sum_(d<=y,gcd(d,M)=1) mu(d)*W(N/(p*d))',
            'B_N(y)':'sum_(d<=y,gcd(d,M)=1) mu(d)*W(N/(q*d))',
            'D':'max(1,floor(4*N/p))','a':'min(N^theta,D)',
            'K':'min(floor(D/2),floor(N^rho))','b':'max(a,D-K)',
            'required_estimate':'for every rational kappa>0, C_core(N)<=C_kappa*N^(1/2+kappa), every integer N>=2',
            'status':'OPEN','proved':False},
        'obligation_graph':{'paid':['exact common-carrier source identity','fractional flow/prefix upper formula',
            'square-root head','square-root integer exit residual','polylog smooth exit plus terminal'],
            'unpaid':['uniform joined interior prefix estimate'],
            'paid_endpoint_and_RH_bridge_binding':parent['obligation_graph']['paid_endpoint_and_RH_bridge_binding'],
            'one_remaining_core_bound_suffices':True,'circular_premises_admitted':False},
        'next_search_input':{
            'preserve_joined_channels':'S=p^-t*(A-B)+(p^-t-q^-t)*B; second coefficient <=t*log(q/p)',
            'exact_tail_identity':'T(Z;y)=sum_(m<=floor(Z/y)) [M_M(Z/m)-M_M(y)]',
            'M_M':'ordinary-mu prefix restricted only by gcd(d,M)=1',
            'joint_reciprocal_tail':'S(y,t)=S(D,t)-[p^-t*(T(4N/p;y)-3T(2N/p;y)+2T(N/p;y))-q^-t*(T(4N/q;y)-3T(2N/q;y)+2T(N/q;y))]',
            'search_targets':['joint reciprocal-interval correlations with every endpoint retained',
                'auxiliary recurrences that actually reduce scale without an unpaid current-scale boundary',
                'higher-arity signed groups or joint weighted moment controls for the interior'],
            'tail_transform_scope':'source-only algebra in stopped review061; no new growth estimate follows from it',
            'no_free_prefix_convolution':True,'no_assumed_Mertens_RH_or_random_sign_bound':True},
        'reviewed_baseline':{'bound':'O(D/(log D)^(k+1-alpha)) + O((1+log2(4N))^k), D>=2',
            'source':'MOBIUS_FRACTIONAL_FLOW_REVIEW_061.txt section5; analytical proof only',
            'proof_backend_admission_claimed':False,'RH_strength':False},
        'numerical_core_estimates_are_descriptive_only':True,'old_copy_costs_unchanged':True,
        'prior_prime_ratio_obstruction_unchanged':True,'uniform_core_bound_proved':False,
        'uniform_RH_strength_bound_proved':False,'uniform_full_source_bound_proved':False,
        'RH_proved':False,'RH_refuted':False}


def main():
    if OUT.exists():raise FileExistsError('preserve every061 attempt')
    started=time.monotonic();counts=validate_parent()
    old=json.loads((PRIOR.OUT/'discovery.json').read_text());params=old['parameters']
    parent=json.loads((PRIOR.OUT/'mechanism_feedback.json').read_text())
    if parent['source_parameters']!=params:raise ValueError('060 source binding')
    compiled=dict(old['signature'])
    compiled['divisor_coefficients']={int(k):v for k,v in compiled['divisor_coefficients'].items()}
    frozen={name:(ROOT/name).read_bytes() for name in FILES}
    development=sum(check_receipt(json.loads(data)) for name,data in frozen.items() if name.endswith('_development.json'))
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,data in frozen.items():(OUT/'source_snapshot'/name).write_bytes(data)
    meter=SEARCH.Meter();cm=CHECK.Meter(cap=50_000_000,seconds=7200)
    try:
        write(OUT/'spec.json',{'spec':SPEC,'parameters':params,'prior_frozen_counts':counts,
            'new_frozen_files':len(FILES),'frozen_before_new_inference_and_cutoff_search':True,
            'prior_exact_signature_reused_without_reenumeration':True,'hashes_used':False})
        found=SEARCH.discover(params,source_kernel_expressions(params['p'],params['q']),compiled,
            SPEC['cutoff_max_denominator'],meter)
        cert=found['selected'];verification=CHECK.verify_fractional_flow(cert,cm)
        write(OUT/'discovery.json',found)
        write(OUT/'selected.json',{'certificate':cert,'verification':verification,
            'selected_before_arithmetic_prefix_tables_or_new_flow_values':True,
            'finite_cost_used_for_selection':False})
        emit('fractional_flow_inferred',cutoff_pairs=len(found['cutoff_rows']),
             admissible=found['admitted_cutoff_pairs'],theta=cert['head_theta'],rho=cert['exit_rho'])
        scales=json.loads((PRIOR.OUT/'report.json').read_text())['saved_scales']
        results=[]
        with mp.get_context('fork').Pool(SPEC['workers']) as pool:
            for result in pool.imap_unordered(evaluate_task,[(N,cert) for N in scales[::-1]],chunksize=1):
                write(OUT/('flow_'+str(result['N'])+'.json'),result);results.append(result)
                emit('fractional_flow_audit',N=result['N'],completed=len(results),total=len(scales),
                     core_float=result['core_float'],total_float=result['total_float'])
        results.sort(key=lambda r:r['N'])
        write(OUT/'diagnostics.json',{'rows':[{k:v for k,v in r.items() if k!='prefix_table'} for r in results],
            'new_flow_integrals_evaluated':True,'original_source_tables_or_kernel_integrals_recomputed':False,
            'descriptive_float_only':True,'new_finite_growth_claims_tested':False})
        write(OUT/'mechanism_feedback.json',mechanism_feedback(cert,verification,parent))
        validate_parent()
        if any((ROOT/name).read_bytes()!=data for name,data in frozen.items()):raise ValueError('preserve frozen061 sources')
        report={'status':'FRACTIONAL_FLOW_HEAD_EXIT_PROVED_JOINT_INTERIOR_OPEN',
            'kernel_columns':found['kernel_columns_inferred'],'cutoff_pairs_examined':len(found['cutoff_rows']),
            'admissible_cutoff_pairs':found['admitted_cutoff_pairs'],
            'selected_head_theta':cert['head_theta'],'selected_exit_rho':cert['exit_rho'],
            'head_coefficient':cert['head_coefficient'],'exit_coefficient':cert['exit_coefficient'],
            'conserved_exit_terminal_coefficient':cert['endpoint_coefficient'],'log_degree':cert['log_degree'],
            'new_synthetic_tests':28,'saved_scales':scales,
            'prefixes_independently_replayed':sum(r['exact_prefix_and_terminal_audit']['prefixes'] for r in results),
            'development_operations':development,'inference_search_operations':meter.operations,
            'independent_checker_operations':cm.operations,
            'new_prefix_quadrature_diagnostic_operations':sum(r['operations'] for r in results),
            'elapsed_seconds':time.monotonic()-started,
            'parent_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'largest_worker_peak_rss_kib':max(r['worker_peak_rss_kib'] for r in results),
            'largest_prospective_algorithm_bytes':max(r['prospective_algorithm_bytes'] for r in results),
            'workers':SPEC['workers'],'native_threads_per_worker':1,
            'prior_frozen_counts':counts,'new_frozen_source_count':len(FILES),
            'hashes_used':False,'old_suites_or_studies_replayed':False,
            'prior_exact_signature_reused':True,'new_flow_integrals_evaluated':True,
            'original_source_tables_or_kernel_integrals_recomputed':False,
            'finite_constants_refitted':False,'head_bound_proved':True,'exit_residual_bound_proved':True,
            'conserved_exit_terminal_bound_proved':True,'uniform_core_bound_proved':False,
            'uniform_RH_strength_bound_proved':False,'uniform_full_source_bound_proved':False,
            'RH_proved':False,'RH_refuted':False}
        write(OUT/'report.json',report)
        emit('fractional_flow_complete',status=report['status'],elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',{'type':type(exc).__name__,'message':str(exc),
            'elapsed_seconds':time.monotonic()-started,'inference_operations':meter.operations,
            'checker_operations':cm.operations,'uniform_core_bound_proved':False,'RH_proved':False})
        raise


if __name__=='__main__':main()
