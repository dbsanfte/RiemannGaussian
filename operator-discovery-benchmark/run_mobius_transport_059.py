"""Frozen arithmetic pairing/upper-bound discovery on the joined058 source."""
import os
for _thread_setting in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[_thread_setting] = '1'

from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import json
import math
import multiprocessing as mp
import random
import resource
import time

import run_prime_transfer_058 as PRIOR
import mobius_transport_search_059 as SEARCH
from run_fractional_prime_kernel_051 import write,emit,check_receipt

ROOT = Path(__file__).resolve().parent
OUT = PRIOR.OUT/'mobius_transport_followup_001'
TRAIN = [64,96,128,192,256,384,512,768,1024,1536,2048,3072]
FINAL_SEED = 590059
FILES = ['mobius_transport_source_059.py','test_mobius_transport_source_059.py',
    'mobius_transport_source_059_development.json','MOBIUS_TRANSPORT_SOURCE_SCOPE_059.txt',
    'check_mobius_transport_059.py','test_check_mobius_transport_059.py',
    'check_mobius_transport_059_development.json','MOBIUS_TRANSPORT_CHECK_SCOPE_059.txt',
    'MOBIUS_TRANSPORT_REVIEW_059.txt',
    'mobius_transport_search_059.py','test_mobius_transport_search_059.py','mobius_transport_search_059_development.json',
    'run_mobius_transport_059.py','test_run_mobius_transport_059.py','mobius_transport_runner_059_development.json',
    'mobius_transport_protocol_059.txt']
PARAMETERS = PROGRAMS = SELECTED = SOURCE_CONTEXT = SOURCE_METER = None


def validate_parent():
    counts = PRIOR.validate_parent()
    snapshots = list((PRIOR.OUT/'source_snapshot').iterdir())
    if len(snapshots) != len(PRIOR.FILES) or any((ROOT/p.name).read_bytes() != p.read_bytes() for p in snapshots):
        raise ValueError('preserve frozen058 sources')
    for name in ('analyze_prime_transfer_058.py',):
        if (ROOT/name).read_bytes() != (PRIOR.OUT/name).read_bytes(): raise ValueError('preserve058 feedback producer')
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if report['uniform_full_source_bound_proved'] is not False or report['RH_proved'] is not False:
        raise ValueError('058 signed forcing remains open')
    return counts+[len(snapshots)]


def source_parameters():
    feedback = json.loads((PRIOR.OUT/'mechanism_feedback.json').read_text())
    target = feedback['next_signed_target']
    row = next(r for r in json.loads((PRIOR.OUT/'proof_candidates.json').read_text())['rows']
        if r['candidate']['id'] == target['operator_id'])
    interp = row['interpretation']
    if interp['family'] != 'weighted_prime_exchange' or interp['scalar'] != '1':
        raise ValueError('058 standard-orientation complete exchange input')
    ep = next(r for r in json.loads((PRIOR.OUT/'endpoint_programs.json').read_text())['rows']
        if r['id'] == target['operator_id'] and r['program']['request']['alpha'] == target['alpha'])
    p,q = interp['p'],interp['q']
    params = {'primes':sorted(interp['R']+[p,q]),'p':p,'q':q,
        'alpha':target['alpha'],'gamma':target['gamma'],'tau':target['tau']}
    if not ep['verification']['both_end_region_bounds_proved']:
        raise ValueError('paid endpoints required')
    if any(ep['program']['request'][k] != params[k] for k in ('alpha','gamma','tau')):
        raise ValueError('bind every moving-cutoff endpoint parameter')
    if any(Q(ep['program'][region]['N_power']) > Q(1,2) for region in ('microscopic','tail')):
        raise ValueError('both paid endpoint powers must support RH recovery')
    return params, {'operator_id':target['operator_id'],'endpoint_program':ep,
        'conditional_bridge_review':'PRIME_TRANSFER_REVIEW_058.txt section4',
        'full_source_RH_implication_conditional_on_missing_uniform_transport_cost_bound':True,
        'uniform_bound_proved':False,'RH_proved':False}


def request(parameters,N): return {'N':N,**parameters}


def dominance_certificate(policy):
    return {'schema':'mobius-profile-dominance-v1','policy':policy,
        'reference':{'steps':[{'kind':'scan','group':'profile','order':'asc','method':'stack'}]},
        'bound':'B_reference<=B_policy','uniform_growth_bound_proved':False,'RH_proved':False}


def worker_init(parameters,programs,selected=None):
    global PARAMETERS,PROGRAMS,SELECTED,SOURCE_CONTEXT,SOURCE_METER
    import mobius_transport_source_059 as SOURCE
    PARAMETERS,PROGRAMS,SELECTED=parameters,programs,selected
    SOURCE_METER=SOURCE.Meter(cap=100_000_000_000,seconds=7200)
    SOURCE_CONTEXT=SOURCE.prepare_context(SOURCE_METER)


def training_task(N):
    import mobius_transport_source_059 as SOURCE
    sm=SEARCH.Meter(cap=100_000_000_000,seconds=7200)
    source=SOURCE.evaluate(request(PARAMETERS,N),degree=64,meter=SOURCE_METER,context=SOURCE_CONTEXT)
    costs=SEARCH.evaluate_policies(N,source['tokens'],PROGRAMS,sm)
    return {'N':N,'source':source,'costs':costs,'absolute_sum':source['absolute_sum'],
        'source_worker_pid':os.getpid(),'source_worker_cumulative_operations':SOURCE_METER.operations,
        'planner_operations':sm.operations,'worker_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


def exact_tokens(source):
    return [{k:t[k] for k in ('d','profile','sign','kernel_sign','mu')} for t in source['tokens']]


def independent_final(parameters,programs,selected,N,source=None):
    import mobius_transport_source_059 as SOURCE
    import check_mobius_transport_059 as CHECK
    pm=SOURCE.Meter(cap=100_000_000_000,seconds=7200)
    sm=SEARCH.Meter(cap=100_000_000_000,seconds=7200)
    cm=CHECK.Meter(cap=200_000_000_000,seconds=7200)
    req=request(parameters,N)
    source=SOURCE.evaluate(req,degree=64,meter=pm) if source is None else source
    if source['request'] != req: raise ValueError('numerical source must match all requested parameters')
    needed=sorted({r['program_id'] for r in selected})
    by_id={r['id']:r for r in programs}; context=SEARCH.Context()
    plans=[SEARCH.build_plan(N,source['tokens'],by_id[i]['policy'],sm,context) for i in needed]
    checked=CHECK.evaluate_many(req,plans,precision=256,meter=cm)
    if exact_tokens(source) != checked['tokens']:
        raise ValueError('producer and independent complete arithmetic tokens differ')
    rows=[]
    for claim in selected:
        index=needed.index(claim['program_id'])
        bound=checked['rows'][index]['bound']
        assessment=CHECK.assess_bound(req,bound,claim['claim'],cm)
        float_cost=SEARCH.plan_cost(source['tokens'],plans[index],sm)
        # This is a numerical discrepancy report, never a containment test
        # pretending a rounded float is a rigorous producer enclosure.
        midpoint=float((Q(bound['lower'])+Q(bound['upper']))/2)
        rows.append({'id':claim['id'],'program_id':claim['program_id'],'N':N,
            'claim':claim['claim'],'assessment':assessment,'checked_cost':bound,
            'float_cost':float_cost,'float_absolute_difference_from_checked_midpoint':abs(float_cost-midpoint),
            'paired_tokens':2*len(plans[index]['pairs']),'unmatched_tokens':len(plans[index]['unmatched']),
            'uniform_cost_bound_proved':False,'RH_proved':False})
    # Descriptive source sensitivity: same squarefree support and exact W
    # geometry, replacing mu signs by |mu|. Never used for selection.
    positive=[{**t,'mu':1,'sign':t['kernel_sign']} for t in source['tokens']]
    ablation=[]
    for i,index in zip(needed,range(len(needed))):
        alternate=SEARCH.build_plan(N,positive,by_id[i]['policy'],sm,SEARCH.Context())
        ablation.append({'program_id':i,'ordinary_mu_cost_float':SEARCH.plan_cost(source['tokens'],plans[index],sm),
            'absolute_mu_cost_float':SEARCH.plan_cost(positive,alternate,sm),
            'descriptive_float_only':True,'used_for_selection':False})
    return {'N':N,'source':source,'program_ids':needed,'plans':plans,'independent':checked,
        'claims':rows,'source_sign_ablation':ablation,
        'operations':{'producer':pm.operations,'planner':sm.operations,'checker':cm.operations},
        'worker_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


def final_task(N): return independent_final(PARAMETERS,PROGRAMS,SELECTED,N)


def final_scales():
    # Call only AFTER writing the selected candidate batch.
    rng=random.Random(FINAL_SEED)
    return sorted({4096,8192,16384,rng.randrange(4500,7500)|1,rng.randrange(10000,15000)|1})


def main():
    import check_mobius_transport_059 as CHECK
    if OUT.exists(): raise FileExistsError('preserve any059 scientific run')
    started=time.monotonic(); prior_counts=validate_parent()
    parameters,binding=source_parameters()
    development=sum(check_receipt(json.loads((ROOT/n).read_text())) for n in FILES if n.endswith('_development.json'))
    frozen={n:(ROOT/n).read_bytes() for n in FILES}
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for n,data in frozen.items(): (OUT/'source_snapshot'/n).write_bytes(data)
    try:
        kernels=SEARCH.source_kernel_expressions(parameters['p'],parameters['q'])
        programs=SEARCH.grammar(8,kernels); gate=SEARCH.profile_dominance(programs); scored=gate['scored']
        cm=CHECK.Meter(cap=10_000_000_000,seconds=7200)
        by_id={r['id']:r for r in programs}
        dominance=[CHECK.verify_profile_dominance(by_id[r['id']]['policy'],dominance_certificate(by_id[r['id']]['policy']),cm)
            for r in gate['excluded']]
        write(OUT/'protocol.json',{'source_parameters':parameters,'source_binding':binding,'training_scales':TRAIN,
            'final_scale_rule':'4096,8192,16384 plus two seeded odd integers in[4500,7500),[10000,15000); generated afterselection',
            'final_seed':FINAL_SEED,'workers':3,'native_threads_per_worker':1,
            'source_degree':64,'final_Arb_precision':256,'grammar_max_denominator':8,
            'kernel_expression_dictionary':kernels,
            'explicit_extra_block_exponents':['1/257','2/11','3/11'],'betas':SEARCH.BETAS,
            'constant_grid':[str(c) for c in SEARCH.CONSTANTS],
            'aggregate_memory_limit_bytes':16*1024**3,'seconds_per_module':7200,
            'previous_goal_turn':'PROGRESS:058 exact search ran and established new signed target plus grammar obstruction',
            'no_magnitude_oracle_in_pair_generation':True,'hashes_used':False,
            'prior_frozen_counts':prior_counts,'new_frozen_files':len(FILES),
            'old_suites_or_studies_replayed':False})
        write(OUT/'grammar.json',{'programs':programs,'profile_optimum_reference_id':gate['reference_id']})
        write(OUT/'dominance.json',{'excluded':gate['excluded'],'verification':dominance,
            'scored_ids':[r['id'] for r in scored],'uniform_growth_bound_proved':False})
        emit('mobius_transport_frozen',programs=len(programs),dominated=len(gate['excluded']),scored=len(scored))
        observations={}
        with mp.get_context('fork').Pool(3,initializer=worker_init,initargs=(parameters,scored)) as pool:
            for result in pool.imap_unordered(training_task,TRAIN[::-1],chunksize=1):
                observations[result['N']]=result
                emit('mobius_transport_training',completed=len(observations),total=len(TRAIN),N=result['N'])
        observations=dict(sorted(observations.items()))
        write(OUT/'training.json',{'rows':list(observations.values()),'numeric_screening_only':True})
        hypotheses=SEARCH.hypotheses(scored,observations)
        selected=SEARCH.select(hypotheses,scored)
        write(OUT/'hypotheses.json',{'rows':hypotheses,'uniform_growth_bound_proved':False})
        write(OUT/'selected.json',{'rows':selected,'source_parameters':parameters,
            'selected_before_final_source_values':True,'numerical_growth_is_not_a_theorem':True})
        numbers=final_scales()
        if set(numbers)&set(TRAIN): raise ValueError('disjoint final parameter observations')
        write(OUT/'final_spec.json',{'scales':numbers,'new_parameter_observations':True,
            'underlying_arithmetic_overlaps_previous_research':True,'ordinary_primes_claimed_unseen':False})
        emit('mobius_transport_selected',claims=len(selected),policies=len({r['program_id'] for r in selected}),final_scales=numbers)
        final=[]
        with mp.get_context('fork').Pool(3,initializer=worker_init,initargs=(parameters,scored,selected)) as pool:
            for result in pool.imap_unordered(final_task,numbers[::-1],chunksize=1):
                final.append(result)
                write(OUT/('final_'+str(result['N'])+'.json'),result)
                emit('mobius_transport_independent_audit',completed=len(final),total=len(numbers),N=result['N'])
        final.sort(key=lambda r:r['N'])
        assessments=[]
        for claim in selected:
            rows=[next(r for r in obs['claims'] if r['id']==claim['id']) for obs in final]
            counts=dict(Counter(r['assessment']['status'] for r in rows))
            assessments.append({'id':claim['id'],'program_id':claim['program_id'],'claim':claim['claim'],
                'finite_status_counts':counts,'status':'REFUTED_FIXED_BOUND' if counts.get('REFUTED') else
                    'UNRESOLVED_FINITE_AUDIT' if counts.get('UNRESOLVED') else 'OPEN_AFTER_FINITE_TESTS',
                'counterexample_scales':[r['N'] for r in rows if r['assessment']['status']=='REFUTED'],
                'uniform_cost_bound_proved':False,'RH_proved':False})
        write(OUT/'assessment.json',{'rows':assessments,'uniform_cost_bound_proved':False})
        write(OUT/'next_search_input.json',{'schema':'mobius-transport-obstruction-feedback-v1',
            'source_parameters':parameters,'source_binding':binding,
            'selected_programs':[by_id[i] for i in sorted({r['program_id'] for r in selected})],
            'claims_and_assessment':assessments,
            'paid':'complete signed matching triangle bound, and universal within-profile optimum/dominance',
            'unpaid':'uniform arithmetic control of the selected transport cost including all unmatched terms',
            'new_proof_coordinate':'weighted absolute prefix discrepancies within profiles plus explicit cross-profile matching costs',
            'no_final_constant_refitted':True,'RH_proved':False,'uniform_full_source_bound_proved':False})
        validate_parent()
        if any((ROOT/n).read_bytes()!=data for n,data in frozen.items()): raise ValueError('preserve frozen059 source bytes')
        report={'status':'ARITHMETIC_TRANSPORT_BOUNDS_SEARCHED_UNIFORM_COST_OPEN',
            'programs':len(programs),'dominated_programs':len(gate['excluded']),'numerically_scored_programs':len(scored),
            'fixed_growth_hypotheses':len(hypotheses),'training_scales':TRAIN,'final_scales':numbers,
            'selected_claims':len(selected),'selected_policies':len({r['program_id'] for r in selected}),
            'finite_status_counts':dict(Counter(row['assessment']['status'] for r in final for row in r['claims'])),
            'assessment_status_counts':dict(Counter(r['status'] for r in assessments)),
            'development_operations':development,'dominance_checker_operations':cm.operations,
            'training_producer_operations':sum(max(r['source_worker_cumulative_operations'] for r in observations.values()
                if r['source_worker_pid']==pid) for pid in {r['source_worker_pid'] for r in observations.values()}),
            'training_planner_operations':sum(r['planner_operations'] for r in observations.values()),
            'final_operations':{name:sum(r['operations'][name] for r in final) for name in ('producer','planner','checker')},
            'elapsed_seconds':time.monotonic()-started,'parent_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'largest_worker_peak_rss_kib':max([0]+[r['worker_peak_rss_kib'] for r in list(observations.values())+final]),
            'prior_frozen_counts':prior_counts,'new_frozen_source_count':len(FILES),
            'hashes_used':False,'old_suites_or_studies_replayed':False,
            'all_scale_pairing_upper_formula_proved':True,'uniform_transport_cost_growth_bound_proved':False,
            'uniform_full_source_bound_proved':False,'RH_proved':False,'RH_refuted':False}
        write(OUT/'report.json',report)
        emit('mobius_transport_complete',elapsed_seconds=report['elapsed_seconds'],statuses=report['finite_status_counts'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',{'type':type(exc).__name__,'message':str(exc),
            'elapsed_seconds':time.monotonic()-started,'RH_proved':False,'uniform_full_source_bound_proved':False})
        raise


if __name__ == '__main__': main()
