"""A new search consumes073 proof obstructions; historical073 science is fixed."""
import os
for _key in ('OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'OMP_NUM_THREADS'):
    os.environ[_key] = '1'
from fractions import Fraction as Q
import json
import multiprocessing as mp
import resource
import time

import mobius_centered_storage_074 as SEARCH
import check_mobius_centered_storage_074 as GRAMMAR
import check_mobius_prime_storage_073 as CHECK
import run_mobius_prime_storage_073 as PRIOR
from run_fractional_prime_kernel_051 import write, emit

ROOT = PRIOR.ROOT
OUT = PRIOR.OUT / 'centered_storage_followup_001'
FILES = ['mobius_centered_storage_074.py', 'test_mobius_centered_storage_074.py',
         'test_mobius_centered_storage_integration_074.py',
         'mobius_centered_storage_search_074_development.json',
         'check_mobius_centered_storage_074.py', 'test_check_mobius_centered_storage_074.py',
         'mobius_centered_storage_checker_074_development.json',
         'MOBIUS_CENTERED_STORAGE_CHECK_SCOPE_074.txt',
         'mobius_centered_storage_protocol_074.txt', 'run_mobius_centered_storage_074.py']
SPEC = dict(source=SEARCH.B.SOURCE_SPEC, q=['1', '65/64'], branches=list(SEARCH.BRANCHES),
            discovery_children=[2,512], adaptation_children=[513,16384],
            final_children=[16385,32768], adaptive_rounds=3, workers=3,
            native_threads_per_worker=1, maximum_aggregate_bytes=16*1024**3,
            module_seconds=7200, work_limit=300_000_000_000,
            known073_final_data_now_used_for_adaptation=True,
            final_data_generated_after_all_new_formulas_fixed=True,
            hashes_used=False, uniform_recurrence_proved=False, RH_proved=False)


def validate_parent():
    counts = PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve073 science '+name)
    feedback = json.loads((PRIOR.OUT/'asymptotic_feedback.json').read_text())
    for name in feedback['new_frozen_postrun_files']:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'postrun_snapshot'/name).read_bytes():
            raise ValueError('preserve073 proof feedback '+name)
    findings = json.loads((PRIOR.OUT/'postrun_findings.json').read_text())
    if findings['learned_programs_refuted'] != 3 or findings['learned_programs_refuted_for_every_finite_constant'] != 2:
        raise ValueError('preserve exact motivating obstruction')
    return counts + [len(PRIOR.FILES), len(feedback['new_frozen_postrun_files'])]


def task_name(task):
    branch, q = task
    return branch+'_'+q.replace('/','_')


def fit_task(task):
    branch, q = task
    start = time.monotonic()
    discovery = json.loads((OUT/'learning_discovery.json').read_text())
    adaptation = json.loads((OUT/'learning_adaptation.json').read_text())
    data = SEARCH.B.join_data(discovery, adaptation)
    pm, cm = SEARCH.B.Meter(SPEC['work_limit']), CHECK.Meter(SPEC['work_limit'])
    result = SEARCH.discover(discovery, adaptation, q, branch, pm, SPEC['adaptive_rounds'])
    admissions = []
    for step in result['history']:
        ordinary = CHECK.verify_candidate(step['candidate'], data, cm)
        grammar = GRAMMAR.verify_grammar(step['candidate'], branch)
        if ordinary.get('verified') is not True or grammar.get('verified') is not True:
            raise ValueError('independent candidate admission '+str((ordinary,grammar)))
        admissions.append(dict(candidate=ordinary, grammar=grammar))
    baseline = CHECK.verify_candidate(result['baseline'], data, cm)
    if baseline.get('verified') is not True:
        raise ValueError('independent baseline admission '+str(baseline))
    result.update(admissions=admissions, baseline_admission=baseline,
                  checker_operations=cm.ops, elapsed_seconds=time.monotonic()-start,
                  worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    file='candidate_'+task_name(task)+'.json'
    write(OUT/file,result)
    return dict(branch=branch,q=q,file=file,rounds=len(result['history']),
                rays=len(result['candidate']['rays']),C=result['candidate']['C'],
                baseline_C=result['baseline']['C'],base_upper=result['candidate']['base_upper'],
                adaptation_violations=result['history'][-1]['adaptation_violations'],
                initial_directions=result['initial_directions'],final_directions=result['final_directions'],
                producer_operations=pm.ops,checker_operations=cm.ops,
                elapsed_seconds=result['elapsed_seconds'],worker_peak_rss_kib=result['worker_peak_rss_kib'])


def final_task(task):
    branch,q=task
    start=time.monotonic()
    candidate=json.loads((OUT/('candidate_'+task_name(task)+'.json')).read_text())
    data=json.loads((OUT/'final_data.json').read_text())
    children=list(range(SPEC['final_children'][0],SPEC['final_children'][1]+1))
    cm=CHECK.Meter(SPEC['work_limit'])
    learned=CHECK.evaluate_candidate(candidate['candidate'],data,cm,scales=children)
    baseline=CHECK.evaluate_candidate(candidate['baseline'],data,cm,scales=children)
    if learned['status']=='INVALID' or baseline['status']=='INVALID':
        raise ValueError('invalid final formula '+str((learned,baseline)))
    result=dict(branch=branch,q=q,learned=learned,baseline=baseline,checker_operations=cm.ops,
                elapsed_seconds=time.monotonic()-start,
                worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                uniform_recurrence_proved=False,uniform_head_bound_proved=False,RH_proved=False)
    file='final_'+task_name(task)+'.json'
    write(OUT/file,result)
    return dict(branch=branch,q=q,file=file,learned_status=learned['status'],
                learned_violations=len(learned['violating_scales']),
                learned_ambiguities=len(learned['inconclusive_scales']),
                baseline_status=baseline['status'],baseline_violations=len(baseline['violating_scales']),
                worst_learned_lower=learned['worst_lower'],worst_baseline_lower=baseline['worst_lower'],
                checker_operations=cm.ops,elapsed_seconds=result['elapsed_seconds'],
                worker_peak_rss_kib=result['worker_peak_rss_kib'])


def collect(pool,function,tasks,start,event):
    results,peak=[],0
    iterator=pool.imap_unordered(function,tasks,chunksize=1)
    while len(results)<len(tasks):
        if time.monotonic()-start>SPEC['module_seconds']:
            raise TimeoutError('074 whole-stage deadline')
        used=PRIOR.rss([os.getpid()]+[p.pid for p in pool._pool]);peak=max(peak,used)
        if used>SPEC['maximum_aggregate_bytes']:
            raise MemoryError('074 aggregate memory')
        try:item=iterator.next(timeout=1)
        except mp.TimeoutError:continue
        results.append(item)
        emit(event,branch=item['branch'],q=item['q'],completed=len(results),total=len(tasks))
    return sorted(results,key=lambda r:(r['branch'],Q(r['q']))),peak


def main():
    if OUT.exists():raise FileExistsError('preserve every074 attempt')
    start=time.monotonic();counts=validate_parent()
    frozen={name:(ROOT/name).read_bytes() for name in FILES}
    receipts=[json.loads(content) for name,content in frozen.items() if name.endswith('_development.json')]
    for receipt in receipts:
        if receipt.get('status',receipt.get('final_status'))!='PASS':
            raise ValueError('development final status')
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,content in frozen.items():
        with (OUT/'source_snapshot'/name).open('xb') as f:f.write(content)
    try:
        write(OUT/'spec.json',dict(spec=SPEC,prior_frozen_counts=counts,new_frozen_files=len(FILES)))
        old={phase:json.loads((PRIOR.OUT/(phase+'_data.json')).read_text())
             for phase in ('discovery','adaptation','final')}
        for phase in old:
            admission=json.loads((PRIOR.OUT/(phase+'_source_admission.json')).read_text())
            if admission['source_admission']['verified'] is not True:
                raise ValueError('inherited independent source admission')
        write(OUT/'learning_discovery.json',old['discovery'])
        write(OUT/'learning_adaptation.json',SEARCH.B.join_data(*old.values()))
        del old
        tasks=[(branch,q) for branch in SPEC['branches'] for q in SPEC['q']]
        with mp.get_context('spawn').Pool(SPEC['workers']) as pool:
            candidates,peak1=collect(pool,fit_task,tasks,start,'centered_candidate_frozen')
            fixed={row['file']:(OUT/row['file']).read_bytes() for row in candidates}
            write(OUT/'candidate_summary.json',dict(candidates=candidates,
                  all_candidates_fixed_before_final_data=True,old073_final_used_for_adaptation=True))
            children=list(range(SPEC['final_children'][0],SPEC['final_children'][1]+1))
            scales=sorted({1,*children,*(k//2 for k in children)})
            pm,cm=SEARCH.B.Meter(SPEC['work_limit']),CHECK.Meter(SPEC['work_limit'])
            phase_start=time.monotonic()
            data=SEARCH.B.make_data(SPEC['source'],scales,pm)
            admission=CHECK.verify_data(data,cm)
            if admission.get('verified') is not True:raise ValueError('new final source admission')
            write(OUT/'final_data.json',data);del data
            phase=dict(source_admission=admission,producer_operations=pm.ops,checker_operations=cm.ops,
                       elapsed_seconds=time.monotonic()-phase_start,source_rows=len(scales),
                       prospective_bytes=pm.peak_bytes)
            write(OUT/'final_source_admission.json',phase)
            emit('centered_final_source_admitted',rows=len(scales),elapsed_seconds=phase['elapsed_seconds'])
            final,peak2=collect(pool,final_task,tasks,start,'centered_final_checked')
        for name,content in fixed.items():
            if (OUT/name).read_bytes()!=content:raise ValueError('final candidate changed')
        for name,content in frozen.items():
            if (ROOT/name).read_bytes()!=content:raise ValueError('frozen074 source changed')
        validate_parent()
        parent_peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        child_peak=max(row['worker_peak_rss_kib'] for row in candidates+final)
        report=dict(status='CENTERED_STORAGE_GRAMMAR_SEARCH_COMPLETE_UNIFORM_CONTROL_OPEN',
                    candidates=candidates,final=final,
                    candidate_programs=len(candidates),baseline_programs=len(candidates),
                    final_refutations=sum(row['learned_status']=='REFUTED' for row in final),
                    final_finite_survivors=sum(row['learned_status']=='VERIFIED_ON_FINITE_DOMAIN' for row in final),
                    finite_final_inequalities=2*len(tasks)*len(children),
                    source_phase=phase,elapsed_seconds=time.monotonic()-start,
                    producer_operations=pm.ops+sum(row['producer_operations'] for row in candidates),
                    checker_operations=cm.ops+sum(row['checker_operations'] for row in candidates+final),
                    parent_peak_rss_kib=parent_peak,largest_worker_peak_rss_kib=child_peak,
                    sampled_parallel_rss_peak_bytes=max(peak1,peak2),
                    conservative_sum_process_peaks_bytes=1024*(parent_peak+SPEC['workers']*child_peak),
                    prior_frozen_counts=counts,new_frozen_files=len(FILES),
                    development_receipts=receipts,
                    known073_data_used_for_new_grammar=True,old_unchanged_science_replayed=False,
                    hashes_used=False,uniform_domination_proved=True,uniform_recurrence_proved=False,
                    uniform_head_bound_proved=False,uniform_core_bound_proved=False,RH_proved=False)
        write(OUT/'report.json',report)
        write(OUT/'next_search_input.json',dict(schema='centered-signed-storage-obligation-v1',
                    source=SPEC['source'],candidate_files=[row['file'] for row in candidates],
                    final_files=[row['file'] for row in final],
                    inherited_proof_feedback='../postrun_next_search_input.json',
                    new_registered_rule='theta=1/2 shares the high-smooth bulk for this source',
                    main_obligation='prove a full signed recurrence or change construction using exact new counterexamples',
                    unknown_modes='theta<1/2 mixed rays remain unresolved, not zero',
                    all_uniform_arithmetic_remainders_paid=False,
                    uniform_recurrence_proved=False,uniform_head_bound_proved=False,RH_proved=False))
        emit('centered_storage_complete',elapsed_seconds=report['elapsed_seconds'],
             refuted=report['final_refutations'],finite_survivors=report['final_finite_survivors'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',dict(type=type(exc).__name__,message=str(exc),RH_proved=False))
        raise


if __name__=='__main__':main()
