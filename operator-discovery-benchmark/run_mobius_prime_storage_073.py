"""Frozen discovery/adaptation/final study of signed prime storage candidates."""
import os
for _key in ('OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'OMP_NUM_THREADS'):
    os.environ[_key] = '1'
import json
import multiprocessing as mp
from fractions import Fraction as Q
import resource
import time

import mobius_prime_storage_073 as SEARCH
import check_mobius_prime_storage_073 as CHECK
import run_mobius_exchange_law_072 as PRIOR
from run_fractional_prime_kernel_051 import write, emit, check_receipt

ROOT = PRIOR.ROOT
OUT = PRIOR.OUT / 'prime_storage_followup_001'
FILES = ['mobius_prime_storage_073.py', 'test_mobius_prime_storage_073.py',
         'test_mobius_prime_storage_integration_073.py', 'mobius_prime_storage_search_073_development.json',
         'check_mobius_prime_storage_073.py', 'test_check_mobius_prime_storage_073.py',
         'mobius_prime_storage_checker_073_development.json', 'MOBIUS_PRIME_STORAGE_CHECK_SCOPE_073.txt',
         'MOBIUS_PRIME_STORAGE_SCHEMA_073.txt', 'MOBIUS_PRIME_BLOCK_REVIEW_073.txt',
         'MOBIUS_PRIME_STORAGE_ASYMPTOTIC_REVIEW_073.txt',
         'mobius_prime_storage_protocol_073.txt', 'run_mobius_prime_storage_073.py']
SPEC = dict(source=SEARCH.SOURCE_SPEC, q=['1', '18/17', '258/257'],
            discovery_children=[2,512], adaptation_children=[513,2048], final_children=[2049,16384],
            adaptive_rounds=3, counterexamples_per_round=32, pricing_rounds=3,
            asymptotic_bulk_modes_annihilated_before_scoring=True,
            trace_budget=128, precision=20, workers=3, native_threads=1,
            maximum_aggregate_bytes=16*1024**3, module_seconds=7200, work_limit=300_000_000_000,
            uniform_recurrence_proved=False, uniform_head_bound_proved=False, RH_proved=False,
            learner_sees_final_data_before_candidate_freeze=False, hashes_used=False)


def validate_parent():
    counts = PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve072 '+name)
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    publication = json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    if report['uniform_profile_laws'] != 9 or report['sublinear_profile_candidates'] or publication['RH_proved']:
        raise ValueError('preserve072 proof-price obstruction and open RH target')
    return counts + [len(PRIOR.FILES)]


def rss(pids):
    total = 0
    for pid in pids:
        try:
            with open('/proc/'+str(pid)+'/status') as source:
                for line in source:
                    if line.startswith('VmRSS:'):
                        total += int(line.split()[1])*1024
        except FileNotFoundError:
            pass
    return total


def phase_data(name, children):
    scales = sorted({1, *children, *(k//2 for k in children)})
    pm, cm = SEARCH.Meter(SPEC['work_limit']), CHECK.Meter(SPEC['work_limit'])
    start = time.monotonic()
    data = SEARCH.make_data(SPEC['source'], scales, pm)
    admission = CHECK.verify_data(data, cm)
    if admission.get('verified') is not True:
        raise ValueError('independent source admission '+name+': '+str(admission))
    write(OUT/(name+'_data.json'), data)
    result = dict(name=name, source_rows=len(scales), child_scales=len(children),
                  source_admission=admission, producer_operations=pm.ops, checker_operations=cm.ops,
                  prospective_bytes=pm.peak_bytes, elapsed_seconds=time.monotonic()-start)
    write(OUT/(name+'_source_admission.json'), result)
    emit('signed_prime_source_admitted', phase=name, rows=len(scales), elapsed_seconds=result['elapsed_seconds'])
    return result


def fit_task(q):
    start = time.monotonic()
    discovery = json.loads((OUT/'discovery_data.json').read_text())
    adaptation = json.loads((OUT/'adaptation_data.json').read_text())
    complete = SEARCH.join_data(discovery, adaptation)
    pm, cm = SEARCH.Meter(SPEC['work_limit']), CHECK.Meter(SPEC['work_limit'])
    result = SEARCH.discover(discovery, adaptation, q, pm, SPEC['adaptive_rounds'])
    admissions = []
    for item in result['history']:
        verdict = CHECK.verify_candidate(item['candidate'], complete, cm)
        if verdict.get('verified') is not True:
            raise ValueError('candidate admission '+str(verdict))
        # Independent physical-coordinate form of the three supplied bulk modes.
        for ray in item['candidate']['rays']:
            v = list(map(Q,ray['direction']))
            if not v[2] == v[3] == v[4] == v[5]:
                raise ValueError('unpaid asymptotic factor-count mode in candidate')
        verdict['asymptotic_bulk_modes_annihilated'] = True
        admissions.append(verdict)
    baseline_admission = CHECK.verify_candidate(result['baseline'], complete, cm)
    if baseline_admission.get('verified') is not True:
        raise ValueError('baseline admission '+str(baseline_admission))
    result.update(q=q, admissions=admissions, baseline_admission=baseline_admission,
                  producer_operations=pm.ops, checker_operations=cm.ops,
                  elapsed_seconds=time.monotonic()-start,
                  worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    name='candidate_'+q.replace('/','_')+'.json'
    write(OUT/name, result)
    return dict(q=q, file=name, rounds=len(result['history']),
                rays=len(result['candidate']['rays']), C=result['candidate']['C'],
                base_upper=result['candidate']['base_upper'],
                baseline_C=result['baseline']['C'],
                adaptation_violations=result['history'][-1]['adaptation_violations'],
                learned_directions=sum(len(h['candidate']['search_metadata']['learned_directions']) for h in result['history']),
                catalog_directions=result['catalog_directions'],
                producer_operations=pm.ops, checker_operations=cm.ops,
                prospective_bytes=pm.peak_bytes, elapsed_seconds=result['elapsed_seconds'],
                worker_peak_rss_kib=result['worker_peak_rss_kib'])


def final_task(q):
    start = time.monotonic()
    saved = json.loads((OUT/('candidate_'+q.replace('/','_')+'.json')).read_text())
    data = json.loads((OUT/'final_data.json').read_text())
    scales = list(range(SPEC['final_children'][0], SPEC['final_children'][1]+1))
    cm = CHECK.Meter(SPEC['work_limit'])
    learned = CHECK.evaluate_candidate(saved['candidate'], data, cm, scales=scales)
    baseline = CHECK.evaluate_candidate(saved['baseline'], data, cm, scales=scales)
    if learned['status']=='INVALID' or baseline['status']=='INVALID':
        raise ValueError('invalid final candidate '+str(learned)+str(baseline))
    result = dict(q=q, learned=learned, baseline=baseline, checker_operations=cm.ops,
                  elapsed_seconds=time.monotonic()-start,
                  worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  uniform_recurrence_proved=False, uniform_head_bound_proved=False, RH_proved=False)
    write(OUT/('final_'+q.replace('/','_')+'.json'), result)
    return dict(q=q, learned_status=learned['status'], baseline_status=baseline['status'],
                learned_violations=len(learned['violating_scales']), baseline_violations=len(baseline['violating_scales']),
                learned_inconclusive=len(learned['inconclusive_scales']), baseline_inconclusive=len(baseline['inconclusive_scales']),
                worst_learned_lower=learned['worst_lower'], worst_baseline_lower=baseline['worst_lower'],
                checker_operations=cm.ops, elapsed_seconds=result['elapsed_seconds'],
                worker_peak_rss_kib=result['worker_peak_rss_kib'])


def collect(pool, function, args, start, event):
    results, peak = [], 0
    it = pool.imap_unordered(function, args, chunksize=1)
    while len(results)<len(args):
        if time.monotonic()-start>SPEC['module_seconds']:
            raise TimeoutError('073 whole-stage deadline')
        used=rss([os.getpid()]+[p.pid for p in pool._pool]);peak=max(peak,used)
        if used>SPEC['maximum_aggregate_bytes']:
            raise MemoryError('073 aggregate memory')
        try: item=it.next(timeout=1)
        except mp.TimeoutError: continue
        results.append(item)
        emit(event,q=item['q'],completed=len(results),total=len(args))
    return sorted(results,key=lambda r:Q(r['q'])),peak


def main():
    if OUT.exists():
        raise FileExistsError('preserve every073 attempt')
    start=time.monotonic();counts=validate_parent()
    frozen={n:(ROOT/n).read_bytes() for n in FILES}
    receipts=[json.loads(b) for n,b in frozen.items() if n.endswith('_development.json')]
    development=sum(check_receipt(r) for r in receipts)
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,content in frozen.items():
        (OUT/'source_snapshot'/name).write_bytes(content)
    try:
        write(OUT/'spec.json',dict(spec=SPEC,prior_frozen_counts=counts,new_frozen_files=len(FILES)))
        phases=[phase_data('discovery',list(range(2,513))),phase_data('adaptation',list(range(513,2049)))]
        with mp.get_context('spawn').Pool(SPEC['workers']) as pool:
            candidates,peak1=collect(pool,fit_task,SPEC['q'],start,'signed_prime_candidate_frozen')
            fixed={r['file']:(OUT/r['file']).read_bytes() for r in candidates}
            write(OUT/'candidate_summary.json',dict(candidates=candidates,all_candidates_fixed_before_final_data=True))
            phases.append(phase_data('final',list(range(2049,16385))))
            final,peak2=collect(pool,final_task,SPEC['q'],start,'signed_prime_final_checked')
        for name,b in fixed.items():
            if (OUT/name).read_bytes()!=b:
                raise ValueError('final outcome cannot tune '+name)
        complete=SEARCH.join_data(*(json.loads((OUT/(p+'_data.json')).read_text()) for p in ('discovery','adaptation','final')))
        actual=SEARCH.data_map(complete)
        known=json.loads((PRIOR.OUT/'original_source_binding.json').read_text())['values']
        for old in known:
            if Q(actual[old['k']][0],complete['denominator'])!=Q(old['actual_signed_target']):
                raise ValueError('saved original source target agreement')
        write(OUT/'original_source_binding.json',dict(source_family='N15k,y16k,p3,q5,r1,j1',
              uniform_identity_reference='../source_snapshot/MOBIUS_PRIME_ORBIT_REVIEW_072.txt',
              saved072_values_compared=len(known),old_science_replayed=False,
              necessary_family_only=True,uniform_head_bound_proved=False,RH_proved=False))
        for name,b in frozen.items():
            if (ROOT/name).read_bytes()!=b:
                raise ValueError('preserve073 '+name)
        if validate_parent()!=counts:
            raise ValueError('inherited source chain changed')
        parent_peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        worker_peak=max(r['worker_peak_rss_kib'] for r in candidates+final)
        conservative=1024*(parent_peak+SPEC['workers']*worker_peak)
        if conservative>SPEC['maximum_aggregate_bytes']:
            raise MemoryError('073 conservative process peak sum')
        report=dict(status='SIGNED_PRIME_STORAGE_CANDIDATES_EVALUATED_UNIFORM_DRIFT_OPEN',
            candidates=candidates,final=final,source_phases=phases,
            candidate_programs=len(candidates),baseline_programs=len(candidates),
            finite_final_inequalities=2*len(candidates)*(16384-2048),
            final_candidate_survivors=sum(r['learned_status']=='VERIFIED_ON_FINITE_DOMAIN' for r in final),
            final_candidate_refutations=sum(r['learned_status']=='REFUTED' for r in final),
            new_synthetic_tests=sum(r['unique_new_synthetic_tests'] for r in receipts),
            test_invocations=sum(sum(x['tests'] for x in r['runs']) for r in receipts),
            development_operations=development,
            producer_operations=sum(p['producer_operations'] for p in phases)+sum(r['producer_operations'] for r in candidates),
            checker_operations=sum(p['checker_operations'] for p in phases)+sum(r['checker_operations'] for r in candidates+final),
            elapsed_seconds=time.monotonic()-start,parent_peak_rss_kib=parent_peak,largest_worker_peak_rss_kib=worker_peak,
            sampled_parallel_rss_peak_bytes=max(peak1,peak2),conservative_sum_process_peaks_bytes=conservative,
            largest_prospective_bytes=max([p['prospective_bytes'] for p in phases]+[r['prospective_bytes'] for r in candidates]),
            prior_frozen_counts=counts,new_frozen_files=len(FILES),old_science_or_suites_replayed=False,hashes_used=False,
            final_data_excluded_from_adaptation=True,uniform_domination_proved=True,uniform_recurrence_proved=False,
            uniform_head_bound_proved=False,uniform_core_bound_proved=False,RH_proved=False,RH_refuted=False)
        write(OUT/'report.json',report)
        write(OUT/'mechanism_feedback.json',dict(previous_goal_turn='072 progress',current_goal_turn='073 new signed states and automatic auxiliary recurrence discovery',
            learned=['rational square directions','nonnegative weights','finite drift constants','counterexample-guided training scales'],
            supplied=['prime/smooth source semantics','nonnegative square domination','conditional all-integer telescoping'],
            final_candidate_refutations=report['final_candidate_refutations'],final_candidate_survivors=report['final_candidate_survivors'],
            next_priority='prove a surviving full signed drift or use exact violations to change arithmetic state/recurrence grammar; do not merely inflate C',
            main_open_leaf='uniform indefinite quadratic drift of actual prime/composite states',uniform_recurrence_proved=False,RH_proved=False))
        write(OUT/'next_search_input.json',dict(schema='signed-prime-storage-obligation-v1',source=SPEC['source'],
            candidate_files=[r['file'] for r in candidates],final_files=['final_'+q.replace('/','_')+'.json' for q in SPEC['q']],
            assertion='F(k)-F(floor(k/2))<=C for every integer k>=2',
            hypotheses='actual ordinary mu; complete sectors and changing smooth cutoffs; fixed rational candidate coefficients',
            paid='F>=Z^2/k^q and actual base E(1)',unpaid='all-scale signed drift; broader whole-head/core/RH transfer',
            counterexample_scope='refutes recorded candidate with its fixed C, not all constants or RH',
            alternate_rules='MOBIUS_PRIME_BLOCK_REVIEW_073.txt: exact prime stencils and complete common-cell/prime correlations',
            uniform_recurrence_proved=False,RH_proved=False))
        emit('signed_prime_storage_complete',elapsed_seconds=report['elapsed_seconds'],survivors=report['final_candidate_survivors'],refuted=report['final_candidate_refutations'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',dict(type=type(exc).__name__,message=str(exc),RH_proved=False))
        raise


if __name__=='__main__':
    main()
