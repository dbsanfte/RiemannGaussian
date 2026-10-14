"""Post-pilot fixed-operator lower witnesses; no SDP or operator retuning."""
import os
for key in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS'):os.environ[key]='1'
import json
import resource
import time
import traceback
from fractions import Fraction as Q
import run_mobius_coupled_square_084 as RUN
import mobius_square_witness_084 as SEARCH
import check_mobius_square_witness_084 as CHECK
from run_fractional_prime_kernel_051 import write,emit

FILES=['mobius_square_witness_084.py','check_mobius_square_witness_084.py',
       'test_mobius_square_witness_084.py','mobius_square_witness_084_development.json','run_mobius_square_witness_084.py']
SPEC=dict(schema='fixed-operator-Boolean-obstruction-v1',seed=20261011085,
          starts='all plus; four largest-eigenvector signs; sixteen seeded random signs',
          max_coordinate_flips='8*complete_effective_dimension per start',max_effective_dimension=512,
          selection='every frozen084 operator at every registered084 new geometry, irrespective of main outcome',
          scope='post hoc method diagnostic on already registered cases; not fresh validation',
          purpose='lower-bound every PSD-completed Boolean price for the fixed operator; test whether any such factor can meet the frozen finite growth hypothesis',
          actual_unknown_Mobius_signs_used=False,operator_retuning=False,SDP_replayed=False,
          whole_theta_grammar_obstruction=False,uniform_obstruction_proved=False,RH_proved=False,hashes_used=False)


def task(item):
    start=time.monotonic();c,u=item;row={};uid=c['id']+'_'+str(u)
    try:
        row=SEARCH.propose(c['program'],u,seed=SPEC['seed'])
        row['admission']=CHECK.verify(c['program'],u,c['outer_certificate'],row['certificate'])
        if row['admission']['status']!='VERIFIED_FINITE_FIXED_OPERATOR_SQUARE_LOWER_BOUND':raise ValueError(str(row['admission']))
        lower=row['certificate']['lower_bound']
        row['lower_bound_over_u']=str(Q(lower)/u)
        row['growth_obstructions']=[dict(**h,impossible_for_any_square_with_frozen_constant=not RUN.TARGET.exact_power_comparison(lower,u,h['j'],h['constant']))
                                   for h in c['calibrated_growth_hypotheses']]
        upper=next(r for r in json.loads((RUN.OUT/('validation_'+c['id']+'.json')).read_text())['rows']if r['u']==u)
        if upper['status']=='EXACT_SQUARE_PROPOSAL':
            row['verified_upper_bound']=upper['certificate']['price']
            if Q(lower)>Q(row['verified_upper_bound']):raise ValueError('exact fixed witness exceeds admitted upper')
        row['status']='EXACT_FIXED_OPERATOR_OBSTRUCTION_WITNESS'
    except Exception as exc:row.update(status='WITNESS_FAILED',error=str(exc),traceback=traceback.format_exc())
    row.update(id=uid,candidate_id=c['id'],u=u,elapsed_seconds=time.monotonic()-start,
               worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(RUN.OUT/('witness_'+uid+'.json'),row)
    return {k:row[k]for k in ['id','candidate_id','u','status','elapsed_seconds','worker_peak_rss_kib']}


def main():
    start=time.monotonic();out=RUN.OUT
    if not (out/'report.json').exists():raise ValueError('main science must finish before diagnostic workers start')
    counts=RUN.validate_parent()
    for name in RUN.FILES:
        if (RUN.ROOT/name).read_bytes()!=(out/'source_snapshot'/name).read_bytes():raise ValueError('preserve main084 '+name)
    snap=out/'witness_source_snapshot';snap.mkdir()
    for name in FILES:(snap/name).write_bytes((RUN.ROOT/name).read_bytes())
    write(out/'witness_protocol.json',dict(**SPEC,source_files=FILES,workers=3,native_threads=1,
                                        module_seconds=7200,max_aggregate_bytes=16*1024**3))
    candidates=json.loads((out/'frozen_candidates.json').read_text())['candidates']
    us=json.loads((out/'validation_draw.json').read_text())['parents']
    roster=[(c,u)for c in candidates for u in us]
    write(out/'witness_frozen_tasks.json',dict(tasks=[dict(candidate_id=c['id'],u=u)for c,u in roster],
                                            all_candidates_and_parents_retained=True))
    outcomes=RUN.PRIOR.pool_tasks(task,roster,start,'fixed_operator_square_obstruction_witnesses')
    rows=[json.loads((out/('witness_'+r['id']+'.json')).read_text())for r in outcomes]
    good=[r for r in rows if r['status']=='EXACT_FIXED_OPERATOR_OBSTRUCTION_WITNESS']
    for name in FILES:
        if (RUN.ROOT/name).read_bytes()!=(snap/name).read_bytes():raise ValueError('frozen witness source changed '+name)
    if RUN.validate_parent()!=counts:raise ValueError('prior evidence changed')
    report=dict(status='COMPLETE_FIXED_OPERATOR_SQUARE_OBSTRUCTION_DIAGNOSTIC',tasks=len(roster),admitted=len(good),outcomes=outcomes,
                growth_obstructions_by_j=[dict(j=j,tested=len(good),obstructed=sum(t['impossible_for_any_square_with_frozen_constant']for r in good for t in r['growth_obstructions']if t['j']==j))
                                          for j in RUN.SPEC['diagnostic_exponent_parameters']],
                elapsed_seconds=time.monotonic()-start,sampled_aggregate_peak_rss_bytes=RUN.PRIOR._PEAK,
                conservative_process_peak_sum_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+
                    3*max([r['worker_peak_rss_kib']for r in outcomes]+[0])),
                search_operations=sum(r.get('ops',0)for r in rows),checker_operations=sum(r['admission']['ops']for r in good),
                source_bytes_preserved=True,posthoc_on_existing_geometries=True,fixed_operator_only=True,
                actual_signed_drift_lower_bound_proved=False,whole_theta_grammar_obstruction=False,uniform_obstruction_proved=False,RH_proved=False)
    write(out/'witness_report.json',report);RUN.PRIOR.stage_check(start,[os.getpid()])
    emit({k:v for k,v in report.items()if k!='outcomes'})


if __name__=='__main__':main()
