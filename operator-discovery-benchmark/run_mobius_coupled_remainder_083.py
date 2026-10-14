"""New exact residual targets on already-frozen winners and validation scales."""
import json
import os
import resource
import time
import traceback
from fractions import Fraction as Q
import run_mobius_coupled_completion_083 as MAIN
import mobius_coupled_remainder_083 as SEARCH
import check_mobius_coupled_remainder_083 as CHECK
from run_fractional_prime_kernel_051 import write,emit

FILES=['mobius_coupled_remainder_083.py','check_mobius_coupled_remainder_083.py',
       'test_check_mobius_coupled_remainder_083.py','mobius_coupled_remainder_checker_083_development.json',
       'MOBIUS_COUPLED_REMAINDER_CHECK_SCOPE_083.txt','run_mobius_coupled_remainder_083.py']


def task(item):
    candidate,u=item;started=time.monotonic()
    row=dict(id=candidate['id']+'_'+str(u),candidate_id=candidate['id'],u=u)
    try:
        model=MAIN.SEARCH.build_model(candidate['program'],u)
        certificate,diagnostics=SEARCH.remainder_certificate(model)
        admission=MAIN.require(CHECK.verify_certificate(candidate['program'],u,candidate['outer_certificate'],certificate),
                               'VERIFIED_FINITE_COUPLED_REMAINDER_UPPER_BOUND')
        for key in ('signed_trace','anchor_constant','anchor_composite_absolute_price','composite_composite_absolute_price'):
            if diagnostics[key]!=admission[key]:raise ValueError('independent exact remainder diagnostic '+key)
        outer=Q(candidate['outer_certificate']['uniform_bound_coefficient'])
        row.update(status='VERIFIED',certificate=certificate,diagnostics=diagnostics,admission=admission,
                   paid_outer_bound=str(outer*u),combined_valid_drift_bound=str(outer*u+Q(certificate['price'])),
                   remainder_price_over_u=str(Q(certificate['price'])/u),remainder_price_over_u2=str(Q(certificate['price'])/(u*u)),
                   ops=model['meter'].ops,prospective_peak_bytes=model['meter'].peak_bytes)
    except Exception as exc:row.update(status='TASK_FAILED',error=str(exc),traceback=traceback.format_exc())
    row.update(elapsed_seconds=time.monotonic()-started,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(MAIN.OUT/('remainder_'+row['id']+'.json'),row)
    return {k:row[k]for k in ('id','status','elapsed_seconds','worker_peak_rss_kib')}


def main():
    started=time.monotonic();counts=MAIN.validate_parent()
    for name in MAIN.FILES:
        if (MAIN.ROOT/name).read_bytes()!=(MAIN.OUT/'source_snapshot'/name).read_bytes():raise ValueError('preserve main083 '+name)
    snapshot=MAIN.OUT/'remainder_source_snapshot';snapshot.mkdir()
    for name in FILES:(snapshot/name).write_bytes((MAIN.ROOT/name).read_bytes())
    selected=json.loads((MAIN.OUT/'frozen_candidates.json').read_text())['candidates']
    selected=[c for c in selected if 'outer_certificate'in c]
    us=json.loads((MAIN.OUT/'validation_draw.json').read_text())['parents']
    write(MAIN.OUT/'remainder_protocol.json',dict(source_files=FILES,selected_ids=[c['id']for c in selected],parents=us,
          formula='R=A-A_outer-G; actual DeltaE=mu^T A_outer mu+mu^T R mu',
          full_raw_outer_block_not_effective_anchor_subtraction=True,new_target_not_old_science_replay=True,
          all_selected_proof_family_winners_included=True,no_reselection=True,unknown_composite_signs_used=False,
          workers=MAIN.SPEC['workers'],max_aggregate_bytes=MAIN.SPEC['max_aggregate_bytes'],module_seconds=MAIN.SPEC['module_seconds'],
          uniform_remaining_bound_proved=False,uniform_original_source_bound_proved=False,RH_proved=False))
    outcomes=MAIN.pool_tasks(task,[(c,u)for c in selected for u in us],started,'new_signed_remainder')
    rows=[json.loads((MAIN.OUT/('remainder_'+r['id']+'.json')).read_text())for r in outcomes]
    for name in FILES:
        if (MAIN.ROOT/name).read_bytes()!=(snapshot/name).read_bytes():raise ValueError('preserve residual083 '+name)
    if MAIN.validate_parent()!=counts:raise ValueError('older provenance changed')
    good=[r for r in rows if r['status']=='VERIFIED']
    report=dict(status='COMPLETE_EXACT_REMAINDER_COMPILATION',rows=rows,outcomes=outcomes,
                parents=us,candidate_ids=[c['id']for c in selected],admitted_rows=len(good),
                elapsed_seconds=time.monotonic()-started,sampled_aggregate_peak_rss_bytes=MAIN._PEAK,
                conservative_process_peak_sum_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+
                    MAIN.SPEC['workers']*max([r['worker_peak_rss_kib']for r in outcomes]+[0])),
                constructor_operations=sum(r['ops']for r in good),independent_checker_operations=sum(r['admission']['ops']for r in good),
                uniform_remaining_bound_proved=False,uniform_original_source_bound_proved=False,RH_proved=False,hashes_used=False)
    write(MAIN.OUT/'remainder_report.json',report);MAIN.stage_check(started,[os.getpid()])
    emit({k:v for k,v in report.items()if k not in ('rows','outcomes')})


if __name__=='__main__':main()
