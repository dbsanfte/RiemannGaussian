"""Promote a saved auxiliary-improvement lead to an entirely fresh finite audit."""
import os
os.environ['OPENBLAS_NUM_THREADS']='2'
os.environ['OMP_NUM_THREADS']='2'
from copy import deepcopy
from fractions import Fraction as Q
import multiprocessing as mp
from pathlib import Path
import resource
import time

import run_floor_residual_prime_047 as PRIOR

ROOT=Path(__file__).resolve().parent
OUT=PRIOR.OUT/'mechanism_followup_001'
FRESH_PARENTS=(227,251,293)
FILES=['run_floor_residual_prime_promotion_048.py',
       'test_floor_residual_prime_promotion_048.py',
       'floor_residual_prime_promotion_048_development.json',
       'floor_residual_prime_promotion_protocol_048.txt']
read,write,emit=PRIOR.read,PRIOR.write,PRIOR.emit


def promote(rows):
    if any(r.get('training_parents')!=list(PRIOR.S.TRAIN_PARENTS) or
           r.get('final_observations_used') is not False for r in rows):
        raise ValueError('saved training evidence only')
    eligible=[r for r in rows if r['finite_failure_count']==0 and Q(r['tau'])>0
              and r['helpful_auxiliary_count']>0]
    if not eligible:
        return None
    def key(r):
        return (-Q(r['request']['target']['eta']),-r['helpful_auxiliary_count'],
                Q(r['request']['argument']['recurrence']['rho']),r['complexity'],
                Q(r['request']['target']['A']),r['id'])
    return deepcopy(min(eligible,key=key))


def configured_runner():
    runner=PRIOR.CAP.isolated('run_floor_residual_prime_047.py','prime_promotion_runner_048')
    search=PRIOR.CAP.isolated('floor_residual_prime_search_047.py','prime_promotion_search_048')
    if set(search.levels(FRESH_PARENTS)) & set(search.levels(search.FINAL_PARENTS)):
        raise ValueError('fresh validation parents and children required')
    search.FINAL_PARENTS=FRESH_PARENTS
    runner.S=search
    return runner


def validate_parent():
    counts=PRIOR.validate_parent()
    files=list((PRIOR.OUT/'source_snapshot').iterdir())
    if len(files)!=len(PRIOR.FILES) or any((ROOT/p.name).read_bytes()!=p.read_bytes() for p in files):
        raise ValueError('preserve frozen047 source')
    if not (PRIOR.OUT/'report.json').exists():
        raise ValueError('047 audit must finish before this fresh application')
    return counts+[len(files)]


def main():
    started=time.monotonic()
    if OUT.exists():raise FileExistsError('preserve mechanism followup')
    counts=validate_parent()
    receipt=read(ROOT/'floor_residual_prime_promotion_048_development.json')
    if not PRIOR.PREV.NUM.R.passing_receipt(receipt):raise ValueError('passing new selection tests')
    snapshots={name:(ROOT/name).read_bytes() for name in FILES}
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,data in snapshots.items():(OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'protocol.json',dict(schema='prime-mechanism-promotion-v1',
            training_source=str((PRIOR.OUT/'search.json').relative_to(ROOT)),
            ranking='finite pass; larger eta; more helpful auxiliary increments; rho; complexity; A; ordinal',
            fresh_parents=list(FRESH_PARENTS),fresh_both_parities=True,
            original_search_and_selection_changed=False,training_norms_rerun=False,
            previous_heldout_scores_used_to_select=False,workers=2,
            memory_limit_bytes=16*1024**3,prior_frozen_source_counts=counts,hashes_used=False))
        # Select solely from frozen training rows. Old held-out observations
        # and report contents never enter this selector.
        saved=read(PRIOR.OUT/'search.json')
        selected=promote(saved['rows'])
        eligible=sum(r['finite_failure_count']==0 and Q(r['tau'])>0 and r['helpful_auxiliary_count']>0 for r in saved['rows'])
        del saved
        if selected is None:raise ValueError('no finite auxiliary-improvement lead')
        write(OUT/'selected_argument.json',dict(row=selected,eligible_training_arguments=eligible))
        emit('mechanism_lead_frozen',id=selected['id'],family=selected['family'],prime=selected['prime'],
             tau=selected['tau'],d=selected['d'],helpful_training_pairs=selected['helpful_auxiliary_count'])
        runner=configured_runner()
        batch=runner.compile_final([selected],progress=emit)
        write(OUT/'final_program_batch.json',batch)
        reserve=PRIOR.CAP.memory_preflight(batch['programs'])
        emit('fresh_audit_started',programs=len(batch['programs']),aggregate_memory_reserve_bytes=reserve)
        rows=[]
        with mp.get_context('fork').Pool(2) as pool:
            for row in pool.imap_unordered(PRIOR.CAP.audit_one,[dict(program=p,H=runner.S.FINAL_H) for p in batch['programs']]):
                write(OUT/('norm_%03d.json'%(len(rows)+1)),row);rows.append(row)
                emit('fresh_norm_verified',completed=len(rows),total=len(batch['programs']),id=row['id'])
        by_id={r['id']:r for r in rows}
        if len(by_id)!=len(rows) or set(by_id)!={p['id'] for p in batch['programs']}:
            raise ValueError('complete fresh exact norm coverage')
        assessment=runner.assess([selected],batch['cases'],by_id)
        write(OUT/'assessment.json',dict(rows=assessment,uniform_recurrence_proved=False))
        refuted=any(c['status']=='refuted_at_this_pair' for c in assessment)
        proved_improvements=sum(c['auxiliary_improves_increment_proved'] for c in assessment)
        feedback=dict(schema='prime-auxiliary-mechanism-feedback-v1',
            parent=str((PRIOR.OUT/'next_search_input.json').relative_to(ROOT)),
            promoted_argument=selected,exact_argument=batch['arguments'][0],finite_cases=assessment,
            recurrence_status='REFUTED' if refuted else 'OPEN',
            arithmetic_source_unchanged=True,uniform_bound_proved=False,
            next_search_target=('change the refuted fixed recurrence using its exact counterexample' if refuted else
                'uniformly control the signed quadratic scale increment for both integer children'),
            next_productions=[dict(kind='rational_state_predictor',
                identity='z_child=B z_parent+xi; retain 2<Bz_parent,Qxi>+<xi,Qxi>',
                paid_precondition='B^T Q B<=rho Q',
                missing='uniform ordinary-Mobius signed work bound including complete tail'),
                dict(kind='drift_aware_scale_potential',
                missing='keep exact beta ceiling jumps; do not replace them by smooth derivatives')],
            base_obligation='every N in[32,63], with complete-domain norms; three training probes do not discharge it',
            noncircular_proof_required=True,RH_proved=False,RH_refuted=False)
        write(OUT/'next_search_input.json',feedback)
        report=dict(status='PRIME_AUXILIARY_MECHANISM_AUDITED_UNIFORM_INCREMENT_OPEN',
            selected_argument=selected,eligible_training_arguments=eligible,
            fresh_parents=list(FRESH_PARENTS),source_constructions=len(batch['constructions']),
            norm_certificates=len(rows),finite_recurrence_pairs=len(assessment),
            finite_status_counts={label:sum(c['status']==label for c in assessment) for label in
                ('verified_at_this_pair','refuted_at_this_pair','unresolved_interval')},
            proved_auxiliary_improvements=proved_improvements,
            training_search_or_norms_rerun=False,prior_norms_rerun=False,
            source_operations=batch['source_operations'],prime_compilation_counts=batch['prime_counts'],
            prime_checker_operations=batch['prime_checker_operations'],
            norm_producer_operations=sum(r['producer_counts']['operations'] for r in rows),
            norm_checker_operations=sum(r['checker_operations'] for r in rows),
            aggregate_memory_reserve_bytes=reserve,
            parent_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            largest_individual_worker_rss_kib=max(r['worker_peak_rss_kib'] for r in rows),
            elapsed_seconds=time.monotonic()-started,prior_frozen_source_counts=counts,
            new_frozen_source_count=len(FILES),uniform_signed_bound_proved=False,RH_proved=False,RH_refuted=False)
        validate_parent()
        if any((ROOT/n).read_bytes()!=data for n,data in snapshots.items()):raise ValueError('frozen048 changed')
        write(OUT/'report.json',report)
        emit('completed',status=report['status'],elapsed_seconds=report['elapsed_seconds'],
             finite_status_counts=report['finite_status_counts'],proved_auxiliary_improvements=proved_improvements)
    except Exception as error:
        write(OUT/'failure.json',dict(type=type(error).__name__,message=str(error),elapsed_seconds=time.monotonic()-started))
        raise


if __name__=='__main__':main()
