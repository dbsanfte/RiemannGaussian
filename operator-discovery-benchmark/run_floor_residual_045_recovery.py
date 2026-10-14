"""Resume the frozen 045 selection after a support-cap-only compilation stop."""
import multiprocessing as mp
from pathlib import Path
import resource
import time

import floor_residual_capacity_045 as C
import run_floor_residual_045 as R

ROOT = Path(__file__).resolve().parent
FAILED = R.OUT
OUT = FAILED / 'recovery-001'
FILES = ['floor_residual_capacity_045.py', 'run_floor_residual_045_recovery.py',
         'test_floor_residual_capacity_045.py', 'floor_residual_capacity_045_development.json',
         'floor_residual_recovery_protocol_045.txt']
read, write, emit = R.read, R.write, R.emit


def validate_frozen():
    prior = R.validate_parent()
    files = list((FAILED / 'source_snapshot').iterdir())
    if len(files) != len(R.FILES) or any((ROOT/p.name).read_bytes() != p.read_bytes() for p in files):
        raise ValueError('preserve all frozen045 sources')
    failure = read(FAILED / 'failure.json')
    if failure['type'] != 'ValueError' or failure['message'] != 'support cap':
        raise ValueError('expected support-only compilation failure')
    if (FAILED / 'final_program_batch.json').exists() or list(FAILED.glob('norm_*.json')):
        raise ValueError('recovery expects no prior final norm application')
    return prior + [len(files)]


def main():
    started = time.monotonic()
    if OUT.exists():
        raise FileExistsError('preserve existing recovery')
    parent_counts = validate_frozen()
    receipt = read(ROOT / 'floor_residual_capacity_045_development.json')
    if not R.passing_receipt(receipt):
        raise ValueError('passing new capacity regressions required')
    snapshots = {name: (ROOT/name).read_bytes() for name in FILES}
    search = read(FAILED / 'search.json')
    gates = read(FAILED / 'presearch_proofs.json')
    frozen = read(FAILED / 'run_spec.json')['grammar']
    if (read(FAILED/'selected_families.json')['rules'] != search['selections'] or
            search['final_observations_used_in_selection'] or
            search['training_parents'] != list(R.S.TRAIN_PARENTS)):
        raise ValueError('unchanged frozen selection and training domain required')
    OUT.mkdir()
    (OUT/'source_snapshot').mkdir()
    for name, data in snapshots.items():
        (OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'run_spec.json', dict(schema='drift-capacity-recovery-v1',
            authoritative_search=str((FAILED/'search.json').relative_to(ROOT)),
            support_limit=C.SUPPORT_LIMIT, prior_support_limit=2048,
            resource_change_only=True, source_formulas_and_bounds_changed=False,
            final_parents=list(R.S.FINAL_PARENTS), final_H=R.S.FINAL_H,
            search_rerun=False, proof_gates_rerun=False, prior_final_norms=0,
            workers=2, aggregate_memory_limit_bytes=16*1024**3,
            unchanged_guards=dict(index=4096, input_bits=4096, intermediate_bits=8192),
            frozen_source_counts=parent_counts+[len(FILES)], hashing_used=False,
            reason='selected legacy mu-convolution auxiliary has dense support beyond2048',
            RH_proved=False))
        emit('recovery_frozen', support_limit=C.SUPPORT_LIMIT, search_rerun=False)
        batch = C.compile_batch(search, R.S.FINAL_PARENTS)
        write(OUT/'final_program_batch.json', batch)
        queue = R.argument_queue(batch['rules'])
        write(OUT/'global_bound_arguments.json', queue)
        aggregate = C.memory_preflight(batch['programs'])
        maximum_support = max(len(p['coefficients'])+len(p['steps']) for p in batch['programs'])
        tasks = [dict(program=p, H=0 if p['constant']=='0' and not p['coefficients'] and not p['steps'] else R.S.FINAL_H)
                 for p in batch['programs']]
        emit('whole_domain_audit_started', programs=len(tasks), maximum_support=maximum_support,
             aggregate_memory_reserve_bytes=aggregate)
        rows = []
        with mp.get_context('fork').Pool(2) as pool:
            for row in pool.imap_unordered(C.audit_one, tasks):
                artifact = 'norm_%03d.json' % (len(rows)+1)
                write(OUT/artifact, row)
                rows.append(dict(**row, artifact=artifact))
                emit('norm_verified', completed=len(rows), total=len(tasks), id=row['id'],
                     interval=[float(v) for v in R.AUDIT.interval(row)])
        by_id = {row['id']: row for row in rows}
        if len(by_id) != len(rows) or set(by_id) != {p['id'] for p in batch['programs']}:
            raise ValueError('complete independent norm coverage')
        cases = [R.AUDIT.analyze_case(case, by_id) for case in batch['cases']]
        write(OUT/'assessment.json', dict(cases=cases, uniform_bound_proved=False, RH_proved=False))
        write(OUT/'next_search_input.json', dict(schema='moving-profile-bound-feedback-v1',
            authoritative_parent=str((R.PARENT/'next_search_input.json').relative_to(ROOT)),
            current_results=str(OUT.relative_to(ROOT)),
            global_arguments=str((OUT/'global_bound_arguments.json').relative_to(ROOT)),
            generated_signed_moment_mixtures=True, proof_obstructions_applied_before_scores=True,
            candidates=[dict(rule=r, finite_cases=[c for c in cases if c['rule']==r['id']]) for r in batch['rules']],
            next_target='bound joint critical-line transfer and truncation with signed cross terms; discharge exact uniform budgets',
            forbidden_providers=['RH', 'RH-equivalent Mertens bound without independent proof',
                                 'finite trends', 'coefficient control alone'],
            harmonic_component='explicit unconditional envelopes and sufficient level thresholds for supported profiles',
            separate_bias_and_truncation_integrability='OPEN; introduced poles may cancel only jointly',
            original_F_and_centered_mobius_obligations='OPEN', uniform_signed_control_proved=False,
            RH_proved=False, RH_refuted=False))
        report = dict(status='MOVING_SIGNED_PROFILES_AUDITED_JOINT_BOUND_OPEN',
            families=len(frozen['recipes']), new_families=frozen['new_family_count'],
            signed_profile_count=frozen['profile_count'], gated_rules=gates['rule_count'],
            refuted_rules_before_scores=gates['entirely_refuted_rules'],
            rejected_bound_pairs_before_scores=gates['rejected_bound_pairs'],
            legacy_training_rows_reused=search['legacy_training_rows_reused'],
            old_training_norms_recomputed=0, search_rerun=False,
            training_matches=search['finite_log_bound_matches'],
            exact_vector_price_cache_hits=search['exact_vector_price_cache_hits'],
            distinct_new_training_vectors=search['distinct_new_training_vectors'],
            selected_rules=batch['rules'], whole_domain_certificates=len(rows), final_cases=len(cases),
            final_bound_status_counts={label:sum(c['logarithmic_forcing_status']==label for c in cases)
                for label in ('verified_at_this_support','refuted_at_this_support','unresolved_interval')},
            signed_mechanism_counts={kind:{label:sum(c[kind]['mechanism']==label for c in cases)
                for label in sorted({c[kind]['mechanism'] for c in cases})} for kind in ('auxiliary','refinement')},
            global_argument_supported_rules=sum(r['verification'] is not None for r in queue['rows']),
            bound_argument_allocations=queue['allocation_count'], global_bound_proved=False,
            proof_gate_operations={k:gates[k] for k in ('producer_operations','checker_operations',
                'drift_certificate_operations','cutoff_operations','cutoff_replay_operations')},
            generation_counts=frozen['generation_counts'], search_counts=search['counts'],
            search_drift_counts=search['drift_counts'], compiler_counts=batch['compiler_counts'],
            compiler_drift_counts=batch['drift_counts'], source_replay_operations=batch['source_replay_operations'],
            finite_argument_operations=batch['argument_operations'],
            global_argument_operations=queue['operations']+queue['replay_operations'],
            norm_producer_operations=sum(r['producer_counts']['operations'] for r in rows),
            norm_checker_operations=sum(r['checker_operations'] for r in rows),
            aggregate_memory_reserve_bytes=aggregate, maximum_support=maximum_support,
            parent_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            largest_individual_worker_rss_kib=max(r['worker_peak_rss_kib'] for r in rows),
            prior_frozen_file_counts=parent_counts, new_frozen_file_count=len(FILES),
            recovery_elapsed_seconds=time.monotonic()-started,
            initial_attempt_elapsed_seconds=read(FAILED/'failure.json')['elapsed_seconds'],
            initial_aborted_compilation_operations='not captured before failure; excluded from reported proxy totals',
            capacity_development_receipt=receipt,
            development_receipts={n:read(ROOT/n) for n in R.RECEIPTS}, RH_proved=False, RH_refuted=False)
        validate_frozen()
        if any((ROOT/n).read_bytes()!=data for n,data in snapshots.items()):
            raise ValueError('frozen recovery source changed')
        write(OUT/'report.json', report)
        emit('completed', status=report['status'], elapsed_seconds=report['recovery_elapsed_seconds'],
             final_bound_status_counts=report['final_bound_status_counts'], signed_mechanism_counts=report['signed_mechanism_counts'])
    except Exception as error:
        write(OUT/'failure.json', dict(type=type(error).__name__, message=str(error),
                                     elapsed_seconds=time.monotonic()-started))
        raise


if __name__ == '__main__':
    main()
