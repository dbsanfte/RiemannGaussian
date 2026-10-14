"""Adversarial exact transition audit of the unchanged048/049 argument.

All case proposals and the six-case work limit are frozen before evaluation.
Stop at the first rigorously refuted pair. Only unresolved intervals trigger
the predeclared horizon refinement. Neither the operator nor the constants fit.
"""
from copy import deepcopy
from fractions import Fraction as Q
import multiprocessing as mp
from pathlib import Path
import resource
import time

import certify_prime_potential_base_049 as BASE
import floor_residual_transition_search_050 as SEARCH
import check_floor_residual_transition_source_050 as SOURCE_CHECK
import floor_residual_capacity_050 as CAP
import floor_residual_prime_work_guard_050 as WORK

ROOT = Path(__file__).resolve().parent
OUT = BASE.OUT/'transition_followup_001'
CASE_LIMIT = 6
HORIZONS = (262144, 1048576)
FILES = ['floor_residual_transition_search_050.py', 'test_floor_residual_transition_search_050.py',
    'floor_residual_transition_search_050_development.json',
    'check_floor_residual_transition_source_050.py', 'test_check_floor_residual_transition_source_050.py',
    'check_floor_residual_transition_source_050_development.json',
    'floor_residual_capacity_050.py', 'test_floor_residual_capacity_050.py',
    'floor_residual_capacity_050_development.json',
    'floor_residual_prime_work_guard_050.py', 'test_floor_residual_prime_work_guard_050.py',
    'floor_residual_prime_work_guard_050_development.json', 'PRIME_WORK_REDUCTION_REVIEW_050.txt',
    'run_floor_residual_transitions_050.py', 'test_floor_residual_transition_runner_050.py',
    'floor_residual_transition_runner_050_development.json', 'floor_residual_transition_protocol_050.txt',
    'floor_residual_transition_preflight_050_failure.json']
read, write, emit = BASE.read, BASE.write, BASE.emit
AUDIT = BASE.P.PRIOR.AUDIT


def verify_receipt(receipt):
    if receipt.get('schema') == 'floor-residual-prime-work-guard-050-development-v1':
        if (type(receipt.get('invocations')) is not int or receipt['invocations'] != 1 or
                type(receipt.get('tests_run')) is not int or receipt['tests_run'] <= 0 or
                receipt.get('errors') != 0 or receipt.get('failures') != 0 or
                receipt.get('failed_attempts') != [] or
                any(receipt.get(key) is not False for key in
                    ('actual_norms_evaluated', 'scientific_candidates_applied', 'source_values_evaluated'))):
            raise ValueError('passing source-free guard receipt required')
        return receipt
    return AUDIT.verify_development_receipt(receipt)


def validate_parent():
    counts = BASE.validate_parent()
    snapshots = list((BASE.OUT/'source_snapshot').iterdir())
    if len(snapshots) != 1 or any((ROOT/f.name).read_bytes() != f.read_bytes() for f in snapshots):
        raise ValueError('preserve frozen049 source')
    if read(BASE.OUT/'report.json')['base_status'] != 'PAID_FINITE_EXACT':
        raise ValueError('unchanged selected finite base required')
    return counts+[len(snapshots)]


def interval(row):
    v = row['verification']
    if v['verified'] is not True or v['all_domain_included'] is not True or v['convergence_proved'] is not False:
        raise ValueError('independently admitted complete fixed norm required')
    lo, hi = CAP.parse_exact(v['global_fixed_norm_squared_lower']), CAP.parse_exact(v['global_fixed_norm_squared_upper'])
    if not 0 <= lo <= hi:
        raise ValueError('ordered nonnegative exact norm bracket')
    return lo, hi


def serialized(pair):
    return dict(lower=CAP.format_exact(pair[0]), upper=CAP.format_exact(pair[1]),
                decimal_lower=float(pair[0]), decimal_upper=float(pair[1]))


def assess(selected, case, state_norms):
    req = selected['request']; rho = Q(req['argument']['recurrence']['rho'])
    C, eta = req['argument']['recurrence']['C'], req['target']['eta']
    tau = Q(selected['tau'])
    if tau < 0 or not 0 <= rho < 1:
        raise ValueError('nonnegative potential and contractive recurrence')
    energies, h_norms, targets = {}, {}, {}
    for N in (case['N'], case['child']):
        h, v = (interval(state_norms[N][name]) for name in ('h', 'v'))
        energy = h[0]+tau*v[0], h[1]+tau*v[1]
        energies[N], h_norms[N] = energy, h
        target = AUDIT.log_bound_interval(N, req['target']['A'], eta)
        tlo, thi = Q(target['lower']), Q(target['upper'])
        def status(pair):
            return 'verified_at_this_support' if pair[1] <= tlo else 'refuted_at_this_support' if pair[0] > thi else 'unresolved_interval'
        targets[str(N)] = dict(potential=serialized(energy), target=target,
            potential_target_status=status(energy), whole_h_target_status=status(h), whole_h_norm=serialized(h))
    parent, child = energies[case['N']], energies[case['child']]
    delta = child[0]-rho*parent[1], child[1]-rho*parent[0]
    forcing = AUDIT.log_bound_interval(case['N'], C, eta)
    status = ('verified_at_this_pair' if delta[1] <= Q(forcing['lower']) else
              'refuted_at_this_pair' if delta[0] > Q(forcing['upper']) else 'unresolved_interval')
    hparent, hchild = h_norms[case['N']], h_norms[case['child']]
    hdelta = hchild[0]-rho*hparent[1], hchild[1]-rho*hparent[0]
    return dict(N=case['N'], r=case['r'], child=case['child'], status=status,
        potential_increment=serialized(delta), forcing=forcing, support_bounds=targets,
        h_only_increment=serialized(hdelta), auxiliary_improves_increment_proved=delta[1] < hdelta[0],
        recurrence_refuted=status == 'refuted_at_this_pair',
        potential_target_refuted=any(v['potential_target_status'] == 'refuted_at_this_support' for v in targets.values()),
        whole_h_target_refuted=any(v['whole_h_target_status'] == 'refuted_at_this_support' for v in targets.values()),
        all_domain_included=True, uniform_recurrence_proved=False, RH_proved=False, RH_refuted=False)


def main():
    started = time.monotonic()
    if OUT.exists(): raise FileExistsError('preserve structural transition audit')
    counts = validate_parent()
    for name in FILES:
        if name.endswith('_development.json'):
            verify_receipt(read(ROOT/name))
    selected = read(BASE.P.OUT/'selected_argument.json')['row']
    if selected['prime'] != selected['request']['prime']:
        raise ValueError('fixed selected prime binding')
    template = BASE.P.PRIOR.ARG.evaluate_argument(selected['request'])
    BASE.P.PRIOR.independent_algebra(selected['request'], template)
    metadata = SEARCH.transition_cases(selected['request']['source_recipe']['base'], selected['prime'],
        minimum=selected['request']['argument']['base']['minimum'])
    planned = metadata['cases'][:CASE_LIMIT]
    # This is a restatement guard application, not a scientific norm probe.
    guard_request = dict(Q=selected['request']['argument']['gram'], B=[['1/2', '0'], ['0', '1/2']],
        rho=selected['request']['argument']['recurrence']['rho'])
    guard = WORK.build_guard(guard_request)
    guard_verification = WORK.verify_guard(guard_request, guard)
    snapshots = {name: (ROOT/name).read_bytes() for name in FILES}
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in snapshots.items(): (OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'protocol.json', dict(schema='floor-transition-audit-v1',
            selected_argument=selected['id'], request=selected['request'], tau=selected['tau'], d=selected['d'],
            case_limit=CASE_LIMIT, planned_pairs=planned, all_metadata_proposals=metadata,
            horizons=list(HORIZONS), refinement='only when the previous interval was unresolved',
            stop_rule='first exact recurrence counterexample or exhaustion of frozen six-case budget',
            scientific_candidate_or_constants_changed=False, old_norms_rerun=False,
            workers=2, memory_limit_bytes=16*1024**3, prior_frozen_source_counts=counts, hashes_used=False))
        write(OUT/'predictor_guard.json', dict(request=guard_request, certificate=guard, verification=guard_verification))
        emit('transition_plan_frozen', candidate=selected['id'], proposed_pairs=len(metadata['cases']),
             planned_pairs=[(c['N'], c['r'], c['child']) for c in planned])
        compiler = SEARCH.StateCompiler()
        source_meter = SOURCE_CHECK.Meter(cap=20_000_000_000, seconds=14400)
        states, norm_cache, norm_rows, results, attempts = {}, {}, [], [], []
        max_reserve = 0
        with mp.get_context('fork').Pool(2) as pool:
            for case in planned:
                for N in (case['N'], case['child']):
                    if N not in states:
                        request = SEARCH.source_request(selected, N)
                        cert = compiler.compile(request)
                        verified = SOURCE_CHECK.verify_state(request, cert, source_meter)
                        states[N] = cert['programs']
                        write(OUT/('source_N%d.json' % N), dict(request=request, certificate=cert, verification=verified))
                        emit('transition_source_verified', N=N, child_source=selected['prime']*N)
                for H in HORIZONS:
                    needed = {}
                    for N in (case['N'], case['child']):
                        for name in ('h', 'v'):
                            program = states[N][name]
                            key = (SEARCH.semantic_key(program), H)
                            if key not in norm_cache: needed[key] = program
                    reserve = CAP.memory_preflight(list(needed.values()), H)
                    max_reserve = max(max_reserve, reserve)
                    emit('transition_norms_started', N=case['N'], r=case['r'], H=H,
                         new_norms=len(needed), aggregate_memory_reserve_bytes=reserve)
                    task_by_id = {p['id']: key for key, p in needed.items()}
                    for row in pool.imap_unordered(CAP.audit_one, [dict(program=p, H=H) for p in needed.values()]):
                        key = task_by_id[row['id']]
                        if key in norm_cache: raise ValueError('duplicate norm result')
                        interval(row)
                        norm_cache[key] = row; norm_rows.append(row)
                        write(OUT/('norm_%03d.json' % len(norm_rows)), dict(H=H, **row))
                        emit('transition_norm_verified', id=row['id'], H=H, total_new_certificates=len(norm_rows))
                    state_norms = {N: {name: norm_cache[(SEARCH.semantic_key(states[N][name]), H)] for name in ('h', 'v')}
                                   for N in (case['N'], case['child'])}
                    result = assess(selected, case, state_norms)
                    result['H'] = H; result['source_parameters'] = case['source_parameters']
                    attempts.append(result)
                    write(OUT/('attempt_%03d.json' % len(attempts)), result)
                    emit('transition_pair_assessed', N=case['N'], child=case['child'], status=result['status'],
                        delta_lower=result['potential_increment']['decimal_lower'],
                        delta_upper=result['potential_increment']['decimal_upper'])
                    if result['status'] != 'unresolved_interval': break
                results.append(result)
                if result['recurrence_refuted']: break
        refuted = any(row['recurrence_refuted'] for row in results)
        feedback = deepcopy(read(BASE.OUT/'next_search_input.json'))
        feedback['parent'] = str((BASE.OUT/'next_search_input.json').relative_to(ROOT))
        feedback['recurrence_status'] = 'REFUTED' if refuted else 'OPEN'
        feedback['transition_evidence'] = dict(path=str((OUT/'assessment.json').relative_to(ROOT)), finite_cases=results)
        feedback['constant_predictor_guard'] = dict(path=str((OUT/'predictor_guard.json').relative_to(ROOT)),
            rule='canonicalize whole work by R=B^TQB; contractive constant predictors add nonnegative parent slack to the old increment',
            further_progress_requires='independent proved innovation/correlation/pairing estimates with acyclic source-bound leaves')
        feedback['remaining_obligations'] = ([
            'replace the refuted fixed recurrence; keep its exact counterexample as an admission test',
            'discover and prove drift-aware whole signed control with exact ceiling and precision phases'] if refuted else [
            'prove the unchanged uniform signed recurrence for every integer N and both parities',
            'finite transition passes leave all untested scales and required tail estimates open'])
        feedback['potential_target_refuted'] = any(r['potential_target_refuted'] for r in results)
        feedback['whole_h_target_refuted'] = any(r['whole_h_target_refuted'] for r in results)
        feedback['next_productions'] = [dict(kind='exact_drift_phase_recurrence',
            state='L(N), L(pN), exact ceilings, both source rounding precisions',
            missing='a uniform arithmetic remainder bound; phase tracking itself does not prove it'),
            dict(kind='source_bound_innovation_lemma',
            missing='a genuinely new bound on coupled prime/composite correlations, preserving cross terms and tail')]
        feedback['uniform_bound_proved'] = False
        write(OUT/'assessment.json', dict(rows=results, attempts=attempts,
            stopped_on_counterexample=refuted, planned_pairs=len(planned), untested_planned_pairs=planned[len(results):],
            uniform_recurrence_proved=False))
        write(OUT/'next_search_input.json', feedback)
        report = dict(status='FIXED_RECURRENCE_REFUTED_AT_PROFILE_TRANSITION' if refuted else 'FINITE_TRANSITION_AUDIT_UNIFORM_RECURRENCE_OPEN',
            selected_argument=selected['id'], source_constructions=len(states), norm_certificates=len(norm_rows),
            finite_recurrence_pairs=len(results), norm_horizons_used=sorted(set(r['H'] for r in attempts)),
            status_counts={s: sum(r['status'] == s for r in results) for s in
                ('verified_at_this_pair', 'refuted_at_this_pair', 'unresolved_interval')},
            recurrence_refuted=refuted, potential_target_refuted=feedback['potential_target_refuted'],
            whole_h_target_refuted=feedback['whole_h_target_refuted'],
            source_producer_operations=compiler.meter.operations, drift_producer_counts=compiler.drift_meter.counts(),
            independent_source_operations=source_meter.operations,
            norm_producer_operations=sum(r['producer_counts']['operations'] for r in norm_rows),
            norm_checker_operations=sum(r['checker_operations'] for r in norm_rows),
            norm_conversion_operations=sum(r['conversion_operations'] for r in norm_rows),
            norm_preflight_operations=sum(r['preflight_operations'] for r in norm_rows),
            parent_capacity_preflight_operations=CAP._preflight_operations,
            parent_conversion_operations=CAP.CONVERSION_OPERATIONS,
            aggregate_memory_reserve_bytes=max_reserve,
            parent_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            largest_individual_worker_rss_kib=max((r['worker_peak_rss_kib'] for r in norm_rows), default=0),
            prior_frozen_source_counts=counts, new_frozen_source_count=len(FILES),
            elapsed_seconds=time.monotonic()-started, scientific_candidate_or_constants_changed=False,
            uniform_signed_bound_proved=False, RH_proved=False, RH_refuted=False)
        validate_parent()
        if any((ROOT/name).read_bytes() != data for name, data in snapshots.items()):
            raise ValueError('frozen050 source changed')
        write(OUT/'report.json', report)
        emit('completed', status=report['status'], norm_certificates=len(norm_rows), elapsed_seconds=report['elapsed_seconds'])
    except Exception as error:
        write(OUT/'failure.json', dict(type=type(error).__name__, message=str(error), elapsed_seconds=time.monotonic()-started))
        raise


if __name__ == '__main__': main()
