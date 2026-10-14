"""Freeze, search and independently audit prime-potential recurrence candidates."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '2'
os.environ['OMP_NUM_THREADS'] = '2'
from copy import deepcopy
from fractions import Fraction as Q
import multiprocessing as mp
from pathlib import Path
import resource
import time

import floor_residual_prime_search_047 as S
import floor_residual_prime_047 as PRIME
import check_floor_residual_prime_047 as PC
import floor_residual_prime_argument_047 as ARG
import floor_residual_capacity_045 as CAP
import publish_floor_residual_global_followup_046 as PREV

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'floor-residual-results/pilot-004'
AUDIT = PREV.NUM.R.AUDIT
read, write, emit = PREV.read, PREV.write, PREV.emit
RECEIPTS = ['floor_residual_prime_047_development.json',
    'check_floor_residual_prime_047_development.json',
    'floor_residual_prime_argument_047_development_receipt.json',
    'floor_residual_prime_argument_scope_047_development.json',
    'floor_residual_prime_text_047_development.json',
    'floor_residual_prime_search_047_development.json']
FILES = ['floor_residual_prime_047.py', 'test_floor_residual_prime_047.py',
    'check_floor_residual_prime_047.py', 'test_check_floor_residual_prime_047.py',
    'floor_residual_prime_argument_047.py', 'test_floor_residual_prime_argument_047.py',
    'PRIME_JOINT_BOUND_ARGUMENT_REVIEW_047.txt',
    'floor_residual_prime_search_047.py', 'test_floor_residual_prime_search_047.py',
    'test_floor_residual_prime_text_047.py',
    'run_floor_residual_prime_047.py', 'floor_residual_prime_protocol_047.txt']+RECEIPTS


def validate_parent():
    counts = PREV.validate_parent()
    files = list((PREV.OUT/'source_snapshot').iterdir())
    if len(files) != len(PREV.FILES) or any((ROOT/p.name).read_bytes()!=p.read_bytes() for p in files):
        raise ValueError('preserve frozen046 sources')
    if not (PREV.OUT/'report.json').exists():
        raise ValueError('completed046 feedback required')
    return counts+[len(files)]


def independent_algebra(request, certificate):
    """Direct 2x2 principal-minor/induction replay, no argument producer call."""
    if certificate.get('request') != request or certificate.get('status') != 'OPEN':
        raise ValueError('source-bound open arithmetic argument required')
    if (certificate.get('uniform_arithmetic_bound_proved') is not False or
        certificate.get('RH_proved') is not False or certificate.get('target_status') != 'OPEN'):
        raise ValueError('an implication is not an arithmetic proof')
    arg = request['argument']; matrix = [[Q(v) for v in row] for row in arg['gram']]
    a, b, c = matrix[0][0]-1, matrix[0][1]-1, matrix[1][1]-1
    if matrix[0][1] != matrix[1][0] or min(a, c) < 0 or a*c < b*b:
        raise ValueError('full signed target must be dominated')
    rec = arg['recurrence']; base = arg['base']['minimum']
    A, eta, rho, C = (Q(request['target']['A']), Q(request['target']['eta']),
                       Q(rec['rho']), Q(rec['C']))
    if (base < 2 or base & (base-1) or A <= 0 or eta <= 0 or not 0 <= rho < 1 or C < 0 or
        rec['parities'] != [0, 1] or rec['forcing'] != 'L_parent^-eta'):
        raise ValueError('uniform integer induction scope')
    L = base.bit_length()
    if (rho+C/A)**eta.denominator > Q(L, L+1)**eta.numerator:
        raise ValueError('exact induction budget')
    by_id = {r['id']: r for r in certificate['dependencies']}
    if by_id['BASE']['status'] != 'OPEN' or by_id['RECURRENCE']['status'] != 'OPEN':
        raise ValueError('uniform arithmetic leaves remain unpaid')
    return dict(verified=True, method='independent exact principal minors and powered induction inequality',
                source_compilation_verified_here=False, all_scale_arithmetic_bound_proved=False)


def compile_final(selections, progress=None):
    maximum = max(S.levels(S.FINAL_PARENTS))*max(s['prime'] for s in selections)
    compiler = S.S.Compiler(maximum, retain_compilation_certificates=False)
    prime_meter = PRIME.Meter(cap=2_000_000_000, seconds=7200)
    check_meter = PC.Meter(cap=4_000_000_000)
    source_meter = S.S.DRIFT_CHECK.Meter(cap=10_000_000_000)
    norm_source_meter = CAP.CHECK.Meter(cap=500_000_000)
    checked_profiles, programs, seen, constructions, cases, arguments = set(), [], {}, [], [], []
    def register(program, identifier):
        p = deepcopy(program); p['id'] = identifier
        CAP.CHECK.verify_program(p, target=False, meter=norm_source_meter)
        key = S.S.OLD.semantic_key(p)
        if key not in seen:
            seen[key] = p['id']; programs.append(p)
        return seen[key]
    for index, selected in enumerate(selections, 1):
        req = selected['request']; recipe, prime = req['source_recipe'], req['prime']
        argument = ARG.evaluate_argument(req)
        ARG.verify_argument(req, argument)
        arguments.append(dict(id=selected['id'], certificate=argument,
                              independent_algebra=independent_algebra(req, argument)))
        for N in S.levels(S.FINAL_PARENTS):
            source = S.source_request(compiler, recipe, prime, N)
            for support, values in ((N, source['parent_values']), (prime*N, source['child_values'])):
                key = (S.S.OLD.ast_key(recipe), support)
                if key not in checked_profiles:
                    for n, value in enumerate(values, 1):
                        S.S.DRIFT_CHECK.verify_compilation(recipe['base'], n, support, value, meter=source_meter)
                    checked_profiles.add(key)
            certificate = PRIME.build_prime_construction(source, meter=prime_meter)
            verified = PC.verify_prime_construction(source, certificate, meter=check_meter)
            if not verified['verified']:
                raise ValueError('independent exact prime construction')
            h, aux = certificate['original_forcing'], certificate['matched']['conversion_auxiliary']
            v = S.direction(h, aux, selected['d'], 'direction')
            prefix = 'selected_%02d_N%d' % (index, N)
            h_id = register(h, prefix+'_whole')
            v_id = register(v, prefix+'_direction')
            constructions.append(dict(selection=selected['id'], N=N, source_recipe=recipe,
                certificate=certificate, verification=verified,
                rounded_source_values_independently_replayed=True))
            cases.append(dict(selection=selected['id'], N=N, whole=h_id, direction=v_id))
            if progress:
                progress('source_verified', selection=selected['id'], N=N, child_support=prime*N)
    return dict(programs=programs, cases=cases, constructions=constructions, arguments=arguments,
        checked_profile_arrays=len(checked_profiles), source_operations=source_meter.operations,
        compiler_counts=compiler.meter.counts(), drift_counts=compiler.drift_meter.counts(),
        prime_counts=prime_meter.counts(), prime_checker_operations=check_meter.operations,
        norm_program_operations=norm_source_meter.operations)


def assess(selections, cases, by_id):
    by_case = {(c['selection'], c['N']): c for c in cases}
    results = []
    for s in selections:
        potential, whole = {}, {}
        tau = Q(s['tau']); req = s['request']; rec = req['argument']['recurrence']
        rho = Q(rec['rho']); bound = req['target']
        for N in S.levels(S.FINAL_PARENTS):
            case = by_case[s['id'], N]
            h, v = AUDIT.interval(by_id[case['whole']]), AUDIT.interval(by_id[case['direction']])
            whole[N] = h
            potential[N] = h[0]+tau*v[0], h[1]+tau*v[1]
        for N in S.FINAL_PARENTS:
            for parity in (0, 1):
                child = 2*N+parity
                delta = (potential[child][0]-rho*potential[N][1],
                         potential[child][1]-rho*potential[N][0])
                threshold = AUDIT.log_bound_interval(N, rec['C'], bound['eta'])
                lo, hi = Q(threshold['lower']), Q(threshold['upper'])
                status = ('verified_at_this_pair' if delta[1] <= lo else
                          'refuted_at_this_pair' if delta[0] > hi else 'unresolved_interval')
                h_delta = (whole[child][0]-rho*whole[N][1], whole[child][1]-rho*whole[N][0])
                results.append(dict(selection=s['id'], N=N, child=child, parity=parity,
                    potential_parent=AUDIT.serialize_interval(potential[N]),
                    potential_child=AUDIT.serialize_interval(potential[child]),
                    increment=AUDIT.serialize_interval(delta), threshold=threshold,
                    status=status, h_only_increment=AUDIT.serialize_interval(h_delta),
                    auxiliary_improves_increment_proved=delta[1]<h_delta[0],
                    all_k_included=True, uniform_recurrence_proved=False))
    return results


def main():
    started = time.monotonic()
    if OUT.exists():
        raise FileExistsError('preserve existing prime search')
    prior = validate_parent()
    for name in RECEIPTS:
        if not PREV.NUM.R.passing_receipt(read(ROOT/name)):
            raise ValueError('passing focused development receipt required: '+name)
    snapshots = {name:(ROOT/name).read_bytes() for name in FILES}
    frozen = S.grammar()
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in snapshots.items():
        (OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'run_spec.json', dict(grammar=frozen, workers=2, aggregate_memory_bytes=16*1024**3,
            authoritative_parent=str((PREV.OUT/'next_search_input.json').relative_to(ROOT)),
            frozen_source_counts=prior+[len(FILES)], hashes_used=False,
            existing_norms_rerun=False, final_H=S.FINAL_H, training_H=S.TRAIN_H))
        emit('prime_search_frozen', recipes=len(frozen['recipes']), source_counts=prior+[len(FILES)])
        gates = S.proof_gates(frozen, progress=emit)
        write(OUT/'presearch_gates.json', gates)
        catalog = S.argument_catalog(frozen, gates)
        write(OUT/'argument_catalog.json', catalog)
        emit('argument_catalog_ready', arguments=len(catalog['rows']), rejected_bounds=gates['rejected_bounds'])
        search = S.search(frozen, catalog, progress=emit)
        write(OUT/'search.json', search)
        selections = search['selections']
        write(OUT/'selected_arguments.json', dict(rows=selections, heldout_observations_used=False))
        emit('arguments_selected', rows=[dict(id=s['id'], family=s['family'], prime=s['prime'],
             tau=s['tau'], d=s['d'], target=s['request']['target'],
             recurrence=s['request']['argument']['recurrence'], training_failures=s['finite_failure_count']) for s in selections])
        batch = compile_final(selections, progress=emit)
        write(OUT/'final_program_batch.json', batch)
        reserve = CAP.memory_preflight(batch['programs'])
        emit('whole_domain_audit_started', programs=len(batch['programs']), aggregate_reserve_bytes=reserve)
        rows = []
        with mp.get_context('fork').Pool(2) as pool:
            for row in pool.imap_unordered(CAP.audit_one, [dict(program=p, H=S.FINAL_H) for p in batch['programs']]):
                artifact = 'norm_%03d.json' % (len(rows)+1)
                write(OUT/artifact, row); rows.append(row)
                emit('norm_verified', completed=len(rows), total=len(batch['programs']), id=row['id'])
        by_id = {r['id']: r for r in rows}
        if set(by_id) != {p['id'] for p in batch['programs']} or len(by_id) != len(rows):
            raise ValueError('complete independent whole-norm coverage')
        assessment = assess(selections, batch['cases'], by_id)
        write(OUT/'assessment.json', dict(rows=assessment, uniform_recurrence_proved=False))
        feedback_rows = []
        for s in selections:
            finite = [c for c in assessment if c['selection']==s['id']]
            refuted = any(c['status']=='refuted_at_this_pair' for c in finite)
            argument = next(a for a in batch['arguments'] if a['id']==s['id'])
            feedback_rows.append(dict(selection=s, exact_argument=argument,
                finite_cases=finite, recurrence_status='REFUTED' if refuted else 'OPEN',
                next_obligation=(dict(kind='change_auxiliary_or_recurrence',
                    reason='complete-domain counterexample to this fixed recurrence') if refuted else
                    dict(kind='uniform_signed_predictor_work_or_recurrence',
                    target='P_(2N+r)-rho P_N <= C/L(N)^eta for every N>=32 and both parities',
                    base='certify every N in[32,63]; current training probes are not a base proof',
                    source='whole H+A with coprime, prime-square, normalization and all k tails')),
                whole_bound_proved=False))
        write(OUT/'next_search_input.json', dict(schema='prime-potential-bound-feedback-v1',
            candidates=feedback_rows, priority='prove or discover a controller for the signed scale increment',
            dependency_cycles_allowed=False, finite_trend_as_provider=False,
            predictor_matrix_search_implemented=False,
            original_F_and_centered_mobius_bounds='OPEN', RH_proved=False))
        report = dict(status='PRIME_AUXILIARY_POTENTIALS_SEARCHED_UNIFORM_RECURRENCE_OPEN',
            formulas=len(frozen['recipes']), theta_values=frozen['theta_values'],
            proposed_arguments=len(catalog['rows']), rejected_bounds=gates['rejected_bounds'],
            induction_parameter_rejections=catalog['invalid_induction_parameters'],
            finite_training_matches=search['finite_argument_matches'],
            noncollinear_training_matches=search['noncollinear_finite_matches'],
            selected_arguments=[dict(id=s['id'], family=s['family'], prime=s['prime'], tau=s['tau'], d=s['d'], request=s['request']) for s in selections],
            independent_source_constructions=len(batch['constructions']),
            norm_certificates=len(rows), final_recurrence_pairs=len(assessment),
            final_status_counts={label:sum(c['status']==label for c in assessment) for label in
                ('verified_at_this_pair', 'refuted_at_this_pair', 'unresolved_interval')},
            proved_auxiliary_improvements=sum(c['auxiliary_improves_increment_proved'] for c in assessment),
            training_counts=search['training_counts'], drift_training_counts=search['drift_counts'],
            prime_training_counts=search['prime_counts'], distinct_training_vectors=search['distinct_numerical_vectors'],
            training_vector_cache_hits=search['exact_vector_cache_hits'], proof_gate_operations=gates['operations'],
            final_source_operations=batch['source_operations'], prime_compilation_counts=batch['prime_counts'],
            prime_checker_operations=batch['prime_checker_operations'],
            norm_producer_operations=sum(r['producer_counts']['operations'] for r in rows),
            norm_checker_operations=sum(r['checker_operations'] for r in rows),
            aggregate_memory_reserve_bytes=reserve, elapsed_seconds=time.monotonic()-started,
            parent_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            largest_individual_worker_rss_kib=max(r['worker_peak_rss_kib'] for r in rows),
            prior_frozen_source_counts=prior, new_frozen_source_count=len(FILES),
            uniform_signed_bound_proved=False, RH_proved=False, RH_refuted=False)
        validate_parent()
        if any((ROOT/n).read_bytes()!=data for n,data in snapshots.items()):
            raise ValueError('frozen047 source changed')
        write(OUT/'report.json', report)
        emit('completed', status=report['status'], elapsed_seconds=report['elapsed_seconds'],
             final_status_counts=report['final_status_counts'])
    except Exception as error:
        write(OUT/'failure.json', dict(type=type(error).__name__, message=str(error), elapsed_seconds=time.monotonic()-started))
        raise


if __name__ == '__main__':
    main()
