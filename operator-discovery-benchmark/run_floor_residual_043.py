"""Freeze fixed arithmetic families, select on training, certify final whole norms."""
from copy import deepcopy
from fractions import Fraction as Q
import json
import multiprocessing as mp
from pathlib import Path
import resource
import time

import floor_residual_search_043 as SEARCH
import floor_residual_interval_043 as INTERVAL
import check_floor_residual_arguments_043 as CHECK


ROOT = Path(__file__).resolve().parent
PARENT = ROOT/'finite-prime-obstruction-results/pilot-001'
OUT = ROOT/'floor-residual-results/pilot-001'
RECEIPTS = ['floor_residual_search_043_development.json', 'floor_residual_interval_043_development.json',
            'check_floor_residual_arguments_043_development.json', 'floor_residual_runner_043_development.json']
FILES = ['floor_residual_search_043.py', 'floor_residual_interval_043.py', 'check_floor_residual_arguments_043.py',
         'run_floor_residual_043.py', 'test_floor_residual_search_043.py', 'test_floor_residual_interval_043.py',
         'test_check_floor_residual_arguments_043.py', 'test_floor_residual_runner_043.py',
         'floor_residual_protocol_043.txt', 'FLOOR_RESIDUAL_INTERVAL_043.txt', 'FLOOR_RESIDUAL_SCOPE_043.txt']+RECEIPTS


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def emit(event, **values):
    print(json.dumps(dict(event=event, **values)), flush=True)


def semantic_key(program):
    return (tuple((r['n'], r['value']) for r in program['coefficients']),
            tuple((r['q'], r['value']) for r in program['steps']))


def log_bound_interval(N, A, eta, meter=None):
    if type(N) is not int or N < 2 or not 0 < Q(eta) <= 1 or Q(A) <= 0:
        raise ValueError('positive cost, support>=2, compatible rational log exponent0..1')
    level = N.bit_length()
    value = SEARCH.root_floor(Q(1, level), eta, 128, meter)
    return dict(A=A, eta=eta, level=level, lower=str(Q(A)*value),
                upper=str(Q(A)*(value+Q(1, 1 << 128))),
                formula='A/(1+floor(log2N))^eta', exact_integer_root_bracket=True)


def compile_batch(search, parents):
    if tuple(parents) != SEARCH.FINAL_PARENTS:
        raise ValueError('frozen final support list')
    compiler = SEARCH.Compiler(max(parents)*max(SEARCH.MULTIPLIERS))
    recipes = {r['id']: r for r in search['selected_recipes']}
    programs, seen, cases, rules, arguments = [], {}, [], [], []
    proof_meter = CHECK.Meter(cap=100_000_000)
    def register(p):
        key = semantic_key(p)
        if key not in seen:
            seen[key] = p['id']
            programs.append(p)
        return seen[key]
    for index, selection in enumerate(search['selections'], 1):
        recipe, q, b = recipes[selection['family']], selection['q'], selection['b']
        tau = selection['finite_contraction_tau']
        if tau is None:
            tau = max((t for t in SEARCH.TAU_VALUES if SEARCH.contraction_admissible(q, b, t)), key=Q)
        gate = CHECK.verify_relative_forcing_gate(q, b, tau, meter=proof_meter)
        if not gate['admissible'] or gate['convergence_proved']:
            raise ValueError('valid conditional contraction with unpaid leaf')
        log_bound = selection['finite_log_bound'] or dict(A='4', eta='1/5')
        log_gate = CHECK.verify_log_forcing_gate(q, b, log_bound['A'], log_bound['eta'], meter=proof_meter)
        rule = dict(id='rule_%02d'%index, **selection, recipe=recipe, audit_tau=tau,
                    tau_selection='negative calibration only: training match, otherwise largest admissible frozen tau',
                    relative_conditional_gate=gate, conditional_gate=log_gate, audit_log_bound=log_bound,
                    uniform_geometric_contraction='EXCLUDED_BY_IMPORTED_BURNOL_LOWER_BOUND')
        rules.append(rule)
        for N in parents:
            parent, child = compiler.compile(recipe, N), compiler.compile(recipe, q*N)
            forcing = SEARCH.forcing_program(parent, child, q, b, identifier=rule['id']+'_N'+str(N)+'_forcing')
            identity = CHECK.verify_family_refinement(parent, child, q, b, meter=proof_meter)
            if semantic_key(identity['forcing_program']) != semantic_key(forcing):
                raise ValueError('independent exact refinement compiler disagreement')
            p_id, c_id, h_id = register(parent), register(child), register(forcing)
            cases.append(dict(rule=rule['id'], N=N, q=q, b=b, tau=tau,
                              log_bound=log_bound_interval(N, log_bound['A'], log_bound['eta'], compiler.meter),
                              parent=p_id, child=c_id, forcing=h_id))
            arguments.append(dict(rule=rule['id'], N=N, identity=identity))
    for p in programs:
        CHECK.verify_program(p, target=not p['steps'], meter=proof_meter)
    return dict(programs=programs, cases=cases, rules=rules, arguments=arguments,
                compiler_counts=compiler.meter.counts(), argument_operations=proof_meter.operations,
                all_programs_compiled_before_norm_evaluation=True, source_array_replay=False,
                uniform_convergence_proved=False, RH_proved=False)


def audit_one(task):
    p, H = task['program'], task['H']
    started = time.monotonic()
    meter = INTERVAL.Meter(cap=500_000_000, seconds=1200)
    certificate = INTERVAL.certify(p, H=H, precision=192, meter=meter)
    check_meter = CHECK.Meter(cap=750_000_000)
    checked = CHECK.verify_norm(p, certificate, meter=check_meter)
    if not checked['verified'] or not checked['all_domain_included'] or checked['convergence_proved']:
        raise ValueError('independent whole-domain norm admission failed')
    return dict(id=p['id'], certificate=certificate, verification=checked,
                producer_counts=meter.counts(), checker_operations=check_meter.operations,
                elapsed_seconds=time.monotonic()-started,
                worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def interval(row):
    return (Q(row['verification']['global_fixed_norm_squared_lower']),
            Q(row['verification']['global_fixed_norm_squared_upper']))


def serialize_interval(pair):
    return dict(lower=str(pair[0]), upper=str(pair[1]),
                decimal_lower=float(pair[0]), decimal_upper=float(pair[1]))


def analyze_case(case, by_id):
    parent, child, forcing = [interval(by_id[case[key]]) for key in ('parent', 'child', 'forcing')]
    tau, b, t = Q(case['tau']), Q(case['b']), Q(case['b'])**2/case['q']
    defect = (forcing[0]-tau*parent[1], forcing[1]-tau*parent[0])
    status = 'verified_at_this_support' if defect[1] <= 0 else 'refuted_at_this_support' if defect[0] > 0 else 'unresolved_interval'
    log_defect = (forcing[0]-Q(case['log_bound']['upper']), forcing[1]-Q(case['log_bound']['lower']))
    log_status = ('verified_at_this_support' if log_defect[1] <= 0 else
                  'refuted_at_this_support' if log_defect[0] > 0 else 'unresolved_interval')
    cross = ((forcing[0]-child[1]-t*parent[1], forcing[1]-child[0]-t*parent[0]) if b else (Q(0), Q(0)))
    benefit = 'strict_cancellation' if cross[1] < 0 else 'strict_reinforcement' if cross[0] > 0 else 'zero_by_restatement' if not b else 'unresolved_interval'
    diagonal = (child[0]+t*parent[0], child[1]+t*parent[1])
    absolute_cross = ((Q(0) if cross[0] <= 0 <= cross[1] else min(abs(cross[0]), abs(cross[1]))),
                      max(abs(cross[0]), abs(cross[1])))
    unsigned = (diagonal[0]+absolute_cross[0], diagonal[1]+absolute_cross[1])
    if not b:
        mechanism = 'endpoint_restatement'
    elif log_status != 'verified_at_this_support':
        mechanism = 'logarithmic_bound_not_verified_here'
    elif diagonal[0] > Q(case['log_bound']['upper']):
        mechanism = 'signed_cross_needed_even_against_diagonal'
    elif unsigned[0] > Q(case['log_bound']['upper']):
        mechanism = 'signed_cross_needed_against_absolute_cross'
    elif unsigned[1] <= Q(case['log_bound']['lower']):
        mechanism = 'bound_survives_absolute_cross_replacement'
    else:
        mechanism = 'unresolved_interval'
    return dict(**case, parent_norm_squared=serialize_interval(parent), child_norm_squared=serialize_interval(child),
                forcing_norm_squared=serialize_interval(forcing), relative_forcing_defect=serialize_interval(defect),
                relative_forcing_status=status, signed_forcing_cross=serialize_interval(cross),
                logarithmic_forcing_defect=serialize_interval(log_defect), logarithmic_forcing_status=log_status,
                diagonal_forcing_proxy=serialize_interval(diagonal), absolute_cross_forcing_proxy=serialize_interval(unsigned),
                signed_mechanism_for_bound=mechanism,
                signed_cross_effect=benefit, cross_formula='H-E_child-(b^2/q)*E_parent=-2*b*<e_child,D_q e_parent>',
                endpoint_restatement=not b, all_supports_inequality_proved=False, RH_proved=False)


def main():
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (16*1024**3, resource.getrlimit(resource.RLIMIT_AS)[1]))
    if read(PARENT/'report.json')['status'] != 'FINITE_PRIME_PROOF_SCOPE_OBSTRUCTION_VERIFIED_ACTUAL_BOUND_OPEN':
        raise ValueError('preserve completed042 and its OPEN actual bound')
    previous = read(PARENT/'next_search_input.json')
    OUT.mkdir(parents=True, exist_ok=False)
    try:
        for name in FILES:
            dest = OUT/'source_snapshot'/name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes((ROOT/name).read_bytes())
        (OUT/'source_snapshot'/'parent042_next_search_input.json').write_bytes((PARENT/'next_search_input.json').read_bytes())
        spec = dict(schema='floor-residual-frozen-run-v1', grammar=SEARCH.grammar(),
                    training_parents=list(SEARCH.TRAIN_PARENTS), final_parents=list(SEARCH.FINAL_PARENTS),
                    training_H=SEARCH.TRAIN_H, final_H=SEARCH.FINAL_H, final_precision=192,
                    independent_precision=256, workers=2, memory_gib=16,
                    selection='three strata: positive b, negative b, b0 restatement; rank logarithmic bound match before observed log powers',
                    audit_tau='training selected tau, otherwise largest admissible frozen tau; fixed before final norms',
                    per_N_fitting=False, anticipated_winner=None, hashing_used=False,
                    target='norm(1-sum c_n(N)f_n)^2 tends to0 as support N increases',
                    source_bridge='Mellin zero obstruction from actual zeta; pure floors only',
                    prior_centered_mobius_and_original_F_obligations='retained OPEN; alternative route does not prove their bounds')
        spec['imported_lower_bound'] = dict(source='https://arxiv.org/pdf/math/0103058', theorem='1.3',
            basis_inclusion='f_n=rho(1/(n*x))-rho(1/x)/n lies in B_(1/N) for n<=N',
            implication='liminf norm(e_N)^2*logN>0; no uniform fixed-ratio geometric contraction on N=N0*q^j',
            library_theorem_not_rediscovered=True, logarithmic_forcing_etas_above_one_excluded=True)
        write(OUT/'run_spec.json', spec)
        emit('protocol_frozen', families=spec['grammar']['raw_family_count'], refinements=spec['grammar']['refinement_count'])
        search = SEARCH.search(spec['grammar'])
        write(OUT/'search.json', search)
        write(OUT/'selected_families.json', dict(recipes=search['selected_recipes'], rules=search['selections']))
        emit('selection_frozen', finite_log_bound_matches=search['finite_log_bound_matches'],
             negative_calibration_contraction_matches=search['finite_contraction_matches'], rules=search['selections'])
        batch = compile_batch(search, SEARCH.FINAL_PARENTS)
        write(OUT/'final_program_batch.json', batch)
        write(OUT/'conditional_arguments.json', dict(rules=batch['rules'], arguments=batch['arguments'],
              argument_operations=batch['argument_operations'], uniform_convergence_proved=False, RH_proved=False))
        # Conservative aggregate allowance, before workers allocate any event array.
        reserves = []
        for p in batch['programs']:
            meter = INTERVAL.Meter()
            lattice = INTERVAL.integer_lattice(p, meter)
            meter.reserve(SEARCH.FINAL_H, lattice['event_magnitude'].bit_length(), len(p['coefficients'])+len(p['steps']))
            reserves.append(meter.counts()['peak_bytes_estimate'])
        aggregate = 2*max(reserves)+512*1024**2
        if aggregate > 15*1024**3:
            raise MemoryError('aggregate two-worker resource preflight')
        emit('whole_domain_audit_started', distinct_programs=len(batch['programs']), workers=2,
             H=SEARCH.FINAL_H, aggregate_memory_reserve_bytes=aggregate)
        tasks = [dict(program=p, H=SEARCH.FINAL_H) for p in batch['programs']]
        rows = []
        with mp.get_context('fork').Pool(2) as pool:
            for row in pool.imap_unordered(audit_one, tasks):
                index = len(rows)+1
                path = 'norm_%03d.json'%index
                write(OUT/path, row)
                rows.append(dict(**row, artifact=path))
                emit('whole_domain_norm_verified', completed=index, total=len(tasks), id=row['id'],
                     norm_squared_decimal=[float(v) for v in interval(row)])
        by_id = {row['id']: row for row in rows}
        if set(by_id) != {p['id'] for p in batch['programs']} or len(by_id) != len(rows):
            raise ValueError('complete distinct audit coverage')
        assessments = [analyze_case(case, by_id) for case in batch['cases']]
        write(OUT/'assessment.json', dict(cases=assessments, uniform_convergence_proved=False, RH_proved=False))
        obligations = []
        for rule in batch['rules']:
            observed = [c for c in assessments if c['rule'] == rule['id']]
            contradicted = any(c['relative_forcing_status'] == 'refuted_at_this_support' for c in observed)
            log_contradicted = any(c['logarithmic_forcing_status'] == 'refuted_at_this_support' for c in observed)
            obligations.append(dict(rule=rule['id'], recipe=rule['recipe'], q=rule['q'], b=rule['b'],
                logarithmic_forcing=dict(**rule['audit_log_bound'],
                    status='REFUTED_AS_CLAIM_FOR_ALL_N_GE40' if log_contradicted else 'OPEN',
                    domain='every integer N>=40; a later starting support requires its own proof',
                    formula='norm(h_N)^2<=A/(1+floor(log2N))^eta',
                    counterexample_supports=[c['N'] for c in observed if c['logarithmic_forcing_status'] == 'refuted_at_this_support']),
                relative_forcing=dict(tau=rule['audit_tau'],
                    status='EXCLUDED_UNIFORM_GEOMETRIC_BY_IMPORTED_LOWER_BOUND',
                    finite_counterexample_found=contradicted,
                    domain='every integer N>=40; geometric-chain versions need their own N0 and proof',
                    formula='norm(h_N)^2<=tau*norm(e_N)^2',
                    counterexample_supports=[c['N'] for c in observed if c['relative_forcing_status'] == 'refuted_at_this_support']),
                remaining_growth_target=dict(status='OPEN', domain='N=N0*q^j, every j>=0',
                    formula='norm(h_N) tends to0; independently establish this without assuming RH or target convergence',
                    h='1-g_(qN)-b*I_q+b*D_q(g_N)', coefficients='exact formula in recipe, dyadic rounding part of definition'),
                target=dict(status='OPEN', formula='norm(e_N) tends to0', e='1-g_N', steps=[]),
                endpoint_restatement=Q(rule['b']) == 0, dependencies=['pure-floor Mellin bridge', 'exact integer dilation identity'],
                circularity_guard='target norm convergence, RH, and finite norms cannot be providers for forcing convergence',
                fixed_dictionary_obstruction='finite heads cannot have vanishing forcing; support must grow or new source mechanism be supplied'))
        write(OUT/'proof_search_input.json', dict(schema='floor-residual-obstruction-input-v1',
              candidates=obligations, existing_centered_mobius_bound='OPEN', original_F_bound='OPEN', RH_proved=False))
        continuation = deepcopy(previous)
        continuation['authoritative_parent'] = str((PARENT/'next_search_input.json').relative_to(ROOT))
        continuation['floor_residual_route'] = dict(results=str(OUT.relative_to(ROOT)),
            proof_search_input=str((OUT/'proof_search_input.json').relative_to(ROOT)),
            alternative_zero_sensitive_route=True, original_target_replaced=False,
            whole_domain_fixed_program_norms=len(rows), uniform_family_convergence_proved=False, RH_proved=False)
        write(OUT/'next_search_input.json', continuation)
        report = dict(status='FLOOR_RESIDUAL_GLOBAL_NORMS_VERIFIED_FAMILY_CONVERGENCE_OPEN',
            family_count=search['family_count'], refinement_count=search['refinement_count'],
            training_finite_contraction_matches=search['finite_contraction_matches'],
            training_finite_log_bound_matches=search['finite_log_bound_matches'],
            training_b_zero_matches=search['b_zero_matches'], selected_rules=batch['rules'],
            whole_domain_norm_certificates=len(rows), final_cases=len(assessments),
            final_relative_forcing_verified=sum(c['relative_forcing_status'] == 'verified_at_this_support' for c in assessments),
            final_relative_forcing_refuted=sum(c['relative_forcing_status'] == 'refuted_at_this_support' for c in assessments),
            final_relative_forcing_unresolved=sum(c['relative_forcing_status'] == 'unresolved_interval' for c in assessments),
            final_logarithmic_forcing_verified=sum(c['logarithmic_forcing_status'] == 'verified_at_this_support' for c in assessments),
            final_logarithmic_forcing_refuted=sum(c['logarithmic_forcing_status'] == 'refuted_at_this_support' for c in assessments),
            final_logarithmic_forcing_unresolved=sum(c['logarithmic_forcing_status'] == 'unresolved_interval' for c in assessments),
            cross_effect_counts={label:sum(c['signed_cross_effect'] == label for c in assessments)
                                 for label in ('strict_cancellation', 'strict_reinforcement', 'zero_by_restatement', 'unresolved_interval')},
            signed_mechanism_counts={label:sum(c['signed_mechanism_for_bound'] == label for c in assessments)
                                    for label in sorted({c['signed_mechanism_for_bound'] for c in assessments})},
            full_signed_core_bound_proved=False, family_convergence_proved=False, RH_proved=False, RH_refuted=False,
            prior_studies_rerun=0, independently_replayed_all_norms=True,
            search_counts=search['counts'], compiler_counts=batch['compiler_counts'],
            argument_operations=batch['argument_operations'],
            producer_operations=sum(r['producer_counts']['operations'] for r in rows),
            checker_operations=sum(r['checker_operations'] for r in rows),
            aggregate_memory_reserve_bytes=aggregate,
            parent_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            worker_max_individual_rss_kib=max(r['worker_peak_rss_kib'] for r in rows),
            elapsed_seconds=time.monotonic()-started,
            certificates=[dict(id=r['id'], artifact=r['artifact']) for r in rows],
            development_receipts={name:read(ROOT/name) for name in RECEIPTS})
        for name in FILES:
            if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
                raise ValueError('frozen043 source changed: '+name)
        write(OUT/'report.json', report)
        emit('completed', status=report['status'], elapsed_seconds=report['elapsed_seconds'],
             certificates=len(rows), logarithmic_forcing_statuses={key:report[key] for key in
                ('final_logarithmic_forcing_verified', 'final_logarithmic_forcing_refuted', 'final_logarithmic_forcing_unresolved')})
    except Exception as error:
        write(OUT/'failure.json', dict(type=type(error).__name__, message=str(error), elapsed_seconds=time.monotonic()-started))
        raise


if __name__ == '__main__':
    main()
