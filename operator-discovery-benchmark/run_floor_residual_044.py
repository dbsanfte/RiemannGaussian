"""Freeze compatible formulas, discover bound candidates, independently audit."""
import os
# Set before NumPy is imported. Two BLAS threads for training; two audit workers.
os.environ['OPENBLAS_NUM_THREADS'] = '2'
os.environ['OMP_NUM_THREADS'] = '2'
from fractions import Fraction as Q
import json
import multiprocessing as mp
from pathlib import Path
import resource
import time

import floor_residual_search_044 as SEARCH
import floor_residual_interval_044 as INTERVAL
import check_floor_residual_arguments_044 as CHECK

ROOT = Path(__file__).resolve().parent
PARENT = ROOT/'floor-residual-results/pilot-001/analytical_followup_001'
OUT = ROOT/'floor-residual-results/pilot-002'
RECEIPTS = ['floor_residual_search_044_development.json', 'floor_residual_interval_044_development.json',
            'check_floor_residual_arguments_044_development.json', 'floor_residual_runner_044_development.json']
FILES = ['floor_residual_search_044.py', 'floor_residual_interval_044.py', 'check_floor_residual_arguments_044.py',
         'run_floor_residual_044.py', 'test_floor_residual_search_044.py', 'test_floor_residual_interval_044.py',
         'test_check_floor_residual_arguments_044.py', 'test_floor_residual_runner_044.py',
         'floor_residual_protocol_044.txt', 'FLOOR_RESIDUAL_INTERVAL_044.txt', 'FLOOR_RESIDUAL_SCOPE_044.txt',
         'floor_residual_search_043.py', 'floor_residual_044_preflight_failure.json',
         'floor_residual_044_run.stderr.txt']+RECEIPTS


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def emit(event, **values):
    print(json.dumps(dict(event=event, **values)), flush=True)


def verify_development_receipt(receipt):
    runs = receipt.get('invocations', receipt.get('runs', []))
    if type(runs) is not list or not runs or runs[-1].get('returncode') != 0:
        raise ValueError('missing passing focused development receipt')
    return runs[-1]


def log_bound_interval(N, A, eta, meter=None):
    if type(N) is not int or N < 2 or Q(A) <= 0 or not 0 < Q(eta) <= 1:
        raise ValueError('positive cost, support>=2, eta in(0,1]')
    level = N.bit_length()
    value = SEARCH.root_floor(Q(1, level), eta, 128, meter)
    return dict(A=A, eta=eta, level=level, lower=str(Q(A)*value),
                upper=str(Q(A)*(value+Q(1, 1 << 128))),
                formula='A/(1+floor(log2N))^eta', exact_integer_root_bracket=True)


def compile_batch(search, parents):
    if tuple(parents) != SEARCH.FINAL_PARENTS:
        raise ValueError('frozen final support partition')
    compiler = SEARCH.Compiler(max(parents)*max(SEARCH.MULTIPLIERS))
    recipes = {r['id']: r for r in search['selected_recipes']}
    programs, seen, cases, rules, arguments = [], {}, [], [], []
    meter = CHECK.Meter(cap=500_000_000)
    def register(p):
        key = SEARCH.semantic_key(p)
        if key not in seen:
            seen[key] = p['id']
            programs.append(p)
        return seen[key]
    for index, selection in enumerate(search['selections'], 1):
        recipe, q, b = recipes[selection['family']], selection['q'], selection['b']
        bound = selection['finite_log_bound'] or dict(A='4', eta='1/5')
        gate = CHECK.verify_log_forcing_gate(q, b, bound['A'], bound['eta'], meter=meter)
        limit = SEARCH.certify_recipe_limit(recipe)
        base = dict(id='baseline_for_'+recipe['id'], base=recipe['base'], auxiliary=None)
        rule = dict(id='rule_%02d'%index, **selection, recipe=recipe, audit_log_bound=bound,
                    baseline_recipe=base, conditional_gate=gate, coefficient_limit_certificate=limit,
                    fallback_bound_policy='A4 eta1/5 only if no training match; fixed before final norms')
        rules.append(rule)
        for N in parents:
            parent, child = compiler.compile(recipe, N), compiler.compile(recipe, q*N)
            h = SEARCH.forcing_program(parent, child, q, b, rule['id']+'_N'+str(N)+'_forcing')
            base_parent, base_child = compiler.compile(base, N), compiler.compile(base, q*N)
            h0 = SEARCH.forcing_program(base_parent, base_child, q, b, rule['id']+'_N'+str(N)+'_baseline_forcing')
            v = SEARCH.difference_program(h, h0, rule['id']+'_N'+str(N)+'_auxiliary_forcing')
            identity = CHECK.verify_family_refinement(parent, child, q, b, meter=meter)
            base_identity = CHECK.verify_family_refinement(base_parent, base_child, q, b, meter=meter)
            if SEARCH.semantic_key(identity['forcing_program']) != SEARCH.semantic_key(h):
                raise ValueError('independent refinement compiler disagreement')
            if SEARCH.semantic_key(base_identity['forcing_program']) != SEARCH.semantic_key(h0):
                raise ValueError('independent baseline refinement disagreement')
            # Direct signed-vector coefficient replay of h=h0+v, including units/steps.
            if SEARCH.semantic_key(SEARCH.difference_program(h, v, 'replay')) != SEARCH.semantic_key(h0):
                raise ValueError('auxiliary signed-vector identity failed')
            cases.append(dict(rule=rule['id'], N=N, q=q, b=b,
                              has_auxiliary=recipe['auxiliary'] is not None,
                              log_bound=log_bound_interval(N, bound['A'], bound['eta'], compiler.meter),
                              parent=register(parent), child=register(child), forcing=register(h),
                              baseline_forcing=register(h0), auxiliary_forcing=register(v)))
            arguments.append(dict(rule=rule['id'], N=N, refinement=identity, baseline_refinement=base_identity,
                                  auxiliary_identity='h=h0+v; constant(v)=0,steps(v)=[]',
                                  auxiliary_program=v, auxiliary_identity_replayed_exactly=True))
    for p in programs:
        CHECK.verify_program(p, target=p['constant']=='1' and not p['steps'], meter=meter)
    return dict(programs=programs, cases=cases, rules=rules, arguments=arguments,
                compiler_counts=compiler.meter.counts(), argument_operations=meter.operations,
                all_programs_compiled_before_norm_evaluation=True, uniform_convergence_proved=False, RH_proved=False)


_worker_kernel = None


def audit_one(task):
    global _worker_kernel
    if _worker_kernel is None:
        _worker_kernel = INTERVAL.JordanKernel()
    p, H = task['program'], task['H']
    started = time.monotonic()
    meter = INTERVAL.Meter(cap=1_000_000_000, seconds=3600)
    certificate = INTERVAL.certify(p, H=H, precision=192, meter=meter, kernel=_worker_kernel)
    proof_meter = CHECK.Meter(cap=3_000_000_000)
    checked = CHECK.verify_norm(p, certificate, meter=proof_meter)
    if not checked['verified'] or not checked['all_domain_included'] or checked['convergence_proved']:
        raise ValueError('whole-domain admission failed')
    return dict(id=p['id'], certificate=certificate, verification=checked,
                producer_counts=meter.counts(), checker_operations=proof_meter.operations,
                elapsed_seconds=time.monotonic()-started,
                worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def interval(row):
    return Q(row['verification']['global_fixed_norm_squared_lower']), Q(row['verification']['global_fixed_norm_squared_upper'])


def serialize_interval(pair):
    return dict(lower=str(pair[0]), upper=str(pair[1]), decimal_lower=float(pair[0]), decimal_upper=float(pair[1]))


def signed_diagnostic(total, left, right, bound, role):
    cross = total[0]-left[1]-right[1], total[1]-left[0]-right[0]
    absolute = (Q(0) if cross[0] <= 0 <= cross[1] else min(abs(cross[0]), abs(cross[1])),
                max(abs(cross[0]), abs(cross[1])))
    diagonal = left[0]+right[0], left[1]+right[1]
    unsigned = diagonal[0]+absolute[0], diagonal[1]+absolute[1]
    if role in ('endpoint_restatement', 'no_auxiliary'):
        mechanism = role
    elif total[1] > bound[0]:
        mechanism = 'bound_not_verified_here'
    elif diagonal[0] > bound[1]:
        mechanism = 'signed_cross_needed_even_against_diagonal'
    elif unsigned[0] > bound[1]:
        mechanism = 'signed_cross_needed_against_absolute_cross'
    elif unsigned[1] <= bound[0]:
        mechanism = 'bound_survives_absolute_cross_replacement'
    else:
        mechanism = 'unresolved_interval'
    effect = ('exact_zero' if cross == (0, 0) else 'strict_cancellation' if cross[1] < 0 else
              'strict_reinforcement' if cross[0] > 0 else 'unresolved_interval')
    return dict(cross=serialize_interval(cross), diagonal=serialize_interval(diagonal),
                absolute_cross_replacement=serialize_interval(unsigned), effect=effect, mechanism=mechanism,
                uniform_cancellation_proved=False)


def analyze_case(case, by_id):
    values = {key: interval(by_id[case[key]]) for key in
              ('parent', 'child', 'forcing', 'baseline_forcing', 'auxiliary_forcing')}
    bound = Q(case['log_bound']['lower']), Q(case['log_bound']['upper'])
    h = values['forcing']
    defect = h[0]-bound[1], h[1]-bound[0]
    status = ('verified_at_this_support' if defect[1] <= 0 else
              'refuted_at_this_support' if defect[0] > 0 else 'unresolved_interval')
    t = Q(case['b'])**2/case['q']
    dilation = tuple(t*v for v in values['parent'])
    refinement = signed_diagnostic(h, values['child'], dilation, bound,
                                  'endpoint_restatement' if case['b']=='0' else 'scale_refinement')
    auxiliary = signed_diagnostic(h, values['baseline_forcing'], values['auxiliary_forcing'], bound,
                                 'signed_auxiliary' if case['has_auxiliary'] else 'no_auxiliary')
    return dict(rule=case['rule'], N=case['N'], q=case['q'], b=case['b'],
                energies={k:serialize_interval(v) for k, v in values.items()}, log_bound=case['log_bound'],
                logarithmic_forcing_defect=serialize_interval(defect), logarithmic_forcing_status=status,
                refinement=refinement, auxiliary=auxiliary,
                all_supports_inequality_proved=False, RH_proved=False)


def memory_preflight(programs):
    reserves = []
    for p in programs:
        meter = INTERVAL.Meter()
        lattice = INTERVAL.integer_lattice(p, meter)
        support = len(p['coefficients'])+len(p['steps'])
        K = p['coefficients'][-1]['n'] if p['coefficients'] else 1
        extra = (K+1)*(384+(lattice['early_bound_num'].bit_length()+7)//8)
        meter.reserve(SEARCH.FINAL_H, lattice['event_abs'].bit_length(), support, extra)
        reserves.append(meter.counts()['peak_bytes_estimate'])
    aggregate = 2*max(reserves, default=0)+2*1024**3
    if aggregate > 16*1024**3:
        raise MemoryError('aggregate two-worker memory preflight')
    return aggregate


def main():
    started = time.monotonic()
    if OUT.exists():
        raise FileExistsError('refuse to replace an existing044 run or its evidence')
    parent = read(PARENT/'grammar_feedback.json')
    if parent.get('next_constructions_implemented') is not False or parent.get('RH_proved') is not False:
        raise ValueError('authoritative043 obstruction input scope changed')
    for name in RECEIPTS:
        receipt = read(ROOT/name)
        verify_development_receipt(receipt)
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    try:
        spec = dict(schema='compatible-floor-protocol-v1', grammar=SEARCH.grammar(),
            authoritative_parent=str((PARENT/'next_search_input.json').relative_to(ROOT)),
            parent_grammar_feedback=str((PARENT/'grammar_feedback.json').relative_to(ROOT)),
            training_parents=list(SEARCH.TRAIN_PARENTS), final_parents=list(SEARCH.FINAL_PARENTS),
            training_H=SEARCH.TRAIN_H, final_H=SEARCH.FINAL_H, precision=192, independent_precision=256,
            norm_workers=2, training_blas_threads=2, memory_gib=16,
            search_work_cap=150_000_000_000, producer_work_cap_per_norm=1_000_000_000,
            checker_work_cap_per_norm=3_000_000_000, phase_deadline_seconds=3600,
            max_index=4096, support_cap=2048, rational_parameter_bits=4096, exact_integer_bits=8192,
            selection='four strata; log-bound match then necessary signed auxiliaries/crosses, eta, growth slopes, proxy, stable id',
            final_threshold_policy='training A,eta frozen; fallback A4 eta1/5 if no training match',
            final_domain='all integers N>=257 for tested uniform bound; geometric-chain convergence remains separate',
            target='pure-floor target residual with constant1; norm tends to0',
            negative_rates=CHECK.geometric_rate_guard(),
            exact_fixed_index_limit_is_not_sufficient_for_convergence=True,
            imported_tail_theorem=INTERVAL.LARGE_SIEVE_URL,
            imported_tail_is_not_new_RH_control=True,
            final_data_used_to_select=False, hashing_used=False, per_N_fitting=False, anticipated_winner=None)
        write(OUT/'run_spec.json', spec)
        emit('protocol_frozen', families=spec['grammar']['raw_family_count'], refinements=spec['grammar']['refinement_count'])
        search = SEARCH.search(spec['grammar'], progress=emit)
        write(OUT/'search.json', search)
        write(OUT/'selected_families.json', dict(recipes=search['selected_recipes'], rules=search['selections']))
        emit('selection_frozen', log_matches=search['finite_log_bound_matches'],
             signed_auxiliary_matches=search['auxiliary_signed_needed_matches'],
             signed_refinement_matches=search['refinement_signed_needed_matches'], rules=search['selections'])
        batch = compile_batch(search, SEARCH.FINAL_PARENTS)
        write(OUT/'final_program_batch.json', batch)
        write(OUT/'conditional_arguments.json', dict(rules=batch['rules'], arguments=batch['arguments'],
              argument_operations=batch['argument_operations'], uniform_convergence_proved=False, RH_proved=False))
        aggregate = memory_preflight(batch['programs'])
        tasks = [dict(program=p, H=0 if p['constant']=='0' and not p['coefficients'] and not p['steps'] else SEARCH.FINAL_H)
                 for p in batch['programs']]
        emit('whole_domain_audit_started', distinct_programs=len(tasks), workers=2,
             H=SEARCH.FINAL_H, aggregate_memory_reserve_bytes=aggregate)
        rows = []
        with mp.get_context('fork').Pool(2) as pool:
            for row in pool.imap_unordered(audit_one, tasks):
                path = 'norm_%03d.json'%(len(rows)+1)
                write(OUT/path, row)
                rows.append(dict(**row, artifact=path))
                emit('whole_domain_norm_verified', completed=len(rows), total=len(tasks), id=row['id'],
                     norm_squared_decimal=[float(v) for v in interval(row)],
                     tail_provider=row['certificate']['tail']['chosen_provider'])
        by_id = {r['id']: r for r in rows}
        if len(by_id) != len(rows) or set(by_id) != {p['id'] for p in batch['programs']}:
            raise ValueError('incomplete or duplicated final norm coverage')
        assessments = [analyze_case(case, by_id) for case in batch['cases']]
        write(OUT/'assessment.json', dict(cases=assessments, uniform_convergence_proved=False, RH_proved=False))
        obligations = []
        for rule in batch['rules']:
            observed = [r for r in assessments if r['rule']==rule['id']]
            counterexamples = [r['N'] for r in observed if r['logarithmic_forcing_status']=='refuted_at_this_support']
            obligations.append(dict(rule=rule['id'], recipe=rule['recipe'], q=rule['q'], b=rule['b'],
                local_coefficient_limit='proved structurally; necessary only',
                bound=dict(**rule['audit_log_bound'], domain='every integer N>=257',
                           formula='norm(h_N)^2<=A/L(N)^eta',
                           status='REFUTED_FOR_THIS_DOMAIN' if counterexamples else 'OPEN',
                           finite_counterexamples=counterexamples),
                decomposition='h_N=h0_N+v_N; keep norm(h0)^2+2<h0,v>+norm(v)^2 jointly',
                desired_provider='all-scale signed inequality using actual complete arithmetic law',
                dependencies=['ordinary mu/Liouville/convolution source definitions', 'exact rounding recipe',
                              'exact dilation', 'all-scale forcing estimate OPEN', 'pure-floor Mellin implication'],
                forbidden_providers=['RH', 'target convergence', 'finite numerical trend', 'local coefficient limit alone'],
                asymptotic_forcing_convergence='OPEN', family_convergence='OPEN',
                earlier_original_F_and_centered_mobius_bounds='OPEN; not implied by this finite study',
                finite_auxiliary_mechanisms=[r['auxiliary']['mechanism'] for r in observed],
                finite_refinement_mechanisms=[r['refinement']['mechanism'] for r in observed]))
        write(OUT/'proof_search_input.json', dict(schema='compatible-signed-forcing-obligations-v1',
              candidates=obligations, complete_uniform_bound_proved=False, RH_proved=False))
        write(OUT/'next_search_input.json', dict(schema='compatible-floor-bound-feedback-v1',
              authoritative_parent=str((PARENT/'next_search_input.json').relative_to(ROOT)),
              original_F_and_centered_mobius_obligations='retained OPEN in authoritative parent',
              active_route=dict(results=str(OUT.relative_to(ROOT)),
                  proofs=str((OUT/'proof_search_input.json').relative_to(ROOT)),
                  target='norm(1-sum c_n(N) f_n) tends to0',
                  required='independent uniform signed forcing bound; finite certificates and local limits insufficient'),
              next_constructions_implemented=True, next_proof_input=obligations,
              no_prior_study_rerun=True, source_sensitive_bound_proved=False, RH_proved=False))
        report = dict(status='COMPATIBLE_AUXILIARIES_AUDITED_UNIFORM_BOUND_OPEN',
            family_count=search['family_count'], refinement_count=search['refinement_count'],
            fixed_index_limit_certificates=len(search['symbolic_limit_certificates']),
            training_log_matches=search['finite_log_bound_matches'],
            training_auxiliary_signed_needed_matches=search['auxiliary_signed_needed_matches'],
            training_refinement_signed_needed_matches=search['refinement_signed_needed_matches'],
            selected_rules=batch['rules'], whole_domain_norm_certificates=len(rows), final_cases=len(assessments),
            final_bound_status_counts={label:sum(c['logarithmic_forcing_status']==label for c in assessments)
                for label in ('verified_at_this_support', 'refuted_at_this_support', 'unresolved_interval')},
            signed_mechanism_counts={kind:{label:sum(c[kind]['mechanism']==label for c in assessments)
                for label in sorted({c[kind]['mechanism'] for c in assessments})} for kind in ('auxiliary','refinement')},
            tail_provider_counts={label:sum(r['certificate']['tail']['chosen_provider']==label for r in rows)
                                  for label in ('large_sieve','pointwise')},
            family_convergence_proved=False, whole_signed_core_bound_proved=False, RH_proved=False, RH_refuted=False,
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
                raise ValueError('frozen044 source changed: '+name)
        write(OUT/'report.json', report)
        emit('completed', status=report['status'], elapsed_seconds=report['elapsed_seconds'],
             certificates=len(rows), final_bound_status_counts=report['final_bound_status_counts'],
             signed_mechanism_counts=report['signed_mechanism_counts'])
    except Exception as error:
        write(OUT/'failure.json', dict(type=type(error).__name__, message=str(error), elapsed_seconds=time.monotonic()-started))
        raise


if __name__ == '__main__':
    main()
