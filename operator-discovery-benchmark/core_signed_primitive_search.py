"""Infer discrete primitives, then prove or exclude their affordable bounds.

The arithmetic target is never assumed as an endpoint bound.  Exact linear
certificates certify the finite grammar; they do not refute a Mobius bound.
"""
import copy
from fractions import Fraction as Q

import core_cutoff_work_search as ALG
import core_work_moment_proof_search as MOM

STATE = {'A', 'Abar', 'c', 'D', 'Dbar'}
FIXED = {'z', 'zbar'}
EVENT = {'a', 'b', 'bbar', 'x'}
INCREMENTS = {'A': ('b', 'x'), 'Abar': ('bbar', 'x'), 'c': ('a', 'x'),
              'D': ('b',), 'Dbar': ('bbar',)}
SPEC = dict(inverse_increment_depth=1, potential_coefficients='rational',
            basis='real conjugate orbits inferred from source monomials',
            search='all endpoint/residual cost thresholds plus requested cost',
            free_variables='zero', numerical_samples=False)
require = MOM.require


def substitute(poly, replacements, meter):
    result = {}
    for key, coefficient in poly.items():
        term = {(): coefficient}
        for symbol in key:
            term = ALG.multiply(term, replacements.get(symbol, ALG.atom(symbol)), meter, True)
        result = ALG.plus(result, term)
    return result


def canonical(poly, meter):
    E = {(): Q(1), ('c', 'z'): Q(1), ('A', 'z'): Q(-1)}
    out = substitute(poly, {'E': E, 'Ebar': ALG.conjugate(E), 'v': {(): Q(1)}}, meter)
    require(all(set(k) <= STATE | FIXED | EVENT for k in out), 'complete canonical state/event language')
    return out


def joined_source(transition, meter):
    odd, even = [MOM.decode(p) for p in transition['work_sectors'][1:]]
    value = ALG.plus(ALG.multiply(odd, ALG.atom('x'), meter, True),
                     ALG.multiply(even, {('x', 'x'): Q(1)}, meter, True))
    value = canonical(value, meter)
    require(value == ALG.conjugate(value), 'real complete joined work')
    return value


def primitive_basis(source, meter):
    """Reverse one declared state increment; never insert a target energy."""
    keys = set()
    for key in source:
        for variable, increment in INCREMENTS.items():
            remaining = list(key)
            for symbol in increment:
                if symbol not in remaining:
                    break
                remaining.remove(symbol)
            else:
                if set(remaining) <= STATE | FIXED:
                    candidate = tuple(sorted(remaining+[variable]))
                    star = next(iter(ALG.conjugate({candidate: Q(1)})))
                    keys.add(min(candidate, star))
            meter.charge(10+len(key))
    basis = []
    for key in sorted(keys):
        star = next(iter(ALG.conjugate({key: Q(1)})))
        basis.append({key: Q(1)} if star == key else {key: Q(1), star: Q(1)})
    return basis


def delta(potential, meter):
    require(all(set(key) <= STATE | FIXED for key in potential),
            'storage coefficients cannot depend on the current event')
    replacements = {v: ALG.plus(ALG.atom(v), {d: Q(1)}) for v, d in INCREMENTS.items()}
    return ALG.plus(substitute(potential, replacements, meter), ALG.scale(potential, -1))


def initialized(potential, meter):
    unit = substitute(potential, {v: {(): Q(1)} for v in STATE}, meter)
    return ALG.plus(potential, ALG.scale(unit, -1))


def term_cost(key, sigma, heights, endpoint=False):
    require(set(key) <= STATE | FIXED | (set() if endpoint else EVENT), 'licensed cost symbols')
    sigma = Q(sigma)
    require(0 < sigma < 1, 'finite state majorants on the open strip')
    r = sum(key.count(v) for v in ('A', 'Abar', 'D', 'Dbar'))*(1-sigma)
    r -= key.count('a')+sigma*(key.count('b')+key.count('bbar'))
    k = key.count('z')+key.count('zbar')
    require(k in heights, 'each invariant zeta power has its own verified height bound')
    h = heights[k]['bound']
    q = MOM.envelope(r) if endpoint else MOM.summed_power(r)
    return MOM.envelope(Q(q['B_power'])+Q(h['B_power']), Q(q['log_degree'])+Q(h['log_degree']))


def bound(poly, sigma, heights, endpoint=False):
    return MOM.max_envelope([term_cost(k, sigma, heights, endpoint) for k in poly])


def linear_solve(columns, source, constrained, allowed, meter):
    """Exact sparse elimination with an auditable left-null contradiction."""
    rows = {key: {} for key in constrained}
    for index in allowed:
        for key, value in columns[index].items():
            if key in rows:
                rows[key][index] = value
            meter.charge(2)
    pivots = {}
    for key in constrained:
        row, rhs, witness = rows[key], source.get(key, Q(0)), {key: Q(1)}
        while row:
            pivot = min(row)
            if pivot not in pivots:
                coefficient = row[pivot]
                pivots[pivot] = ({k: v/coefficient for k, v in row.items()}, rhs/coefficient,
                                 {k: v/coefficient for k, v in witness.items()})
                meter.charge(10*(len(row)+len(witness)+1))
                break
            old, old_rhs, old_witness = pivots[pivot]
            multiplier = row[pivot]
            row = ALG.plus(row, ALG.scale(old, -multiplier))
            rhs -= multiplier*old_rhs
            witness = ALG.plus(witness, ALG.scale(old_witness, -multiplier))
            meter.charge(15*(len(old)+len(old_witness)+1))
        else:
            if rhs:
                return dict(status='infeasible', dual=ALG.encode(witness), contradiction=str(rhs))
    solution = {}
    for pivot in sorted(pivots, reverse=True):
        row, rhs, _ = pivots[pivot]
        value = rhs-sum((a*solution.get(j, Q(0)) for j, a in row.items() if j != pivot), Q(0))
        if value:
            solution[pivot] = value
        meter.charge(10*len(row))
    return dict(status='feasible', solution=[dict(basis_id=i, coefficient=str(v)) for i, v in sorted(solution.items())])


def compose(basis, solution):
    result = {}
    for term in solution:
        result = ALG.plus(result, ALG.scale(basis[term['basis_id']], Q(term['coefficient'])))
    return result


def certificate(source, basis, solution, sigma, heights, meter):
    potential = compose(basis, solution)
    residual = ALG.plus(source, ALG.scale(delta(potential, meter), -1))
    boundary = initialized(potential, meter)
    endpoint_cost = bound(boundary, sigma, heights, True)
    residual_cost = bound(residual, sigma, heights)
    return dict(potential=ALG.encode(potential), boundary=ALG.encode(boundary), residual=ALG.encode(residual),
        endpoint_bound=endpoint_cost, residual_bound=residual_cost,
        bound=MOM.max_envelope([endpoint_cost, residual_cost]),
        identity='sum_(q=2..V) W_q = F(state_V)-F(state_1)+sum_(q=2..V) R_q',
        every_event_and_zero_mu_history_retained=True, target_bound_assumed=False)


def synthesize(source, sigma, heights, requested, meter):
    require(source == ALG.conjugate(source), 'real source required')
    require(all(set(k) <= STATE | FIXED | EVENT and k.count('x') <= 2 for k in source),
            'canonical reduced ternary input')
    basis = primitive_basis(source, meter)
    columns = [delta(p, meter) for p in basis]
    endpoints = [bound(initialized(p, meter), sigma, heights, True) for p in basis]
    universe = sorted(set(source).union(*(set(c) for c in columns)))
    row_costs = {key: term_cost(key, sigma, heights) for key in universe}
    costs = sorted({MOM.cost(c) for c in list(row_costs.values())+endpoints+[requested, MOM.envelope(0)]})
    trials = []
    for power, logs in costs:
        threshold = MOM.envelope(power, logs)
        allowed = [i for i, c in enumerate(endpoints) if MOM.cost(c) <= (power, logs)]
        constrained = [key for key in universe if MOM.cost(row_costs[key]) > (power, logs)]
        result = linear_solve(columns, source, constrained, allowed, meter)
        trials.append(dict(threshold=threshold, allowed_basis=allowed, constrained_rows=len(constrained), **result))
    feasible = [i for i, t in enumerate(trials) if t['status'] == 'feasible']
    require(feasible, 'finite elementary absolute baseline remains available')
    chosen = min(feasible, key=lambda i: MOM.cost(trials[i]['threshold']))
    proved = certificate(source, basis, trials[chosen]['solution'], sigma, heights, meter)
    require(MOM.cost(proved['bound']) <= MOM.cost(trials[chosen]['threshold']), 'all endpoint and residual costs paid')
    # Separately ask whether all explicitly signed event rows are a coboundary.
    # Deterministic head changes remain in the residual and must be bounded.
    signed_rows = [k for k in universe if 'x' in k]
    exact = linear_solve(columns, source, signed_rows, list(range(len(basis))), meter)
    if exact['status'] == 'feasible':
        exact['certificate'] = certificate(source, basis, exact['solution'], sigma, heights, meter)
    return dict(spec=copy.deepcopy(SPEC), source=ALG.encode(source), sigma=str(Q(sigma)), requested=requested,
        basis=[ALG.encode(p) for p in basis], basis_endpoint_costs=endpoints,
        trials=trials, selected_trial=chosen, certificate=proved,
        unconstrained_signed_elimination=exact, baseline=bound(source, sigma, heights),
        requested_bound_proved=MOM.meets(proved['bound'], requested),
        finite_grammar_only=True, arithmetic_bound_refuted=False,
        uniform_domain='all dyadic B>=1 and every integer B<V<=2B; common height fixed during telescoping')


def source_binding(parent, meter):
    require(parent['schema'] == 'core-work-moment-proof-feedback-v1', 'published moment proof feedback')
    view = dict(parent, schema='core-cutoff-prefix-projection-feedback-v1')
    binding = MOM.source_binding(view, meter)
    require(binding == parent['work_moment_proof_search']['binding'], 'complete unchanged signed source')
    return binding


def search(parent, meter):
    binding = source_binding(parent, meter)
    target = parent['cutoff_work_targets'][0]
    transition = target['programs'][target['selected_program']]['transition']
    source = joined_source(transition, meter)
    heights = {t['zeta_power']: t['height'] for t in parent['work_moment_proof_search']['moment_library']}
    requested = MOM.envelope(binding['inherited_bound']['power'])
    result = synthesize(source, target['sigma'], heights, requested, meter)
    # Detect this exact restatement AFTER solving; it is not a search seed.
    p = canonical(MOM.decode(transition['parent']), meter)
    energy = ALG.multiply(p, ALG.conjugate(p), meter)
    primitive = result['unconstrained_signed_elimination']
    restatement = primitive['status'] == 'feasible' and (
        MOM.decode(primitive['certificate']['boundary']) == initialized(energy, meter))
    return dict(schema='core-signed-primitive-search-v1', binding=binding, search=result,
        inherited_height_library=copy.deepcopy(parent['work_moment_proof_search']['moment_library']),
        common_window=copy.deepcopy(parent['prefix_projection_search']['proof_search']['common_window']),
        exact_primitive_is_original_energy_restatement=restatement,
        supplied_rules=dict(review='CORE_SIGNED_PRIMITIVE_SEARCH_REVIEW_029.txt',
            Mobius_reciprocal_bound='N*c_N=1+sum_(d<=N) mu(d)*{N/d}; abs(c_N)<=2',
            moment_library='unchanged independently verified parent certificates',
            formal_proof_assistant_verified=False),
        statistics=dict(source_monomials=len(source), inferred_potential_basis=len(result['basis']),
            cost_thresholds=len(result['trials']), infeasible_thresholds=sum(t['status']=='infeasible' for t in result['trials']),
            signed_elimination_found=primitive['status']=='feasible',
            requested_bound_proved=result['requested_bound_proved'],
            actual_arithmetic_observations=0, fitted_constants=0, runtime_model_calls=0),
        whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, result, artifact):
    out = copy.deepcopy(parent)
    out.update(schema='core-signed-primitive-feedback-v1', status='signed_primitive_proof_search_complete',
        parent_obligation_file='candidate10_work_moment_proof_obligation.json', complete_search_artifact=artifact)
    out['signed_primitive_search'] = copy.deepcopy(result)
    out['inherited_signed_primitive_tasks'] = copy.deepcopy(parent['next_search_tasks'])
    out['next_search_tasks'] = [copy.deepcopy(parent['next_search_tasks'][0]), dict(priority=1,
        search_kind='supply_arithmetic_endpoint_control_or_extend_signed_primitive_language',
        target_id=result['binding']['target_id'], status='open',
        exact_failed_requested_threshold=next(t for t in result['search']['trials'] if t['threshold']==result['search']['requested']),
        best_proved_bound=result['search']['certificate']['bound'],
        original_energy_restatement=result['exact_primitive_is_original_energy_restatement'],
        failure_scope='only source-inferred polynomial primitives with existing endpoint and residual majorants',
        arithmetic_bound_refuted=False, complete_source_and_alternatives_preserved=True)]
    out['next_search_tasks'].extend(copy.deepcopy(parent['next_search_tasks'][1:]))
    return out
