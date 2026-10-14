"""Price complete convolution identities and search centered truncation controls.

All prefix estimates have uniform constants and every finite head is priced.
Analytic moments and local coefficient identities remain separate objects.
"""
import copy
import itertools
from fractions import Fraction as Q

import core_convolution_argument_search as OLD

require = OLD.require
add, scale, mul, power = OLD.add, OLD.scale, OLD.mul, OLD.power
encode, decode, solve, compose = OLD.encode, OLD.decode, OLD.solve, OLD.compose


def term(c=1, u=0, x=0, lu=0, lx=0):
    return dict(constant=str(Q(c)), U_power=str(Q(u)), X_power=str(Q(x)), logU_degree=lu, logX_degree=lx)


def collect(rows):
    out = {}
    for t in rows:
        key = (Q(t['U_power']), Q(t['X_power']), t['logU_degree'], t['logX_degree'])
        out[key] = out.get(key, Q(0))+Q(t['constant'])
    return [term(c, *key) for key, c in sorted(out.items()) if c]


def times(rows, c):
    return [dict(t, constant=str(Q(t['constant'])*c)) for t in rows if c]


def score(rows, rho):
    require(rows, 'nonempty proved envelope')
    leading = max((Q(t['X_power'])+rho*Q(t['U_power']), t['logU_degree']+t['logX_degree']) for t in rows)
    c = sum((Q(t['constant']) for t in rows if
             (Q(t['X_power'])+rho*Q(t['U_power']), t['logU_degree']+t['logX_degree']) == leading), Q(0))
    return leading+(c,)


def fractions(limit=6):
    require(type(limit) is int and 2 <= limit <= 12, 'bounded rational grammar')
    return sorted({Q(a, b) for b in range(2, limit+1) for a in range(1, b)})


def profile_check(profile):
    require(profile in {'mobius', 'bounded'}, 'declared arithmetic assumptions')


def mass_bound(m, profile):
    return [term(3**m, 0, 1, m if profile == 'bounded' else 0, 2*m-1)]


def lift_finite(bound, caps, profile):
    """Each factor has |f|<=3 d2, or <=3(1+log U)d2, cutoff<=X^cap."""
    profile_check(profile)
    caps = list(map(Q, caps))
    require(all(0 < a <= 1 for a in caps), 'finite relative cutoffs')
    out = []
    for row in bound:
        beta = Q(row['X_power'])
        require(0 <= beta <= 1, 'available weighted divisor decay')
        k = len(caps)
        if beta < 1:
            c, x, logs = (3/(1-beta))**k, beta+(1-beta)*sum(caps, Q(0)), k
        else:
            c, x, logs = Q(3)**k, Q(1), 2*k
        out.append(term(Q(row['constant'])*c, row['U_power'], x,
            row['logU_degree']+(k if profile == 'bounded' else 0), row['logX_degree']+logs))
    return collect(out)


def finite_power_price(m, alpha, profile, rho):
    candidates = [dict(rule='coefficient_mass', bound=mass_bound(m, profile)),
        dict(rule='keep_one_signed_prefix', bound=lift_finite([term(2, 1)], [alpha]*(m-1), profile))]
    if m*alpha <= 1:
        candidates.append(dict(rule='complete_rectangle', bound=[term(2**m, m)]))
    chosen = min(range(len(candidates)), key=lambda i: score(candidates[i]['bound'], rho)+(i,))
    return dict(candidates=candidates, selected=chosen, bound=candidates[chosen]['bound'])


def prefix_library(profile, rho, meter, maximum=3):
    profile_check(profile); rho = Q(rho)
    require(0 < rho < 1 and type(maximum) is int and 1 <= maximum <= 4, 'prefix grammar domain')
    levels = [dict(power=1, selected=0, candidates=[dict(rule='bounded_prefix', bound=[term(2, 1)])],
                   bound=[term(2, 1)])]
    for m in range(2, maximum+1):
        candidates = [dict(rule='coefficient_mass', bound=mass_bound(m, profile))]
        for alpha in fractions():
            if m*alpha < 1:
                continue
            source = {('E',)*m: Q(1)}
            basis = [{('E',)*(m-k)+('T',)*k: Q(1)} for k in range(1, m+1)]
            ideal = power({('E',): Q(1), ('T',): Q(-1)}, m)
            cert = solve(basis+[ideal], source, meter)
            require(cert['status'] == 'feasible', 'complete power reduction')
            priced, bound = [], []
            for row in cert['solution']:
                if row['column'] == m:
                    continue
                k = row['column']+1
                if k == m:
                    pricing = finite_power_price(m, alpha, profile, rho)
                else:
                    pricing = dict(rule='weighted_finite_lift', premise_power=m-k,
                        bound=lift_finite(levels[m-k-1]['bound'], [alpha]*k, profile))
                priced.append(dict(column=row['column'], coefficient=row['coefficient'], pricing=pricing))
                bound += times(pricing['bound'], abs(Q(row['coefficient'])))
            candidates.append(dict(rule='synthesized_hyperbola', alpha=str(alpha),
                source=encode(source), basis=[encode(b) for b in basis], ideal=encode(ideal), certificate=cert,
                priced_terms=priced, bound=collect(bound), full_product_indicator_retained=True))
        chosen = min(range(len(candidates)), key=lambda i: score(candidates[i]['bound'], rho)+(i,))
        levels.append(dict(power=m, candidates=candidates, selected=chosen, bound=candidates[chosen]['bound']))
    return dict(profile=profile, rho=str(rho), levels=levels,
        quantifier='every fixed f with |prefix_f(x)|<=2U and |f(n)|<=K*d2(n), every real x>=1, uniformly in any truncation of f',
        K='3' if profile == 'mobius' else '3*(1+log U)', ordinary_critical_moment_convergence_assumed=False)


def substitute(poly, mapping):
    out = {}
    for key, c in poly.items():
        value = {(): c}
        for name in key:
            value = mul(value, mapping[name])
        out = add(out, value)
    return out


def normalize(g, meter):
    joined = add(mul(decode(g['one_e_coefficient']), {('e',): Q(1)}), decode(g['finite_head']))
    mapping = {'C': {('C',): Q(1)}}
    for old, new in [('e', 'E'), ('t', 'T'), ('r', 'R')]:
        mapping[old] = {(new,): Q(1), ('C',): Q(-1)}
    affine = substitute(joined, mapping)
    vanished = substitute(decode(g['vanishing_remainder']), mapping)
    require(add(affine, vanished) == {('E',)*g['m']: Q(1)}, 'complete affine source reconstruction')
    reduced = {k: c for k, c in affine.items() if 'C' not in k}
    remainder = {k: c for k, c in vanished.items() if 'C' not in k}
    require(add(reduced, remainder) == {('E',)*g['m']: Q(1)}, 'parameter-independent tail ideal')
    meter.charge(20*(len(affine)+len(vanished)+1))
    return dict(alpha=g['alpha'], beta=g['beta'], affine_join=encode(affine),
        affine_remainder=encode(vanished), normalized_join=encode(reduced), normalized_remainder=encode(remainder),
        license='tails E-T and E-R are independent of C; specialize the complete polynomial identity at C=0',
        domain='coefficients n<=N with the original fixed integer cutoffs', full_source_retained=True)


def geometry_columns(alpha, beta, maximum_e=2):
    alpha, beta = Q(alpha), Q(beta)
    require(0 < alpha <= beta < 1 and maximum_e in (1, 2), 'strict-short cubic geometry')
    basis = [{key: Q(1)} for key in itertools.combinations_with_replacement(('E', 'R', 'T'), 3)
             if key.count('E') <= maximum_e]
    ideals, witnesses = [], []
    for a in range(4):
        for b in range(4-a):
            if a+b and a*alpha+b*beta >= 1:
                factor = mul(power({('E',): Q(1), ('T',): Q(-1)}, a),
                             power({('E',): Q(1), ('R',): Q(-1)}, b))
                for key in itertools.combinations_with_replacement(('E', 'R', 'T'), 3-a-b):
                    ideals.append(mul({key: Q(1)}, factor))
                    witnesses.append(dict(t_tail_power=a, r_tail_power=b, multiplier=list(key),
                                          support_power=str(a*alpha+b*beta)))
    return basis, ideals, witnesses


def monomial_price(key, alpha, beta, library, meter):
    profile, rho = library['profile'], Q(library['rho'])
    caps = dict(E=Q(1), T=Q(alpha), R=Q(beta))
    candidates = [dict(rule='coefficient_mass', bound=mass_bound(len(key), profile))]
    if 'E' not in key and sum((caps[v] for v in key), Q(0)) <= 1:
        candidates.append(dict(rule='complete_rectangle', bound=[term(2**len(key), len(key))]))
    for name in sorted(set(key)):
        count = key.count(name)
        require(name != 'E' or count < 3, 'no target restatement as a premise')
        bound = lift_finite(library['levels'][count-1]['bound'], [caps[n] for n in key if n != name], profile)
        candidates.append(dict(rule='uniform_power_then_finite_lift', base=name, premise_power=count, bound=bound))
        meter.charge(20)
    selected = min(range(len(candidates)), key=lambda i: score(candidates[i]['bound'], rho)+(i,))
    return dict(candidates=candidates, selected=selected, bound=candidates[selected]['bound'])


def complete_geometry(alpha, beta, library, meter):
    basis, ideals, support = geometry_columns(alpha, beta)
    prices = [monomial_price(next(iter(b)), alpha, beta, library, meter) for b in basis]
    costs = [score(p['bound'], Q(library['rho']))[:2] for p in prices]
    thresholds = sorted(set(costs))
    source, trials = {('E',)*3: Q(1)}, []
    for threshold in thresholds:
        allowed = [i for i, c in enumerate(costs) if c <= threshold]
        cert = solve([basis[i] for i in allowed]+ideals, source, meter)
        row = dict(threshold=[str(threshold[0]), threshold[1]], allowed=allowed, certificate=cert)
        if cert['status'] == 'feasible':
            representation, bound = {}, []
            for item in cert['solution']:
                if item['column'] < len(allowed):
                    i = allowed[item['column']]; c = Q(item['coefficient'])
                    representation = add(representation, scale(basis[i], c))
                    bound += times(prices[i]['bound'], abs(c))
            row.update(representation=encode(representation), bound=collect(bound))
        trials.append(row)
    viable = [i for i, row in enumerate(trials) if row['certificate']['status'] == 'feasible']
    require(viable, 'fully priced cubic representation')
    chosen = min(viable, key=lambda i: score(trials[i]['bound'], Q(library['rho']))+(i,))
    return dict(alpha=str(Q(alpha)), beta=str(Q(beta)), basis=[encode(b) for b in basis],
        ideals=[encode(i) for i in ideals], support_certificates=support, monomial_prices=prices,
        trials=trials, selected=chosen, bound=trials[chosen]['bound'], every_finite_head_priced=True,
        scope='complete E^3 prefix, uniformly for integer N>=1; outer A and K not yet applied')


def lift_outer(bound, p, m, profile):
    """Bound A^p*f^m-c^m*One_[1,U]; the current source has m-p=1."""
    profile_check(profile)
    require(type(p) is int and 0 <= p <= 6 and type(m) is int and m == p+1,
            'outer source with the licensed One_[1,U] head, m-p=1')
    out = []
    for row in bound:
        beta = Q(row['X_power'])
        require(0 <= beta <= 1, 'outer weighted mass rule')
        if beta < 1:
            c, u, logs = (1/(1-beta))**p, p*(1-beta), 0
        else:
            c, u, logs = Q(1), Q(0), p
        out.append(term(Q(row['constant'])*c, Q(row['U_power'])+u, beta,
                        row['logU_degree']+logs, row['logX_degree']))
    out.append(term(2**m if profile == 'mobius' else 1, 1, 0, m if profile == 'bounded' else 0))
    return collect(out)


def square_energy(bound):
    return collect([term(Q(a['constant'])*Q(b['constant']), Q(a['U_power'])+Q(b['U_power']),
        Q(a['X_power'])+Q(b['X_power'])-1, a['logU_degree']+b['logU_degree'], a['logX_degree']+b['logX_degree'])
        for a in bound for b in bound])


def transfer_search(p, theta, rho, meter, profile='mobius'):
    profile_check(profile)
    theta, rho = Q(theta), Q(rho)
    require(type(p) is int and 0 <= p <= 6 and 0 < theta < 1 and 0 < rho < 1,
            'centered cubic transfer parameters')
    C1 = Q(216)/(theta*(1-theta)**(p+2))
    C2 = 144*((2 if profile == 'mobius' else 3)/(1-theta)+8)/(theta*(1-theta)**p)
    tail_logs, defect_logs = (4, 0) if profile == 'mobius' else (8, 4)
    trials = []
    for alpha_text, beta_text in OLD.geometry_grid():
        alpha, beta = Q(alpha_text), Q(beta_text)
        if alpha < rho:
            continue
        _, ideals, support = geometry_columns(alpha, beta)
        source = {('E',)*3: Q(1), ('R',)*3: Q(-1)}
        for base, cutoff in [('T', alpha), ('R', beta)]:
            column = mul({(base, base): Q(1)}, {('E',): Q(1), ('R',): Q(-1)})
            cert = solve([column]+ideals, source, meter)
            row = dict(alpha=str(alpha), beta=str(beta), base=base, effective_short_cutoff=str(cutoff),
                column=encode(column), support_certificates=support, certificate=cert)
            if cert['status'] == 'feasible':
                coefficient = sum((Q(v['coefficient']) for v in cert['solution'] if v['column'] == 0), Q(0))
                require(coefficient == 3, 'moment-defect rule for the solved cubic coefficient')
                e1 = 2*rho*(1+p*(1-theta))+4*(1-theta)*cutoff+2*theta-1-2*theta*beta
                e2 = 2*rho*(2+(p+1)*(1-theta))+2*theta-1-2*theta*(cutoff+beta)
                row.update(coefficient=str(coefficient), normalized_error_energy=[
                    dict(constant=str(8*C1*C1), N_power=str(e1), log_degree=tail_logs),
                    dict(constant=str(32*C2*C2), N_power=str(e2), log_degree=defect_logs)],
                    subcritical_padding=max(e1, e2) < 0,
                    moment_defect='A(theta)^p*J(theta)*(E(theta)^2+E(theta)*R(theta)+R(theta)^2-3*S(theta)^2)',
                    analytic_moment_not_inferred_from_local_identity=True)
            trials.append(row)
    eligible = [i for i, t in enumerate(trials) if t.get('subcritical_padding')]
    selected = min(eligible, key=lambda i: (Q(trials[i]['beta']),
        max(Q(t['N_power']) for t in trials[i]['normalized_error_energy']), Q(trials[i]['alpha']), i)) if eligible else None
    return dict(p=p, theta=str(theta), rho=str(rho), profile=profile, trials=trials, selected=selected,
        C1=str(C1), C2=str(C2),
        energy='N^-2*sum_(1<=n<=N)|S(n)|^2; all integer U,N>=1 with U<=N^rho',
        domain='t=floor(N^alpha)>=U, r=floor(N^beta)>=t; fixed N; S denotes the chosen short E truncation',
        exact_join='S_F=S_R+S_(hJ)-(mF-mR-h(theta)*J(theta))*n^theta/theta; h=3*A^p*S^2',
        retained_head='the SAME -c^3*D in F=A^p*E^3-c^3*D and Rsource=A^p*R^3-c^3*D',
        comparison='energy(F)<=2*energy(Rsource)+2*error_energy and conversely; error includes both pieces and their cross',
        full_finite_cube_bound_proved=False, global_fixed_U_Mellin_bound_proved=False)


def source_binding(parent, meter):
    require(parent['schema'] == 'core-convolution-argument-feedback-v1', 'current verified input')
    binding = OLD.source_binding(dict(parent, schema='core-bound-argument-feedback-v1'), meter)
    require(binding == parent['convolution_argument_search']['binding'], 'complete original source')
    return binding


def search(parent, meter):
    binding = source_binding(parent, meter)
    target = parent['cutoff_work_targets'][0]
    require((target['p'], target['m'], target['theta']) == (2, 3, '2/3'), 'current full component adapter')
    rho = Q(target['original_low_obligation']['parameters']['alpha'])
    libraries = [prefix_library(profile, rho, meter) for profile in ('mobius', 'bounded')]
    normalizations = [normalize(g, meter) for g in parent['convolution_argument_search']['geometries']]
    geometries = [complete_geometry(a, b, libraries[0], meter) for a, b in OLD.geometry_grid()]
    selected = min(range(len(geometries)), key=lambda i: score(geometries[i]['bound'], rho)+(i,))
    # Both universal and geometry-derived arguments compete after the COMPLETE outer source is paid.
    routes = [dict(rule='universal_cubic', bound=lift_outer(libraries[0]['levels'][2]['bound'], 2, 3, 'mobius'))]
    routes += [dict(rule='complete_geometry', geometry=i, bound=lift_outer(g['bound'], 2, 3, 'mobius'))
               for i, g in enumerate(geometries)]
    best = min(range(len(routes)), key=lambda i: score(routes[i]['bound'], rho)+(i,))
    bound = routes[best]['bound']
    comparison = lift_outer(libraries[1]['levels'][2]['bound'], 2, 3, 'bounded')
    transfer = transfer_search(2, target['theta'], rho, meter)
    ablation = transfer_search(2, target['theta'], rho, meter, profile='bounded')
    return dict(schema='core-complete-convolution-search-v1', binding=binding, normalizations=normalizations,
        libraries=libraries, geometries=geometries, selected_geometry=selected, full_prefix_routes=routes,
        selected_prefix_route=best, full_source_prefix_bound=bound, generic_comparison=comparison,
        before_outer_K_energy_bound=square_energy(bound), centered_transfer=transfer,
        transfer_ablation=ablation,
        frontier=dict(finite_cube='uniform subpower centered energy of A^2*R^3-c^3*D at the selected moving cutoff',
            original_Mellin=copy.deepcopy(target['original_low_obligation']),
            ordinary_moment_test=dict(prefix_X_power=str(max(Q(t['X_power']) for t in bound)),
                sigma=target['sigma'], theta=target['theta'], strict_convergence_proved=False)),
        statistics=dict(normalizations=len(normalizations), complete_geometries=len(geometries),
            complete_thresholds=sum(len(g['trials']) for g in geometries), transfer_trials=len(transfer['trials']),
            subcritical_transfer_candidates=sum(t.get('subcritical_padding', False) for t in transfer['trials']),
            arithmetic_power_advantage=False, actual_source_observations=0, runtime_model_calls=0),
        supplied_rules='CORE_COMPLETE_CONVOLUTION_BOUND_REVIEW_032.txt',
        full_component_bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, result, artifact):
    out = copy.deepcopy(parent)
    out.update(schema='core-complete-convolution-feedback-v1', status='complete_convolution_search_core_open',
        parent_obligation_file='candidate10_convolution_argument_obligation.json', complete_search_artifact=artifact)
    out['complete_convolution_search'] = copy.deepcopy(result)
    out['inherited_complete_convolution_tasks'] = copy.deepcopy(parent['next_search_tasks'])
    transfer = result['centered_transfer']
    chosen = None if transfer['selected'] is None else transfer['trials'][transfer['selected']]
    out['next_search_tasks'] = [copy.deepcopy(parent['next_search_tasks'][0]), dict(priority=1,
        target_id=result['binding']['target_id'], search_kind='complete_centered_finite_cube', status='open',
        verified_transfer=copy.deepcopy(chosen), exact_source='A^2*(E restricted<=floor(N^beta))^3-c^3*D',
        all_finite_heads_units_and_crosses_required=True, analytic_moment_required=True,
        original_global_Mellin_obligation_retained=True)] + copy.deepcopy(parent['next_search_tasks'][1:])
    return out
