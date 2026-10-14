"""Independent replay of finite rational-frequency bound arguments.

The elementary rules are a supplied trust base.  This checker audits their
composition and finite search coverage; an unsupported Mellin bridge stays open.
It imports no implementation from the argument producer.
"""
import copy
import itertools
import math
from fractions import Fraction

RULES = ('bounded_sawtooth', 'mean_from_supremum', 'sawtooth_fourier',
         'absolute_cofactor', 'complete_divisor_inverse', 'coprime_dilation_inverse',
         'parseval_uniform_cofactor', 'parseval_keep_cutoff', 'parseval_inverse',
         'weighted_Abel', 'interval_from_supremum', 'finite_dilation_spacing',
         'source_prefix_auxiliary')
WINDOWS = ('0', '1/2', '1', '2', '3', '6')
SPEC = dict(rules=list(RULES), window_powers=list(WINDOWS), depth_limit=12,
            node_limit=4096, selection='exponent, logs, assumptions, constant, proof size',
            runtime_model_calls=0, numerical_fit=False)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def rational(value, meter):
    require(type(value) in (str, int, Fraction), 'exact rational type')
    if isinstance(value, str):
        require(len(value) <= 2600, 'bounded rational text')
    try:
        q = Fraction(value)
    except (ValueError, ZeroDivisionError):
        raise ValueError('exact rational encoding') from None
    bits = max(abs(q.numerator).bit_length(), q.denominator.bit_length())
    meter.charge(1 + bits // 64)
    require(bits <= 4096, 'bounded rational size')
    return q


def equal(actual, expected, meter, label):
    """Structural equality also distinguishes booleans from integer certificates."""
    meter.charge()
    require(type(actual) is type(expected), label + ': type')
    if isinstance(expected, dict):
        require(actual.keys() == expected.keys(), label + ': fields')
        for key in expected:
            equal(actual[key], expected[key], meter, label)
    elif isinstance(expected, list):
        require(len(actual) == len(expected), label + ': coverage')
        for a, b in zip(actual, expected):
            equal(a, b, meter, label)
    else:
        require(actual == expected, label + ': value')


def auxiliary(kind, theta='0', profile='bounded', support='0', mass='0'):
    return dict(kind=kind, theta=str(theta), profile=profile,
                support_power=str(support), l1_power=str(mass))


def validate_goal(g, meter):
    require(type(g) is dict and type(g.get('kind')) is str, 'typed goal')
    kind = g['kind']
    if kind in {'component_mellin', 'signed_convolution_mellin_bridge'}:
        require(set(g) == {'kind', 'p', 'm', 'sigma', 'theta', 'required'}, 'source goal fields')
        require(type(g['p']) is int and g['p'] >= 0 and type(g['m']) is int and g['m'] >= 1,
                'Dirichlet powers')
        require(0 < rational(g['sigma'], meter) < 1 and 0 < rational(g['theta'], meter) < 1,
                'Mellin and residue domain')
        require(type(g['required']) is dict and 'U_power' in g['required'], 'required bound object')
        rational(g['required']['U_power'], meter)
    elif kind in {'pointwise2', 'spectrum', 'cofactor', 'reciprocal', 'variance', 'interval'}:
        require(set(g) == {'kind', 'theta', 'profile', 'support_power', 'l1_power'}, 'auxiliary fields')
        require(g['profile'] in {'bounded', 'mobius'}, 'arithmetic profile')
        q = [rational(g[k], meter) for k in ('theta', 'support_power', 'l1_power')]
        require(min(q) >= 0, 'nonnegative decay/support/mass')
        require(kind == 'interval' or q[1:] == [0, 0], 'only finite interval lifts have support')
        require(all(type(g[key]) is str and g[key] == str(value)
                    for key,value in zip(('theta','support_power','l1_power'),q)), 'canonical rational goal')


def applications(g):
    k = g['kind']
    c = lambda kind, t=None: auxiliary(kind, g['theta'] if t is None else t, g['profile'])
    if k in ('pointwise2', 'spectrum'):
        return [(('bounded_sawtooth' if k == 'pointwise2' else 'sawtooth_fourier'), [])]
    if k == 'reciprocal':
        return [('complete_divisor_inverse', [])] if g['profile'] == 'mobius' else []
    if k == 'cofactor':
        return [('absolute_cofactor', [])] + ([('coprime_dilation_inverse', [c('reciprocal')])]
                                           if g['profile'] == 'mobius' else [])
    if k == 'variance':
        out = [('mean_from_supremum', [c('pointwise2')])]
        out.extend((rule, [c('spectrum'), c('cofactor')]) for rule in
                   ('parseval_uniform_cofactor', 'parseval_keep_cutoff', 'parseval_inverse'))
        if Fraction(g['theta']) > 0:
            out.append(('weighted_Abel', [c('variance', '0')]))
        return out
    if k == 'interval':
        return [('interval_from_supremum', [c('pointwise2')]),
                ('finite_dilation_spacing', [c('variance')])]
    if k == 'component_mellin':
        bridge = dict(g, kind='signed_convolution_mellin_bridge')
        return [('source_prefix_auxiliary', [auxiliary('interval', profile='mobius',
                                                       support=g['p'], mass=g['p']), bridge])]
    return []


def env(c, u=0, l=0, logs=0):
    return dict(constant=str(Fraction(c)), U_power=str(Fraction(u)),
                L_power=str(Fraction(l)), log_degree=logs)


def sum_bound(decay):
    if decay == 1:
        return Fraction(1), Fraction(0), 1
    if decay < 1:
        return 1 / (1-decay), 1-decay, 0
    return decay / (decay-1), Fraction(0), 0


def certify(rule, g, parents, meter):
    """Replay one reviewed rule, including all domain/provider conditions."""
    t = rational(g.get('theta', 0), meter)
    value, details = None, {}
    if rule == 'bounded_sawtooth':
        c, u, log = sum_bound(t)
        value = [env(c*c/4, 2*u, logs=2*log)]
        details = dict(reason='abs(B_d(n))<=1/2; retain d^-theta in the power sum')
    elif rule == 'mean_from_supremum':
        value = copy.deepcopy(parents[0]['bound'])
    elif rule == 'sawtooth_fourier':
        details = dict(coefficient='-K_r/(r*(1-exp(-2*pi*i*a/r)))',
            K_r='r^-theta * sum_(k<=U/r) w_(kr)/k^(1+theta)',
            frequencies='all reduced a/r with 2<=r<=U, 1<=a<r',
            residue_sum='sum_(a,r)=1 abs(1-exp(2*pi*i*a/r))^-2 = J2(r)/12',
            collisions_grouped_before_absolute_values=True,
            zero_frequency='removed exactly, not assumed small')
    elif rule == 'absolute_cofactor':
        details = dict(provider='absolute', bound='r^-theta * H_floor(U/r)^(1+theta)',
                       cutoff_dependence_retained=True)
    elif rule == 'complete_divisor_inverse':
        require(g['profile'] == 'mobius', 'divisor inverse assumption')
        details = dict(provider='reciprocal_inverse', bound='2',
            identity='N*c_N=1+sum_(d<=N) mu(d)*{N/d}', all_primes_and_scales=True)
    elif rule == 'coprime_dilation_inverse':
        if g['profile'] != 'mobius' or parents[0]['details'].get('provider') != 'reciprocal_inverse':
            return None
        details = dict(provider='inverse', bound='2*r^(1-theta)/phi(r)',
            non_squarefree_conductor_zero=True,
            identity='C_r(T)=sum_(m|r^infinity,m<=T) c_floor(T/m)/m',
            weighting='Abel summation preserves the uniform cofactor bound for theta>=0')
    elif rule.startswith('parseval_'):
        provider = parents[1]['details'].get('provider')
        if rule == 'parseval_keep_cutoff':
            if provider != 'absolute' or t:
                return None
            value = [env(Fraction(1, 2), 1)]
            details = dict(summation='swap r,k,l; count r<=U/max(k,l) before bounding',
                identity='sum_r H_floor(U/r)^2=sum_(k,l<=U) floor(U/max(k,l))/(k*l)',
                majorant='sum_(k,l>=1) 1/(k*l*max(k,l))<=5<6', generic_bounded_weights=True)
        elif rule == 'parseval_uniform_cofactor':
            if provider != 'absolute':
                return None
            c, u, log = sum_bound(2*t)
            factor = Fraction(1, 12) if not t else (1+1/t)**2/12
            value = [env(c*factor, u, logs=log + (0 if t else 2))]
            details = dict(summation='uniform cofactor maximum then sum r^-2theta',
                           generic_bounded_weights=True)
        else:
            if provider != 'inverse':
                return None
            c, u, log = sum_bound(2*t)
            value = [env(9*c, u, logs=log)]
            details = dict(summation='Abel from sum_(r<=V) (r/phi(r))^2 <=27*V',
                           generic_bounded_weights=False)
    elif rule == 'weighted_Abel':
        bound = parents[0]['bound']
        if t <= 0 or not bound or len(bound) != 1:
            return None
        b = bound[0]
        if b['log_degree'] or Fraction(b['L_power']):
            return None
        a = rational(b['U_power'], meter)/2
        require(a >= 0, 'Abel growth domain')
        c = rational(b['constant'], meter)
        if t == a:
            value = [env(c*max(1, t)**2, logs=2)]
        else:
            multiplier = a/(a-t) if t < a else t/(t-a)
            value = [env(c*multiplier**2, max(0, 2*(a-t)))]
        details = dict(reason='Abel in the common-period Hilbert norm of all partial divisor sums',
                       retains_unit_endpoint=True)
    elif rule in ('interval_from_supremum', 'finite_dilation_spacing'):
        d = rational(g['support_power'], meter)
        h = rational(g['l1_power'], meter)
        totals = {}
        for b in parents[0]['bound']:
            c = rational(b['constant'], meter)
            u = rational(b['U_power'], meter) + 2*h
            rows = [(c, u, Fraction(1), b['log_degree'])]
            if rule == 'finite_dilation_spacing':
                rows.append((2*(1+d)*c, u+2*(1+d), Fraction(0), b['log_degree']+1))
            for c, u, l, log in rows:
                key = (u, l, log)
                totals[key] = totals.get(key, 0) + c
        value = [env(c, *k) for k, c in sorted(totals.items())]
        if rule == 'finite_dilation_spacing':
            details = dict(domain='every integer interval of length L>=1 starting at n>=D',
                support='D<=U^support_power, sum abs(h(d))<=U^l1_power',
                frequencies='lift floor(n/d) to d rational modes; group all collisions; denominator<=U*D',
                variance_lift='Minkowski over h; squared norm of each dilation equals the original variance',
                row_sum='L+(U*D)^2*(1+2*log(U*D))',
                short_head='n<D retains exact Qplus(floor(n/d)); Qplus(0)=0',
                all_offdiagonal_terms_paid=True)
        else:
            details = dict(domain='every positive-integer interval of length L>=1',
                support='sum abs(h(d))<=U^l1_power', zero_extension_at_zero=True)
    elif rule == 'source_prefix_auxiliary':
        return None
    else:
        raise ValueError('unlicensed rule')
    facts = {a for p in parents for a in p['assumptions']}
    if rule == 'complete_divisor_inverse':
        facts.update(('mu multiplicative', 'mu*One=delta'))
    return dict(bound=value, details=details, assumptions=sorted(facts))


def verify_plan(result, meter):
    """Audit the DAG and every attempted product of premise certificates."""
    require(type(result) is dict, 'plan object')
    require(set(result) == {'target', 'enabled_rules', 'depth_limit', 'node_limit', 'nodes',
                           'attempts', 'solutions', 'frontier', 'target_proved', 'finite_grammar_only'},
            'complete plan fields')
    enabled = result['enabled_rules']
    require(type(enabled) is list and all(type(r) is str for r in enabled) and
            len(set(enabled)) == len(enabled) and set(enabled) <= set(RULES), 'rule subset')
    depth, cap = result['depth_limit'], result['node_limit']
    require(type(depth) is int and 1 <= depth <= 32 and type(cap) is int and 1 <= cap <= 65536,
            'finite search limits')
    for field in ('nodes', 'attempts', 'solutions', 'frontier'):
        require(type(result[field]) is list, 'certificate list')
    require(len(result['nodes']) <= cap and len(result['attempts']) <= 200000, 'certificate budget')
    nodes, attempts, frontier, cache = [], [], [], {}

    def visit(g, ancestors):
        validate_goal(g, meter)
        # Canonical field tuples are structural memoization, not file hashes.
        token = repr(sorted(g.items()))
        if token in ancestors or len(ancestors) >= depth:
            frontier.append(dict(goal=copy.deepcopy(g), reason='cycle' if token in ancestors else 'depth_limit'))
            return []
        if token in cache:
            return cache[token]
        answer = []
        for rule, children in applications(g):
            if rule not in enabled:
                continue
            groups = [visit(child, ancestors+(token,)) for child in children]
            attempt = dict(goal=copy.deepcopy(g), rule=rule, premises=copy.deepcopy(children),
                           premise_solutions=copy.deepcopy(groups), accepted=[])
            attempts.append(attempt)
            for ids in itertools.product(*groups):
                meter.charge(10 + len(ids))
                step = certify(rule, g, [nodes[i] for i in ids], meter)
                if step is None:
                    continue
                require(len(nodes) < cap, 'node budget exceeded')
                ident = len(nodes)
                node = dict(id=ident, goal=copy.deepcopy(g), rule=rule, premises=list(ids), **step)
                require(ident < len(result['nodes']), 'missing closed argument')
                equal(result['nodes'][ident], node, meter, 'proof rule replay')
                nodes.append(node)
                answer.append(ident)
                attempt['accepted'].append(ident)
        if not answer:
            frontier.append(dict(goal=copy.deepcopy(g), reason='no_closed_argument_in_enabled_grammar'))
        cache[token] = answer
        return answer

    solutions = visit(result['target'], ())
    equal(result['nodes'], nodes, meter, 'node coverage')
    equal(result['attempts'], attempts, meter, 'application coverage')
    equal(result['solutions'], solutions, meter, 'root solutions')
    equal(result['frontier'], frontier, meter, 'open leaves')
    equal(result['target_proved'], bool(solutions), meter, 'closed root status')
    equal(result['finite_grammar_only'], True, meter, 'finite grammar scope')
    return dict(verified=True, arguments=len(nodes), applications=len(attempts),
                target_proved=bool(solutions))


def selections(plan, meter, solutions=None):
    nodes = plan['nodes']
    solutions = plan['solutions'] if solutions is None else solutions
    out = []
    for w in WINDOWS:
        def cost(i):
            n = nodes[i]
            require(n['bound'], 'numerical bound for ranking')
            terms = [(rational(t['U_power'], meter)+Fraction(w)*rational(t['L_power'], meter),
                      t['log_degree'], rational(t['constant'], meter)) for t in n['bound']]
            top = max((u, log) for u, log, c in terms)
            seen, pending = set(), [i]
            while pending:
                j = pending.pop()
                meter.charge()
                if j not in seen:
                    seen.add(j)
                    pending.extend(nodes[j]['premises'])
            return (*top, len(n['assumptions']), sum(c for u, log, c in terms if (u, log) == top),
                    len(seen), i)
        if solutions:
            chosen = min(solutions, key=cost)
            u, log, assumptions, c, size, _ = cost(chosen)
            out.append(dict(L_equals_U_power=w, selected=chosen, exponent=str(u), log_degree=log,
                            arithmetic_assumptions=assumptions, leading_constant=str(c)))
    return out


def verify_compiler(weights, constant, result, meter):
    """Divisor accumulation and Jordan's convolution identity audit the DFT."""
    require(type(weights) in (list, tuple) and 1 <= len(weights) <= 10000, 'finite DFT input')
    a = [rational(w, meter) for w in weights]
    u = len(a)
    k = [Fraction(0) for _ in range(u+1)]
    j = [n*n for n in range(u+1)]
    for d in range(1, u+1):
        # Jordan J2 is recovered from sum_(r|d) J2(r)=d^2.
        for multiple in range(2*d, u+1, d):
            j[multiple] -= j[d]
            meter.charge()
        for multiple in range(d, u+1, d):
            k[d] += a[multiple-1]*Fraction(d, multiple)
            meter.charge()
    mean = rational(constant, meter) + sum((a[d-1]*Fraction(d-1, 2*d) for d in range(1,u+1)), Fraction(0))
    rows = [dict(r=r, K=str(k[r]), J2=j[r]) for r in range(2,u+1) if k[r]]
    variance = sum((k[r]**2*Fraction(j[r], 12*r*r) for r in range(2,u+1)), Fraction(0))
    expected = dict(mean=str(mean), conductors=rows, variance=str(variance),
        coefficient='-K/(r*(1-exp(-2*pi*i*a/r)))', scope='exact finite coefficients; not a uniform inference')
    equal(result, expected, meter, 'discrete compiler')
    return dict(verified=True, mean=str(mean), variance=str(variance))


def source_binding(parent, meter):
    import check_core_signed_primitive_search as PRIOR
    require(parent['schema'] == 'core-signed-primitive-feedback-v1', 'current source publication')
    binding = PRIOR.source_binding(dict(parent, schema='core-work-moment-proof-feedback-v1'), meter)
    equal(binding, parent['signed_primitive_search']['binding'], meter, 'unchanged source binding')
    t = parent['cutoff_work_targets'][0]
    require((t['p'], t['m']) == (2, 3), 'actual component powers')
    return binding


def recovery(p, m):
    return dict(mean='C_U=1+(M(U)-c_U)/2', mean_bound_assumed=False,
        zero_mean_prefix='Q_U(n)=sum_(d<=U)mu(d)*({n/d}-(d-1)/(2*d)), n>=1; Qplus(0)=0',
        exact_source='A^p * (C_U*delta+e_U)^{*m} - c_U^m*D_U',
        branches=[dict(coefficient=math.comb(m,j), mean_power=m-j, A_power=p, e_Dirichlet_power=j)
                  for j in range(m+1)],
        all_ordered_cross_terms=[dict(left=j, right=k, coefficient=math.comb(m,j)*math.comb(m,k))
                                 for j in range(m+1) for k in range(m+1)],
        deterministic_head='-c_U^m*D_U and all of its crosses retained',
        missing='signed reciprocal-simplex covariance and Mellin recovery for e_U^{*j}, j>=2, '
                'with the exact mean, unit, head correction, residues and all source crosses',
        pointwise_power_substitution_allowed=False, full_component_bound_proved=False)


def verify_search(parent, result, meter):
    binding = source_binding(parent, meter)
    t = parent['cutoff_work_targets'][0]
    root = dict(kind='component_mellin', p=t['p'], m=t['m'], sigma=t['sigma'], theta=t['theta'],
                required=copy.deepcopy(t['original_low_obligation']['required_upper']))
    inferred = auxiliary('interval', profile='mobius', support=t['p'], mass=t['p'])
    goals = [root, dict(inferred, profile='bounded'), auxiliary('interval', profile='mobius'),
             auxiliary('interval')]
    labels = ['actual_source_argument', 'same_auxiliary_unsigned', 'base_prefix', 'base_prefix_unsigned']
    require(type(result) is dict and type(result.get('trials')) is list and len(result['trials']) == 4,
            'all arithmetic ablations')
    arguments = applications_count = 0
    for trial, goal, label in zip(result['trials'], goals, labels):
        require(set(trial) == {'id', 'proof_search', 'selection'}, 'trial fields')
        equal(trial['id'], label, meter, 'trial identity')
        p = trial['proof_search']
        equal(p['target'], goal, meter, 'source-generated goal')
        for key in ('enabled_rules', 'depth_limit', 'node_limit'):
            equal(p[key], SPEC[{'enabled_rules':'rules'}.get(key,key)], meter, 'frozen search specification')
        audit = verify_plan(p, meter)
        arguments += audit['arguments']
        applications_count += audit['applications']
        equal(trial['selection'], selections(p, meter), meter, 'selected argument')
    full = result['trials'][0]['proof_search']
    attempt = next(a for a in full['attempts'] if a['rule'] == 'source_prefix_auxiliary')
    aux_rank = selections(full, meter, attempt['premise_solutions'][0])
    unsigned = result['trials'][1]['selection']
    advantage = any((Fraction(a['exponent']),a['log_degree']) < (Fraction(b['exponent']),b['log_degree'])
                    for a,b in zip(aux_rank,unsigned))
    expected = dict(schema='core-bound-argument-search-v1', spec=copy.deepcopy(SPEC), binding=binding,
        original_missing_bound=copy.deepcopy(t['original_low_obligation']), inferred_auxiliary=inferred,
        auxiliary_selection=aux_rank, trials=result['trials'], recovery=recovery(t['p'],t['m']),
        discovery_scope=dict(supplied='typed representations and inference rules, reviewed analytically',
            selected_by_detector='subgoals, rule compositions, exact bound costs and scale-dependent choices',
            open_leaves_generated=True, runtime_model_calls=0, formal_proof_assistant_verified=False),
        statistics=dict(arguments=arguments, applications=applications_count, actual_arithmetic_observations=0,
            fitted_constants=0, auxiliary_exponent_advantage_over_unsigned=advantage, full_component_bound_proved=False),
        whole_signed_bound_proved=False, RH_proved=False)
    equal(result, expected, meter, 'search scope and source recovery')
    return dict(verified=True, arguments=arguments, applications=applications_count,
                full_component_bound_proved=False)


def verify_feedback(parent, result, out, artifact, meter):
    audit = verify_search(parent, result, meter)
    expected = copy.deepcopy(parent)
    expected.update(schema='core-bound-argument-feedback-v1', status='bound_arguments_searched_core_open',
                    parent_obligation_file='candidate10_signed_primitive_obligation.json', complete_search_artifact=artifact)
    expected['bound_argument_search'] = copy.deepcopy(result)
    expected['inherited_bound_argument_tasks'] = copy.deepcopy(parent['next_search_tasks'])
    expected['next_search_tasks'] = [copy.deepcopy(parent['next_search_tasks'][0]), dict(priority=1,
        target_id=result['binding']['target_id'], search_kind='close_generated_signed_convolution_bridge',
        status='open', proof_frontier=copy.deepcopy(result['trials'][0]['proof_search']['frontier']),
        exact_recovery=copy.deepcopy(result['recovery']),
        auxiliary_exponent_advantage_over_unsigned=result['statistics']['auxiliary_exponent_advantage_over_unsigned'],
        original_goal_not_replaced=True)] + copy.deepcopy(parent['next_search_tasks'][1:])
    equal(out, expected, meter, 'complete inherited feedback')
    return audit
