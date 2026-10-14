"""Goal-directed composition of supplied bound rules, with explicit open leaves.

The program chooses arguments; it does not invent its trusted inference rules.
Unsigned ablations prevent a generic averaging bound being called Mobius control.
"""
import copy
import itertools
import math
from fractions import Fraction as Q


RULES = (
    'bounded_sawtooth', 'mean_from_supremum', 'sawtooth_fourier',
    'absolute_cofactor', 'complete_divisor_inverse', 'coprime_dilation_inverse',
    'parseval_uniform_cofactor', 'parseval_keep_cutoff', 'parseval_inverse',
    'weighted_Abel', 'interval_from_supremum', 'finite_dilation_spacing',
    'source_prefix_auxiliary',
)
WINDOW_POWERS = ('0', '1/2', '1', '2', '3', '6')
SPEC = dict(rules=list(RULES), window_powers=list(WINDOW_POWERS),
            depth_limit=12, node_limit=4096, selection='exponent, logs, assumptions, constant, proof size',
            runtime_model_calls=0, numerical_fit=False)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def number(value):
    q = Q(value)
    require(max(abs(q.numerator).bit_length(), q.denominator.bit_length()) <= 4096,
            'bounded exact rational')
    return q


def goal(kind, theta=0, profile='bounded', support_power=0, l1_power=0):
    require(kind in {'pointwise2', 'spectrum', 'cofactor', 'reciprocal', 'variance', 'interval'},
            'typed auxiliary goal')
    require(profile in {'bounded', 'mobius'}, 'explicit arithmetic assumptions')
    theta, d, h = map(number, (theta, support_power, l1_power))
    require(min(theta, d, h) >= 0, 'nonnegative rational decay and support exponents')
    require(kind == 'interval' or (d == 0 and h == 0), 'finite lift belongs to interval goal')
    return dict(kind=kind, theta=str(theta), profile=profile, support_power=str(d), l1_power=str(h))


def envelope(c=1, u=0, l=0, logs=0):
    require(number(c) > 0 and number(logs).denominator == 1 and number(logs) >= 0,
            'positive bound and integer logarithmic degree')
    return dict(constant=str(number(c)), U_power=str(number(u)), L_power=str(number(l)),
                log_degree=int(logs))


def normalize(terms):
    result = {}
    for t in terms:
        key = (number(t['U_power']), number(t['L_power']), t['log_degree'])
        result[key] = result.get(key, Q(0)) + number(t['constant'])
    return [envelope(c, *key) for key, c in sorted(result.items()) if c]


def power_sum(decay):
    """Upper bound on sum_(1<=n<=U) n^-decay, U>=1; log means 1+log U."""
    decay = number(decay)
    require(decay >= 0, 'decreasing power sum')
    if decay < 1:
        return envelope(1/(1-decay), 1-decay)
    if decay == 1:
        return envelope(1, logs=1)
    return envelope(decay/(decay-1))


def child(g, kind, theta=None):
    return goal(kind, g['theta'] if theta is None else theta, g['profile'])


def expansions(g):
    """Generate inference applications from the requested expression, not an answer list."""
    k = g['kind']
    if k == 'pointwise2':
        return [('bounded_sawtooth', [])]
    if k == 'spectrum':
        return [('sawtooth_fourier', [])]
    if k == 'reciprocal':
        return [('complete_divisor_inverse', [])] if g['profile'] == 'mobius' else []
    if k == 'cofactor':
        out = [('absolute_cofactor', [])]
        if g['profile'] == 'mobius':
            out.append(('coprime_dilation_inverse', [child(g, 'reciprocal')]))
        return out
    if k == 'variance':
        out = [('mean_from_supremum', [child(g, 'pointwise2')]),
               ('parseval_uniform_cofactor', [child(g, 'spectrum'), child(g, 'cofactor')]),
               ('parseval_keep_cutoff', [child(g, 'spectrum'), child(g, 'cofactor')]),
               ('parseval_inverse', [child(g, 'spectrum'), child(g, 'cofactor')])]
        if number(g['theta']) > 0:
            out.append(('weighted_Abel', [child(g, 'variance', 0)]))
        return out
    if k == 'interval':
        return [('interval_from_supremum', [child(g, 'pointwise2')]),
                ('finite_dilation_spacing', [child(g, 'variance')])]
    if k == 'component_mellin':
        # A prefix norm is useful only with a further, presently unsupported bridge.
        return [('source_prefix_auxiliary', [
            goal('interval', 0, 'mobius', g['p'], g['p']),
            dict(kind='signed_convolution_mellin_bridge', p=g['p'], m=g['m'],
                 sigma=g['sigma'], theta=g['theta'], required=copy.deepcopy(g['required']))])]
    return []


def apply(rule, g, premises):
    """One checked mathematical step; None means that rule's side condition fails."""
    theta = number(g.get('theta', 0))
    bounds = [p['bound'] for p in premises]
    details, value = {}, None
    if rule == 'bounded_sawtooth':
        t = power_sum(theta)
        value = [envelope(number(t['constant'])**2/4, 2*number(t['U_power']), logs=2*t['log_degree'])]
        details = dict(reason='abs(B_d(n))<=1/2; retain d^-theta in the power sum')
    elif rule == 'mean_from_supremum':
        value = bounds[0]
    elif rule == 'sawtooth_fourier':
        details = dict(coefficient='-K_r/(r*(1-exp(-2*pi*i*a/r)))',
            K_r='r^-theta * sum_(k<=U/r) w_(kr)/k^(1+theta)',
            frequencies='all reduced a/r with 2<=r<=U, 1<=a<r',
            residue_sum='sum_(a,r)=1 abs(1-exp(2*pi*i*a/r))^-2 = J2(r)/12',
            collisions_grouped_before_absolute_values=True, zero_frequency='removed exactly, not assumed small')
    elif rule == 'absolute_cofactor':
        details = dict(provider='absolute', bound='r^-theta * H_floor(U/r)^(1+theta)',
                       cutoff_dependence_retained=True)
    elif rule == 'complete_divisor_inverse':
        if g['profile'] != 'mobius':
            return None
        details = dict(provider='reciprocal_inverse', bound='2',
            identity='N*c_N=1+sum_(d<=N) mu(d)*{N/d}', all_primes_and_scales=True)
    elif rule == 'coprime_dilation_inverse':
        if g['profile'] != 'mobius' or premises[0]['details'].get('provider') != 'reciprocal_inverse':
            return None
        details = dict(provider='inverse', bound='2*r^(1-theta)/phi(r)',
            non_squarefree_conductor_zero=True,
            identity='C_r(T)=sum_(m|r^infinity,m<=T) c_floor(T/m)/m',
            weighting='Abel summation preserves the uniform cofactor bound for theta>=0')
    elif rule in {'parseval_uniform_cofactor', 'parseval_keep_cutoff', 'parseval_inverse'}:
        provider = premises[1]['details'].get('provider')
        if rule == 'parseval_uniform_cofactor':
            if provider != 'absolute':
                return None
            t = power_sum(2*theta)
            c = Q(1, 12) if theta == 0 else ((1+theta)/theta)**2/12
            value = [envelope(c*number(t['constant']), t['U_power'],
                              logs=t['log_degree']+(2 if theta == 0 else 0))]
            details = dict(summation='uniform cofactor maximum then sum r^-2theta',
                           generic_bounded_weights=True)
        elif rule == 'parseval_keep_cutoff':
            if provider != 'absolute' or theta != 0:
                return None
            value = [envelope(Q(1, 2), 1)]
            details = dict(summation='swap r,k,l; count r<=U/max(k,l) before bounding',
                identity='sum_r H_floor(U/r)^2=sum_(k,l<=U) floor(U/max(k,l))/(k*l)',
                majorant='sum_(k,l>=1) 1/(k*l*max(k,l))<=5<6', generic_bounded_weights=True)
        else:
            if provider != 'inverse':
                return None
            t = power_sum(2*theta)
            value = [envelope(9*number(t['constant']), t['U_power'], logs=t['log_degree'])]
            details = dict(summation='Abel from sum_(r<=V) (r/phi(r))^2 <=27*V',
                           generic_bounded_weights=False)
    elif rule == 'weighted_Abel':
        if theta <= 0 or len(bounds[0]) != 1:
            return None
        t = bounds[0][0]
        if t['log_degree'] or number(t['L_power']) != 0:
            return None
        a, c = number(t['U_power'])/2, number(t['constant'])
        if theta < a:
            value = [envelope(c*(a/(a-theta))**2, 2*(a-theta))]
        elif theta == a:
            value = [envelope(c*max(Q(1), theta)**2, logs=2)]
        else:
            value = [envelope(c*(theta/(theta-a))**2)]
        details = dict(reason='Abel in the common-period Hilbert norm of all partial divisor sums',
                       retains_unit_endpoint=True)
    elif rule in {'interval_from_supremum', 'finite_dilation_spacing'}:
        d, h = number(g['support_power']), number(g['l1_power'])
        terms = [envelope(t['constant'], number(t['U_power'])+2*h, 1, t['log_degree']) for t in bounds[0]]
        if rule == 'finite_dilation_spacing':
            terms += [envelope(2*(1+d)*number(t['constant']),
                number(t['U_power'])+2*h+2*(1+d), 0, t['log_degree']+1) for t in bounds[0]]
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
        value = normalize(terms)
    elif rule == 'source_prefix_auxiliary':
        # No licensed convolution/Mellin bridge exists in this grammar.
        return None
    else:
        raise ValueError('unknown inference rule')
    assumptions = sorted(set(a for p in premises for a in p['assumptions']) |
                         ({'mu*One=delta', 'mu multiplicative'} if rule == 'complete_divisor_inverse' else set()))
    return dict(bound=copy.deepcopy(value), details=details, assumptions=assumptions)


def key(g):
    # Structural keys are the memoization algorithm, not precautionary file hashes.
    return tuple(sorted((k, key(v) if isinstance(v, dict) else v) for k, v in g.items()))


def validate_goal(g):
    require(isinstance(g, dict) and isinstance(g.get('kind'), str), 'typed bound goal')
    if g['kind'] in {'pointwise2', 'spectrum', 'cofactor', 'reciprocal', 'variance', 'interval'}:
        require(g == goal(g['kind'], g.get('theta'), g.get('profile'),
                          g.get('support_power'), g.get('l1_power')), 'canonical complete auxiliary scope')
    elif g['kind'] in {'component_mellin', 'signed_convolution_mellin_bridge'}:
        require(set(g) == {'kind', 'p', 'm', 'sigma', 'theta', 'required'}, 'complete component goal')
        require(type(g['p']) is int and g['p'] >= 0 and type(g['m']) is int and g['m'] >= 1,
                'nonnegative finite factor and positive Dirichlet powers')
        require(0 < number(g['sigma']) < 1 and 0 < number(g['theta']) < 1, 'component strip and kernel')
        require(isinstance(g['required'], dict) and 'U_power' in g['required'], 'original requested bound')
        number(g['required']['U_power'])


def plan(target, meter, enabled=None, depth_limit=12, node_limit=4096):
    enabled = list(RULES if enabled is None else enabled)
    require(len(set(enabled)) == len(enabled) and set(enabled) <= set(RULES), 'declared rule subset')
    require(1 <= depth_limit <= 32 and 1 <= node_limit <= 65536, 'bounded proof search')
    nodes, attempts, cache, frontier = [], [], {}, []

    def visit(g, ancestors):
        validate_goal(g)
        token = key(g)
        if token in ancestors or len(ancestors) >= depth_limit:
            frontier.append(dict(goal=copy.deepcopy(g), reason='cycle' if token in ancestors else 'depth_limit'))
            return []
        if token in cache:
            return cache[token]
        answer = []
        for rule, goals in expansions(g):
            if rule not in enabled:
                continue
            groups = [visit(p, ancestors+(token,)) for p in goals]
            entry = dict(goal=copy.deepcopy(g), rule=rule, premises=copy.deepcopy(goals),
                         premise_solutions=copy.deepcopy(groups), accepted=[])
            attempts.append(entry)
            for ids in itertools.product(*groups):
                meter.charge(30+10*len(ids))
                result = apply(rule, g, [nodes[i] for i in ids])
                if result is None:
                    continue
                require(len(nodes) < node_limit, 'proof node budget')
                ident = len(nodes)
                nodes.append(dict(id=ident, goal=copy.deepcopy(g), rule=rule, premises=list(ids), **result))
                answer.append(ident)
                entry['accepted'].append(ident)
        if not answer:
            frontier.append(dict(goal=copy.deepcopy(g), reason='no_closed_argument_in_enabled_grammar'))
        cache[token] = answer
        return answer

    solutions = visit(copy.deepcopy(target), ())
    return dict(target=copy.deepcopy(target), enabled_rules=enabled, depth_limit=depth_limit, node_limit=node_limit,
                nodes=nodes, attempts=attempts, solutions=solutions, frontier=frontier,
                target_proved=bool(solutions), finite_grammar_only=True)


def score(node, window_power, nodes):
    require(node['bound'], 'rank proved numerical envelopes only')
    top = max((number(t['U_power'])+number(window_power)*number(t['L_power']), t['log_degree']) for t in node['bound'])
    c = sum((number(t['constant']) for t in node['bound']
             if (number(t['U_power'])+number(window_power)*number(t['L_power']), t['log_degree']) == top), Q(0))
    seen, pending = set(), [node['id']]
    while pending:
        i = pending.pop()
        if i not in seen:
            seen.add(i)
            pending.extend(nodes[i]['premises'])
    return (*top, len(node['assumptions']), c, len(seen), node['id'])


def rank(result, window_powers=WINDOW_POWERS):
    out = []
    for w in window_powers:
        w = str(number(w))
        require(number(w) >= 0, 'nonnegative window scale')
        if result['solutions']:
            ident = min(result['solutions'], key=lambda i: score(result['nodes'][i], w, result['nodes']))
            s = score(result['nodes'][ident], w, result['nodes'])
            out.append(dict(L_equals_U_power=w, selected=ident, exponent=str(s[0]), log_degree=s[1],
                            arithmetic_assumptions=s[2], leading_constant=str(s[3])))
    return out


def jordan2(n):
    value, remain, p = n*n, n, 2
    while p*p <= remain:
        if remain % p == 0:
            value = value//(p*p)*(p*p-1)
            while remain % p == 0:
                remain //= p
        p += 1
    if remain > 1:
        value = value//(remain*remain)*(remain*remain-1)
    return value


def compile_sawtooth(weights, meter, constant=0):
    """Exact rational Fourier compiler; no period enumeration or prime sampling."""
    require(1 <= len(weights) <= 10000, 'bounded finite calibration input, indexed from d=1')
    weights = list(map(number, weights))
    mean = number(constant)+sum((a*Q(d-1, 2*d) for d, a in enumerate(weights, 1)), Q(0))
    conductors, variance = [], Q(0)
    for r in range(2, len(weights)+1):
        c = sum((weights[k*r-1]/k for k in range(1, len(weights)//r+1)), Q(0))
        meter.charge(10*(len(weights)//r+1)+r)
        if c:
            j = jordan2(r)
            conductors.append(dict(r=r, K=str(c), J2=j))
            variance += c*c*Q(j, 12*r*r)
    return dict(mean=str(mean), conductors=conductors, variance=str(variance),
                coefficient='-K/(r*(1-exp(-2*pi*i*a/r)))', scope='exact finite coefficients; not a uniform inference')


def source_binding(parent, meter):
    import core_signed_primitive_search as PRIOR
    require(parent['schema'] == 'core-signed-primitive-feedback-v1', 'current published obstruction')
    binding = PRIOR.source_binding(dict(parent, schema='core-work-moment-proof-feedback-v1'), meter)
    require(binding == parent['signed_primitive_search']['binding'], 'complete unchanged arithmetic source')
    t = parent['cutoff_work_targets'][0]
    require((t['p'], t['m']) == (2, 3), 'current complete component mapping')
    return binding


def recovery(p, m):
    require(type(p) is int and type(m) is int and p >= 0 and m >= 1, 'Dirichlet polynomial powers')
    return dict(mean='C_U=1+(M(U)-c_U)/2', mean_bound_assumed=False,
        zero_mean_prefix='Q_U(n)=sum_(d<=U)mu(d)*({n/d}-(d-1)/(2*d)), n>=1; Qplus(0)=0',
        exact_source='A^p * (C_U*delta+e_U)^{*m} - c_U^m*D_U',
        branches=[dict(coefficient=math.comb(m, j), mean_power=m-j, A_power=p,
                       e_Dirichlet_power=j) for j in range(m+1)],
        all_ordered_cross_terms=[dict(left=j, right=k, coefficient=math.comb(m, j)*math.comb(m, k))
                                 for j in range(m+1) for k in range(m+1)],
        deterministic_head='-c_U^m*D_U and all of its crosses retained',
        missing='signed reciprocal-simplex covariance and Mellin recovery for e_U^{*j}, j>=2, '
                'with the exact mean, unit, head correction, residues and all source crosses',
        pointwise_power_substitution_allowed=False, full_component_bound_proved=False)


def search(parent, meter):
    binding = source_binding(parent, meter)
    t = parent['cutoff_work_targets'][0]
    root = dict(kind='component_mellin', p=t['p'], m=t['m'], sigma=t['sigma'], theta=t['theta'],
                required=copy.deepcopy(t['original_low_obligation']['required_upper']))
    full = plan(root, meter)
    # Ablate arithmetic assumptions on the SAME constructed auxiliary goal.
    inferred = next(a['premises'][0] for a in full['attempts'] if a['rule'] == 'source_prefix_auxiliary')
    unsigned = plan(dict(inferred, profile='bounded'), meter)
    base = plan(goal('interval', profile='mobius'), meter)
    base_unsigned = plan(goal('interval', profile='bounded'), meter)
    trials = []
    for label, result in [('actual_source_argument', full), ('same_auxiliary_unsigned', unsigned),
                          ('base_prefix', base), ('base_prefix_unsigned', base_unsigned)]:
        selected = rank(result) if result['solutions'] else []
        trials.append(dict(id=label, proof_search=result, selection=selected))
    subsolutions = next(a['premise_solutions'][0] for a in full['attempts'] if a['rule'] == 'source_prefix_auxiliary')
    auxview = dict(full, solutions=subsolutions)
    selections = rank(auxview)
    unsigned_selection = trials[1]['selection']
    advantage = any((number(a['exponent']), a['log_degree']) < (number(b['exponent']), b['log_degree'])
                    for a, b in zip(selections, unsigned_selection))
    return dict(schema='core-bound-argument-search-v1', spec=copy.deepcopy(SPEC), binding=binding,
        original_missing_bound=copy.deepcopy(t['original_low_obligation']),
        inferred_auxiliary=inferred, auxiliary_selection=selections, trials=trials,
        recovery=recovery(t['p'], t['m']),
        discovery_scope=dict(supplied='typed representations and inference rules, reviewed analytically',
            selected_by_detector='subgoals, rule compositions, exact bound costs and scale-dependent choices',
            open_leaves_generated=True, runtime_model_calls=0, formal_proof_assistant_verified=False),
        statistics=dict(arguments=sum(len(x['proof_search']['nodes']) for x in trials),
            applications=sum(len(x['proof_search']['attempts']) for x in trials),
            actual_arithmetic_observations=0, fitted_constants=0,
            auxiliary_exponent_advantage_over_unsigned=advantage,
            full_component_bound_proved=False),
        whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, result, artifact):
    out = copy.deepcopy(parent)
    out.update(schema='core-bound-argument-feedback-v1', status='bound_arguments_searched_core_open',
        parent_obligation_file='candidate10_signed_primitive_obligation.json', complete_search_artifact=artifact)
    out['bound_argument_search'] = copy.deepcopy(result)
    out['inherited_bound_argument_tasks'] = copy.deepcopy(parent['next_search_tasks'])
    out['next_search_tasks'] = [copy.deepcopy(parent['next_search_tasks'][0]), dict(priority=1,
        target_id=result['binding']['target_id'], search_kind='close_generated_signed_convolution_bridge',
        status='open', proof_frontier=copy.deepcopy(result['trials'][0]['proof_search']['frontier']),
        exact_recovery=copy.deepcopy(result['recovery']),
        auxiliary_exponent_advantage_over_unsigned=result['statistics']['auxiliary_exponent_advantage_over_unsigned'],
        original_goal_not_replaced=True)] + copy.deepcopy(parent['next_search_tasks'][1:])
    return out
