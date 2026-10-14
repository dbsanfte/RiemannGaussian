"""Goal-directed, exact bound composition for compiled cutoff energies.

The input is a polynomial transition and a requested exponent. No winning
auxiliary, sign inequality, or numerical growth fit is supplied. Rules remain
supplied mathematics; an exhausted rule set returns a precise open leaf.
"""
from fractions import Fraction as Q


def envelope(power, logs=0):
    if Q(logs) < 0:
        raise ValueError('nonnegative logarithmic degree')
    return dict(U_power=str(Q(power)), log_degree=str(Q(logs)))


def maximum(*terms):
    return max(terms, key=lambda e: (Q(e['U_power']), Q(e['log_degree'])))


def summation(term):
    """Uniform upper envelope of sums from 2 to U, including resonance."""
    p, k = Q(term['U_power']), Q(term['log_degree'])
    if p > -1:
        return envelope(p+1, k)
    if p == -1:
        return envelope(0, k+1)
    return envelope(0)


def meets(term, goal):
    p, k = Q(term['U_power']), Q(term['log_degree'])
    return p < goal or (p == goal and k == 0)


def maximal_energy_rule(a, nonnegative_cost, signed_prefix, r):
    """E_n<=E_(n-1)+a_n*E_(n-1)^r+b_n+R_n, 0<=r<1.

    For every V<=U the signed prefix must be <= its supplied NONNEGATIVE
    upper envelope. Taking the actual finite maximum is not an assumption
    of a bound on E. M<=D+A*M^r implies M<=2D+(2A)^(1/(1-r)).
    """
    r = Q(r)
    if not 0 <= r < 1:
        raise ValueError('sublinear nonnegative energy exponent')
    if a is None:
        feedback = envelope(0)
    else:
        total = summation(a)
        feedback = envelope(Q(total['U_power'])/(1-r), Q(total['log_degree'])/(1-r))
    result = maximum(envelope(0), feedback, nonnegative_cost, signed_prefix)
    return dict(rule='finite_maximum_and_sublinear_Young', energy_root=str(r),
        feedback_envelope=feedback, resulting_envelope=result,
        inequality='M<=D+A*M^r implies M<=2*D+(2*A)^(1/(1-r))',
        D='initial energy + summed nonnegative costs + upper bound for EVERY signed prefix',
        target_assumed_in_proof=False, all_integer_cutoffs=True)


def finite_shift_control(terms, head_degree, theta, sigma, meter):
    """Recognize a finite Dirichlet polynomial, then use a kernel norm.

    A term c^j*a^k*b^l*v^h is a coefficient at q^l, where a=q^-1,
    b=q^-s and |c|<=2. The supplied head atom satisfies |v|<=q^(d-1)
    for d>=1; d=0 gives v=0 at every q>=2. No sign is assumed.
    """
    if not (type(head_degree) is int and head_degree >= 0 and 0 < sigma < theta < 1):
        raise ValueError('finite head degree and admissible contour')
    contributions = []
    for term in terms:
        symbols, coeff = term['monomial'], Q(term['coefficient'])
        meter.charge(40+10*len(symbols))
        if any(s not in {'c', 'a', 'b', 'v'} for s in symbols):
            return dict(available=False, reason='not a certified finite-shift polynomial')
        if head_degree == 0 and 'v' in symbols:
            continue
        power = -symbols.count('a')-sigma*symbols.count('b')
        power += max(0, head_degree-1)*symbols.count('v')
        contributions.append(dict(root_U_power=str(power),
            coefficient_upper=str(abs(coeff)*2**symbols.count('c'))))
    if not contributions:
        return dict(available=True, identically_zero=True, terms=[],
            squared_norm_constant='0', squared_norm_envelope=envelope(0),
            root_U_power='0', target_assumed_in_proof=False)
    B = (1/(theta-sigma)+1/sigma)/(2*theta**2)
    C = sum(Q(t['coefficient_upper']) for t in contributions)
    power = max(Q(t['root_U_power']) for t in contributions)
    return dict(available=True, identically_zero=False, terms=contributions,
        squared_norm_constant=str(B*C*C), squared_norm_envelope=envelope(2*power),
        root_U_power=str(power), target_assumed_in_proof=False,
        rule='finite shifted complete centered power kernels and Minkowski',
        norm_domain='entire real height line, hence every old window',
        v_bound='v=0 for degree 0, otherwise abs(v)<=q^(degree-1)',
        work_control='W0_integral<=2*sqrt(D)*q^a*sqrt(L_old)+D*q^(2*a)',
        absolute_work_control=True, retained_zero_mu_branch=True)


def search_bounds(program, head_bound, theta, sigma, goal, generic_power, meter):
    """Try all declared rule compositions and expose the remaining estimates."""
    theta, sigma, goal, generic_power = map(Q, (theta, sigma, goal, generic_power))
    if not (goal > 0 and generic_power >= 0 and 0 < sigma < theta < 1):
        raise ValueError('positive goal and valid inherited generic norm bound')
    tr = program['transition']
    zero = finite_shift_control(tr['increment_sectors'][0], head_bound['convolution_power'],
                                theta, sigma, meter)
    if head_bound['atom'] == 'mu' and tr['increment_sectors'][0]:
        zero = dict(available=False, reason='inverse-divisor v depends on mu(q); repartition before using the zero-sector rule')
    generic = envelope(generic_power)
    if program['subtract_exact_head']:
        generic = maximum(generic, envelope(head_bound['global_U_power'], head_bound['global_log_degree']))
    shell_costs = [dict(name=p['name'], per_step=envelope(p['U_power'], p['log_degree']),
                        summed=summation(envelope(p['U_power'], p['log_degree'])))
                   for p in program['moving_height_shell']['parts']]
    summed_shell = maximum(envelope(0), *(c['summed'] for c in shell_costs))
    active = [i for i, terms in enumerate(tr['work_sectors']) if terms]
    routes = [dict(id=0, method='inherited_norm_envelope', status='proved' if meets(generic, goal) else 'insufficient_exponent',
        known_envelope=generic, required_U_power=str(goal), open_leaves=[],
        relation_to_original_goal='original goal', target_assumed_in_proof=False)]
    strategies = [('complete_work', active)]
    if zero['available'] and not zero['identically_zero']:
        strategies.append(('pay_zero_sector_by_energy_feedback', [s for s in active if s != 0]))
    for strategy, sectors in strategies:
        paid_zero = strategy == 'pay_zero_sector_by_energy_feedback'
        a = envelope(zero['root_U_power']) if paid_zero else None
        cost = summed_shell
        if paid_zero:
            cost = maximum(cost, summation(zero['squared_norm_envelope']))
        for mode in ['prefix', 'dyadic_max_partial', 'consecutive']:
            required = goal-1 if mode == 'consecutive' else goal
            arithmetic = summation(envelope(required)) if mode == 'consecutive' else envelope(required)
            recurrence = maximal_energy_rule(a, cost, arithmetic, Q(1, 2))
            feasible = meets(recurrence['resulting_envelope'], goal)
            known = generic
            if paid_zero:
                k = Q(zero['root_U_power'])
                cross = envelope(Q(generic['U_power'])/2+k, Q(generic['log_degree'])/2)
                squared = zero['squared_norm_envelope']
                if mode != 'consecutive':
                    cross, squared = summation(cross), summation(squared)
                known = maximum(known, cross, squared)
            forcing_proved = meets(known, required)
            if mode == 'consecutive':
                expr = 'R_q'
                domain = 'every integer q>=2'
                relation = 'optional stronger sufficient requirement; not equivalent'
            elif mode == 'prefix':
                expr = 'sum_(q=2..V) R_q'
                domain = 'every integer V>=1; empty prefix is zero'
                relation = 'equivalent goal up to paid costs' if feasible else 'unpaid recovery in this rule set'
            else:
                expr = 'sum_(q=U+1..V) R_q'
                domain = 'every U=2^k, k>=0, and EVERY integer U<=V<=2*U'
                relation = 'equivalent goal up to paid costs' if feasible else 'unpaid recovery in this rule set'
            leaf_id = 'program_'+str(program['id'])+'_route_'+str(len(routes))+'_signed_work'
            leaf = dict(id=leaf_id, status='proved_by_inherited_envelope' if forcing_proved else 'open',
                expression=expr, R_q=dict(integral='dt/(2*pi) over abs(t)<H(q-1)',
                    weight=tr['weight'], sectors=sectors, sector_polynomials=[tr['work_sectors'][i] for i in sectors],
                    term='sum_(i in sectors) mu(q)^i*W_i'),
                upper='C*q^power' if mode == 'consecutive' else ('C*V^power' if mode == 'prefix' else 'C*U^power'),
                power=str(required), quantifier=domain,
                uniform_constant='one finite C independent of q,U,V,X,N',
                known_envelope=known, actual_Mobius_required=True,
                arbitrary_sign_identity_suffices=False, sector_signs_assumed=False,
                moving_shells_included_separately=True, target_assumed_in_proof=False)
            status = ('proved' if forcing_proved else 'conditional_open_signed_work') if feasible else 'unpaid_auxiliary_cost'
            routes.append(dict(id=len(routes), method=strategy, aggregation=mode, status=status,
                required_U_power=str(goal), recurrence=recurrence, shell_costs=shell_costs,
                nonnegative_cost=cost, open_leaves=[] if forcing_proved else [leaf_id], forcing=leaf,
                dyadic_to_prefix_constant=str(1+2/goal) if mode == 'dyadic_max_partial' else None,
                endpoint_samples_suffice=False, all_integer_cutoffs=True,
                relation_to_original_goal=relation, target_assumed_in_proof=False))
            meter.charge(500)
    closed = [r for r in routes if r['status'] == 'proved']
    admissible = [r for r in routes if r['status'] in {'proved', 'conditional_open_signed_work'}]
    selected = min(admissible, key=lambda r: (r['status'] != 'proved',
        len(r.get('forcing', {}).get('R_q', {}).get('sectors', [])),
        r.get('aggregation') == 'consecutive', r['id']))['id'] if admissible else None
    next_targets = [] if selected is None or routes[selected]['status'] == 'proved' else [routes[selected]['forcing']]
    return dict(schema='cutoff-bound-composition-v1', goal_U_power=str(goal),
        supplied_generic_envelope=generic, zero_sector_control=zero, routes=routes,
        selected_route=selected, next_bound_targets=next_targets, goal_proved=bool(closed),
        model_calls=0, numerical_observations=0,
        selection='proved goal first, fewer unbounded sectors, cumulative before stronger consecutive condition, enumeration order',
        new_arithmetic_estimate_proved=False,
        proof_rule_limit='finite-shift kernels, Cauchy, summation, sublinear maximum, inherited norm envelope',
        automatic_feedback='unresolved selected forcing becomes the next bound target, with its exact signed polynomial')
