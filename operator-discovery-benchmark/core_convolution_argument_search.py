"""Discover exact floor and convolution reductions before pricing their bounds.

All identities have explicit integer/support domains.  An expensive proof
route never supplies a lower bound for actual arithmetic cancellation.
"""
import copy
import itertools
import math
from fractions import Fraction as Q

import core_bound_argument_search as OLD

require = OLD.require


def add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, Q(0))+v
        if not out[k]:
            del out[k]
    return out


def scale(a, c):
    return {k: v*c for k, v in a.items() if v*c}


def mul(a, b):
    out = {}
    for k, v in a.items():
        for l, w in b.items():
            out = add(out, {tuple(sorted(k+l)): v*w})
    return out


def power(a, n):
    out = {(): Q(1)}
    for _ in range(n):
        out = mul(out, a)
    return out


def encode(a):
    return [dict(key=list(k), value=str(v)) for k, v in sorted(a.items())]


def decode(a):
    return {tuple(t['key']): Q(t['value']) for t in a}


def solve(columns, source, meter):
    """Rational column solve or an exact left-null contradiction."""
    universe = sorted(set(source).union(*(set(c) for c in columns)))
    pivots = {}
    for key in universe:
        row = {i: c[key] for i, c in enumerate(columns) if c.get(key)}
        rhs, witness = source.get(key, Q(0)), {key: Q(1)}
        while row:
            p = min(row)
            if p not in pivots:
                z = row[p]
                pivots[p] = (scale(row, 1/z), rhs/z, scale(witness, 1/z))
                break
            r, b, w = pivots[p]
            z = row[p]
            row, rhs, witness = add(row, scale(r, -z)), rhs-z*b, add(witness, scale(w, -z))
            meter.charge(10*(len(r)+len(w)+1))
        else:
            if rhs:
                return dict(status='infeasible', dual=encode(witness), contradiction=str(rhs))
        meter.charge(10*(len(columns)+len(witness)+1))
    answer = {}
    for p in sorted(pivots, reverse=True):
        row, rhs, _ = pivots[p]
        v = rhs-sum((a*answer.get(i, 0) for i, a in row.items() if i != p), Q(0))
        if v:
            answer[p] = v
    return dict(status='feasible', solution=[dict(column=i, coefficient=str(v)) for i, v in sorted(answer.items())])


def compose(columns, solution):
    value = {}
    for term in solution:
        value = add(value, scale(columns[term['column']], Q(term['coefficient'])))
    return value


def floor_problem():
    # x=1/a,y=1/d. Atoms are n, floor(n/a), floor(n/d), floor(n/(ad)), 1.
    source = {('Fd', 1, 0): Q(1), ('Fad', 0, 0): Q(-1),
              ('one', 0, 0): Q(-1, 2), ('one', 1, 0): Q(1, 2)}
    denominators = [('d', 0, 1), ('a', 1, 0), ('ad', 1, 1)]
    multipliers = [(i, j) for i in range(3) for j in range(3-i)]
    basis = []
    for name, a, d in denominators:
        base = {('n', a, d): Q(1), ('F'+name, 0, 0): Q(-1),
                ('one', 0, 0): Q(-1, 2), ('one', a, d): Q(1, 2)}
        for i, j in multipliers:
            poly = {(s, x+i, y+j): v for (s, x, y), v in base.items()}
            basis.append(dict(denominator=[a, d], reciprocal=[i, j], polynomial=encode(poly)))
    return source, basis


def synthesize_floor(meter):
    source, basis = floor_problem()
    columns = [decode(b['polynomial']) for b in basis]
    result = solve(columns, source, meter)
    require(result['status'] == 'feasible' and compose(columns, result['solution']) == source,
            'discovered exact floor identity')
    return dict(source=encode(source), basis=basis, certificate=result,
        domain='positive integers a,d; integer n>=0',
        normalization='floor(floor(n/d)/a)=floor(n/(ad)); x=1/a,y=1/d',
        inference='denominator factor closure and reciprocal monomials of total degree<=2',
        numerical_fitting=False)


def finite_convolution(a, b):
    out = [Q(0)]*(len(a)*len(b))
    for d, v in enumerate(a, 1):
        for k, w in enumerate(b, 1):
            out[d*k-1] += v*w
    return out


def compile_dilation(a, h, floor_certificate, meter):
    """Apply the discovered identity to real rational coefficient arrays."""
    require(1 <= len(a)*len(h) <= 10000, 'bounded finite exact calibration')
    a, h = list(map(Q, a)), list(map(Q, h))
    c = sum((v/d for d, v in enumerate(a, 1)), Q(0))
    out = [Q(0)]*(len(a)*len(h))
    basis, proof = floor_certificate['basis'], floor_certificate['certificate']
    require(proof['status'] == 'feasible', 'proved floor compiler')
    source, declared_basis = floor_problem()
    require(basis == declared_basis and
            compose([decode(b['polynomial']) for b in basis], proof['solution']) == source,
            'complete floor certificate before specialization')
    for i, av in enumerate(a, 1):
        for d, hv in enumerate(h, 1):
            for t in proof['solution']:
                b = basis[t['column']]
                x, y = b['denominator']; u, v = b['reciprocal']
                index = i**x*d**y
                out[index-1] += av*hv*Q(t['coefficient'])/i**u/d**v
                meter.charge(10)
    expected = finite_convolution(h, a)
    for d, v in enumerate(h, 1):
        expected[d-1] -= c*v
    require(out == expected, 'signed convolution collected from the solved identity')
    null = sum((v/n for n, v in enumerate(out, 1)), Q(0))
    require(null == 0, 'complete reciprocal coefficient null')
    mean = 1+sum((v*Q(d-1, 2*d) for d, v in enumerate(a, 1)), Q(0))
    return dict(coefficients=list(map(str, out)), c=str(c), mean=str(mean), harmonic_null=str(null),
                short_head='-(1-C)*sum_(d>n)h(d); not part of the periodic covariance')


def exact_gram(v, w, meter):
    require(len(v)*len(w) <= 1000000, 'bounded exact Gram calibration')
    v, w = list(map(Q, v)), list(map(Q, w))
    value = Q(0)
    for n, a in enumerate(v, 1):
        for m, b in enumerate(w, 1):
            value += a*b*Q(math.gcd(n, m)**2-1, 12*n*m)
            meter.charge(8)
    return str(value)


def divisor_sum(k, s):
    require(type(k) is int and k >= 1 and s >= 0, 'positive integer divisor depth and nonnegative decay')
    if s < 1:
        return Q(1)/(1-s), 1-s, k-1
    if s == 1:
        return Q(1), Q(0), k
    return (s/(s-1))**k, Q(0), 0


def exponential_moment(j):
    value = 1
    for i in range(1, j+1):
        value = i*value+1
    return value


def divisor_arguments(p, decay, profile, meter):
    require(type(p) is int and 0 <= p <= 12 and profile in {'mobius', 'bounded'}, 'finite product grammar')
    decay = OLD.number(decay)
    require(decay >= 0, 'rational nonnegative divisor decay')
    k = p+1
    c, extra = (Q(3), 0) if profile == 'mobius' else ((Q(2), 2) if not decay else (2+1/decay, 0))
    # c is the coefficient amplitude of A^(p+1)-c_U A^p; extra is its squared log cost.
    rows = []

    def put(rule, constant, H_power, logs, details):
        meter.charge(30)
        rows.append(dict(rule=rule, bound=OLD.envelope(c*c*constant*k**logs, k*H_power, logs=logs+extra),
                         details=details, amplitude=str(c), amplitude_squared_log_degree=extra))

    a, h, l = divisor_sum(k, decay)
    put('pointwise_divisor_mass', a*a/4, 2*h, 2*l, 'abs(B_n)<=1/2; complete divisor mass')
    a, h, l = divisor_sum(2*k*k, 2*decay)
    put('weighted_coefficient_l2', a/6, h, l, 'Var<=sum d2(n)*abs(v(n))^2/6; d2*d_k^2<=d_(2k^2)')
    a, h, l = divisor_sum(k*k, 2*decay)
    if decay:
        put('uniform_divisor_cofactor', a*((1+decay)/decay)**(2*k)/12, h, l,
            'complete cofactor bounded by d_k(r)*r^-decay*(1+1/decay)^k')
    else:
        put('uniform_divisor_cofactor', a/12, h, l+2*k, 'take the uniform cofactor maximum')
        put('cutoff_divisor_cofactor', Q(exponential_moment(2*k), 12), Q(1), k*k-1,
            'retain H/r; d_k^2<=d_(k^2); Stieltjes exponential moment R_(2k)')
    if decay:
        base = Q(exponential_moment(2*k), 12)
        if decay < Q(1, 2):
            put('weighted_Abel', base/(1-2*decay)**2, 1-2*decay, k*k-1,
                'common-period norm of partial divisor envelopes; endpoint retained')
        elif decay == Q(1, 2):
            put('weighted_Abel', base, Q(0), k*k+1, 'critical Abel integral retains two logs')
        else:
            put('weighted_Abel', base*(decay/(decay-Q(1, 2)))**2, Q(0), k*k-1,
                'Abel with the full terminal logarithmic envelope')
    selected = min(range(len(rows)), key=lambda i: (Q(rows[i]['bound']['U_power']),
        rows[i]['bound']['log_degree'], Q(rows[i]['bound']['constant']), i))
    variance = rows[selected]['bound']
    spacing = [OLD.envelope(variance['constant'], variance['U_power'], 1, variance['log_degree']),
        OLD.envelope(2*k*Q(variance['constant']), Q(variance['U_power'])+2*k,
                     logs=variance['log_degree']+1)]
    return dict(p=p, decay=str(decay), profile=profile, divisor_depth=k, support_U_power=k,
        candidates=rows, selected=selected, period_bound=variance, window_bound=spacing,
        window_domain='integer U,L>=1; physical prefix agrees on n>=U^p; exact short head otherwise',
        log_conversion='1+log(U^k)<=k*(1+log U); constants include k^log_degree',
        harmonic_null='sum_n (A^(p+1)-c*A^p)(n)/n=0; all coefficients including unit retained')


def monomials(variables, degree):
    return [tuple(v) for v in itertools.combinations_with_replacement(variables, degree)]


def geometry_problem(alpha, beta, m=3):
    alpha, beta = Q(alpha), Q(beta)
    require(0 < alpha <= beta <= 1 and type(m) is int and 1 <= m <= 6, 'ordered fixed geometry')
    variables = ('C', 'e', 'r', 't')
    source = power({('C',): Q(1), ('e',): Q(1)}, m)
    basis = [{key: Q(1)} for key in monomials(variables, m) if key.count('e') <= 1]
    ideals, descriptions = [], []
    et, er = {('e',): Q(1), ('t',): Q(-1)}, {('e',): Q(1), ('r',): Q(-1)}
    for a in range(m+1):
        for b in range(m+1-a):
            if a+b and a*alpha+b*beta >= 1:
                factor = mul(power(et, a), power(er, b))
                for multiplier in monomials(variables, m-a-b):
                    ideals.append(mul({multiplier: Q(1)}, factor))
                    descriptions.append(dict(t_tail_power=a, r_tail_power=b, multiplier=list(multiplier),
                                             lower_support_power=str(a*alpha+b*beta)))
    costs = [Q(next(iter(b)).count('t'))*alpha+Q(next(iter(b)).count('r'))*beta
             if 'e' in next(iter(b)) else None for b in basis]
    return source, basis, costs, ideals, descriptions


def hyperbola_synthesize(alpha, beta, meter, m=3):
    source, basis, costs, ideals, descriptions = geometry_problem(alpha, beta, m)
    thresholds = sorted({Q(0)} | {c for c in costs if c is not None})
    trials = []
    for threshold in thresholds:
        allowed = [i for i, c in enumerate(costs) if c is None or c <= threshold]
        columns = [basis[i] for i in allowed]+ideals
        outcome = solve(columns, source, meter)
        trials.append(dict(support_threshold=str(threshold), allowed=allowed, certificate=outcome))
    viable = [i for i, t in enumerate(trials) if t['certificate']['status'] == 'feasible']
    require(viable, 'full short representation available in declared geometry')
    selected = min(viable)
    t = trials[selected]
    representation, vanishing = {}, {}
    for term in t['certificate']['solution']:
        i, c = term['column'], Q(term['coefficient'])
        if i < len(t['allowed']):
            representation = add(representation, scale(basis[t['allowed'][i]], c))
        else:
            vanishing = add(vanishing, scale(ideals[i-len(t['allowed'])], c))
    require(add(representation, vanishing) == source, 'complete local convolution identity')
    h, z = {}, {}
    for key, c in representation.items():
        if 'e' in key:
            l = list(key); l.remove('e'); h[tuple(l)] = c
        else:
            z[key] = c
    return dict(alpha=str(Q(alpha)), beta=str(Q(beta)), m=m, source=encode(source),
        basis=[encode(b) for b in basis], support_costs=[None if c is None else str(c) for c in costs],
        ideals=[encode(i) for i in ideals], support_certificates=descriptions, trials=trials, selected=selected,
        one_e_coefficient=encode(h), finite_head=encode(z), vanishing_remainder=encode(vanishing),
        identity='(C*delta+e)^m = h*e+z on coefficients n<=N',
        domain='fixed t=floor(N^alpha), r=floor(N^beta), integer N>=1; every coefficient 1<=n<=N',
        full_finite_head_indicator_retained=True, global_Dirichlet_series_identity=False,
        moving_cutoffs_allowed_in_period_rule=False, head_or_cross_paid=False)


def geometry_cost(g, p, cutoff_power):
    h = decode(g['one_e_coefficient'])
    alpha, beta, u = Q(g['alpha']), Q(g['beta']), Q(cutoff_power)
    require(h and g['m'] == 3, 'nonempty cubic one-e geometry cost')
    gamma = max(key.count('t')*alpha+key.count('r')*beta for key in h)
    k = max(p+2*(key.count('t')+key.count('r'))+1 for key in h)
    # C<=5U/2; the unit of e is O(U), and |e(n)|<=5U*d2(n) includes it.
    amplitude_h = sum((abs(c)*Q(5, 2)**key.count('C')*5**(key.count('t')+key.count('r'))
                       for key, c in h.items()), Q(0))
    return dict(coefficient_divisor_depth=k, coefficient_amplitude=str(3*amplitude_h),
        coefficient_U_power=2, denominator=dict(U_power=p+1, N_power=str(gamma)),
        normalized_spacing_cost_power=str((3*(p+1)+4)*u+3*gamma-2),
        optimistic_zero_amplitude_cost_power=str(3*(p+1)*u+3*gamma-2),
        scope='cost of separate periodic-spacing argument divided by N^2; not a core energy bound',
        finite_head_and_cross_paid=False, outer_kernel_and_centering_paid=False,
        actual_arithmetic_lower_bound=False)


def geometry_grid(max_denominator=6):
    """Enumerate cutoffs from a rational grammar, not a list of examples.

    The full cubic mean expansion includes C*e^2, so a quadratic tail
    relation is needed before reducing it to one unrestricted e factor.
    With ordered cutoffs this requires 2*beta>=1. No special lower
    cutoff or nominated decomposition coefficients are assumed.
    """
    require(type(max_denominator) is int and 2 <= max_denominator <= 12,
            'bounded rational cutoff grammar')
    # beta=1 can put the whole source into its finite head without reducing
    # the obligation. This grammar searches strictly shorter cutoffs.
    values = sorted({Q(a, b) for b in range(1, max_denominator+1) for a in range(1, b)})
    return [(str(a), str(b)) for a in values for b in values if a <= b and 2*b >= 1]


GEOMETRIES = geometry_grid()
GEOMETRY_GRAMMAR = dict(max_denominator=6, ordered_cutoffs=2,
    coverage='2*beta>=1; fixed integer floors; beta<1',
    coefficient_search='all degree-m monomials with at most one e; rational linear certificates')


def fresh_prime_obstruction(p):
    require(type(p) is int and 0 <= p <= 12, 'finite actual Mobius convolution depth')
    k = p+1
    return dict(p=p, number_of_distinct_primes=k, prime_interval='U/2<q<=U',
        conductor='product of k distinct primes from the declared interval',
        coefficient=str((-1)**k*math.factorial(k)),
        higher_cofactors_zero='a short factor containing q>U/2 cannot absorb any further integer>=2',
        lower_coefficient=str(Q(math.factorial(k)**2, 24)),
        uniform_lower_bound='Var >= lower_coefficient * binom(pi(U)-pi(U/2),k)',
        jordan_ratio_lower='J2(r)/r^2>=1/2 by the telescoping product over all integers>=2',
        asymptotic=dict(U_power=k, log_denominator_degree=k,
            imported_theorem='pi(x)~x/log(x)', source='https://dlmf.nist.gov/27.2.E3',
            scope='positive implied constant for all sufficiently large U; no effective threshold claimed'),
        applies_only_to='full-period covariance of A^p*e at decay zero with actual Mobius coefficients',
        finite_window_lower_bound=False, full_core_refuted=False)


def source_binding(parent, meter):
    require(parent['schema'] == 'core-bound-argument-feedback-v1', 'verified current bound-argument input')
    binding = OLD.source_binding(dict(parent, schema='core-signed-primitive-feedback-v1'), meter)
    require(binding == parent['bound_argument_search']['binding'], 'unchanged complete source')
    return binding


def search(parent, meter):
    binding = source_binding(parent, meter)
    t = parent['cutoff_work_targets'][0]
    require((t['p'], t['m']) == (2, 3), 'current full component mapping')
    floor = synthesize_floor(meter)
    actual = divisor_arguments(t['p'], 0, 'mobius', meter)
    unsigned = divisor_arguments(t['p'], 0, 'bounded', meter)
    geometries = [hyperbola_synthesize(a, b, meter, t['m']) for a, b in GEOMETRIES]
    u = t['original_low_obligation']['parameters']['alpha']
    costs = [geometry_cost(g, t['p'], u) for g in geometries]
    chosen = min(range(len(costs)), key=lambda i: (Q(costs[i]['normalized_spacing_cost_power']), i))
    return dict(schema='core-convolution-argument-search-v1', binding=binding, floor_search=floor,
        divisor_proofs=[actual, unsigned], geometry_grammar=copy.deepcopy(GEOMETRY_GRAMMAR),
        geometries=geometries, geometry_costs=costs,
        period_obstruction=fresh_prime_obstruction(t['p']),
        selected_geometry=chosen, inherited_recovery=copy.deepcopy(parent['bound_argument_search']['recovery']),
        complete_source='A^p*(h*e+z)-c^m*D on n<=N; unchanged full source outside local identity',
        source_recovery=dict(mean='C=1+(M(U)-c)/2', unit='e(1)=c-C; included in 5U*d2 envelope',
            floor_head='-(1-C)*sum_(d>n)(A^p*h)(d)', finite_head='prefix(A^p*z-c^m*D)(n)',
            joined_covariance='square of periodic branch + exact floor head + exact finite head, all ordered crosses',
            outer_K_and_analytic_residue='unchanged and still unpaid',
            ordinary_theta_moment_convergence_assumed=False),
        missing='uniform signed finite-window covariance of the COMPLETE joined hyperbola branches and '
                'outer-kernel/centering recovery; fixed-period estimates do not pay this',
        statistics=dict(floor_columns=len(floor['basis']),
            divisor_arguments=sum(len(x['candidates']) for x in (actual, unsigned)),
            geometries=len(geometries), geometry_thresholds=sum(len(g['trials']) for g in geometries),
            actual_arithmetic_observations=0, fitted_constants=0, runtime_model_calls=0,
            arithmetic_U_power_advantage=False, arithmetic_log_degree_advantage=2,
            full_component_bound_proved=False),
        supplied_rules='CORE_DILATION_COVARIANCE_REVIEW_031.txt',
        formal_proof_assistant_verified=False, whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, result, artifact):
    out = copy.deepcopy(parent)
    out.update(schema='core-convolution-argument-feedback-v1', status='convolution_arguments_searched_core_open',
        parent_obligation_file='candidate10_bound_argument_obligation.json', complete_search_artifact=artifact)
    out['convolution_argument_search'] = copy.deepcopy(result)
    out['inherited_convolution_argument_tasks'] = copy.deepcopy(parent['next_search_tasks'])
    out['next_search_tasks'] = [copy.deepcopy(parent['next_search_tasks'][0]), dict(priority=1,
        target_id=result['binding']['target_id'], search_kind='signed_joined_hyperbola_window_covariance', status='open',
        exact_geometry=copy.deepcopy(result['geometries'][result['selected_geometry']]),
        failed_separate_spacing_cost=copy.deepcopy(result['geometry_costs'][result['selected_geometry']]),
        complete_recovery=copy.deepcopy(result['source_recovery']), missing=result['missing'],
        original_global_Mellin_bound_and_all_routes_retained=True)] + copy.deepcopy(parent['next_search_tasks'][1:])
    return out
