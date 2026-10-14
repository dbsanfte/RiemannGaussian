"""Search exact rewrites and proof trees for an unresolved signed core.

Primitive facts are supplied, but no resulting combination is nominated.
The dynamic program chooses which factor's signed prefixes to retain. A
proved component bound never closes the remaining joined arithmetic leaf.
"""
from fractions import Fraction as Q
from itertools import product
from math import ceil, comb


def atom_bounds(alpha, gamma):
    a, b = Q(alpha), Q(gamma)
    if not 0 < a < 1 or not 0 < b < 1:
        raise ValueError('strict rational cutoff exponents')
    return {
        ('A', 'mass'): [(1, a, 0, 'A_mass')],
        ('A', 'critical'): [(2, a/2, 0, 'A_critical')],
        ('B', 'mass'): [(3, b/3, 0, 'B_mass')],
        ('B', 'critical'): [(7, 0, 0, 'B_critical')],
        ('R', 'mass'): [(1, 1, 1, 'R_mass')],
        ('R', 'critical'): [(2, Q(1, 2), 1, 'R_critical')],
        ('S', 'mass'): [(3, Q(1, 3), 1, 'S_mass')],
        ('S', 'critical'): [(50, 0, 0, 'S_critical_direct'),
                              (84, -b/6, 0, 'S_critical_tail')],
        ('E', 'mass'): [(3, 1, 1, 'E_mass')],
        ('E', 'critical'): [(6, Q(1, 2), 1, 'E_critical')],
        ('E', 'prefix'): [(2, a, 0, 'E_prefix')],
        ('O', 'mass'): [(1, 1, 0, 'O_mass')],
        ('O', 'critical'): [(2, Q(1, 2), 0, 'O_critical')],
        ('K', 'mass'): [(Q(3, 2), Q(2, 3), 0, 'K_mass')],
        ('K', 'critical'): [(6, Q(1, 6), 0, 'K_critical')],
        **{('C', norm): [(2, 0, 0, 'C_'+norm)]
           for norm in ('mass', 'critical', 'prefix')},
    }


def partitions(expression):
    """Every proper unordered multiset partition, without permutations."""
    names = sorted(set(expression))
    counts = [expression.count(name) for name in names]
    for selected in product(*(range(count+1) for count in counts)):
        left = tuple(name for name, count in zip(names, selected) for _ in range(count))
        right = tuple(name for name, count, used in zip(names, counts, selected)
                      for _ in range(count-used))
        if left and right and left <= right:
            yield left, right


def cost(node):
    return (Q(node['power']), node['log_degree'], Q(node['constant']), node['proof_size'])


class ProofSearch:
    def __init__(self, alpha, gamma, meter):
        self.atoms = atom_bounds(alpha, gamma)
        self.meter = meter
        self.nodes = []
        self.cache = {}
        self.rule_applications = 0

    def solve(self, expression, norm):
        expression = tuple(sorted(expression))
        if norm not in ('mass', 'critical', 'prefix') or any(c not in 'ABCEKORS' for c in expression):
            raise ValueError('declared factor and norm grammar')
        if len(expression) > 16:
            raise ValueError('bounded convolution degree')
        key = expression, norm
        if key in self.cache:
            return self.cache[key]
        choices = []

        def offer(rule, children=(), value=None, atom_rule=None):
            self.meter.charge(20+10*len(children))
            self.rule_applications += 1
            if value is None:
                constant, power, degree = Q(1), Q(0), 0
                for child in children:
                    node = self.nodes[child]
                    constant *= Q(node['constant'])
                    power += Q(node['power'])
                    degree += node['log_degree']
                if rule == 'critical_to_prefix':
                    power += Q(1, 2)
            else:
                constant, power, degree = value
            candidate = dict(expression=list(expression), norm=norm, rule=rule,
                children=list(children), constant=str(Q(constant)), power=str(Q(power)),
                log_degree=degree, proof_size=1+sum(self.nodes[c]['proof_size'] for c in children))
            if atom_rule is not None:
                candidate['atom_rule'] = atom_rule
            choices.append(candidate)

        if not expression:
            offer('atom', value=(1, 0, 0), atom_rule='delta_'+norm)
        elif len(expression) == 1:
            for constant, power, degree, name in self.atoms.get((expression[0], norm), []):
                offer('atom', value=(constant, power, degree), atom_rule=name)
        if norm == 'prefix':
            offer('mass_to_prefix', (self.solve(expression, 'mass'),))
            offer('critical_to_prefix', (self.solve(expression, 'critical'),))
        for left, right in partitions(expression):
            self.meter.charge(10)
            if norm in ('mass', 'critical'):
                offer(norm+'_convolution', (self.solve(left, norm), self.solve(right, norm)))
            else:
                offer('prefix_convolution', (self.solve(left, 'prefix'), self.solve(right, 'mass')))
                if left != right:
                    offer('prefix_convolution', (self.solve(right, 'prefix'), self.solve(left, 'mass')))
        if not choices:
            raise ValueError('no rule for declared expression')
        best = min(choices, key=cost)
        best['id'] = len(self.nodes)
        self.nodes.append(best)
        self.cache[key] = best['id']
        self.meter.live(128*len(self.nodes))
        return best['id']


def uniform_payment(power, log_degree):
    power = Q(power)
    if type(log_degree) is not int or log_degree < 0:
        raise ValueError('nonnegative integral logarithmic degree')
    if power > 0 or (power == 0 and log_degree > 0):
        return None
    if log_degree == 0:
        return Q(1)
    return 2**log_degree*(1+(Q(log_degree)/(-power))**log_degree)


def energy_bound(node, coefficient, source_scalar):
    scalar = {'beta': Q(9, 2), '-beta': Q(9, 2), '-R_u': Q(5)}[source_scalar]
    constant = 4*(Q(node['constant'])*Q(coefficient)*scalar)**2
    power, degree = 2*Q(node['power'])-1, 2*node['log_degree']
    payment = uniform_payment(power, degree)
    return dict(constant=str(constant), power=str(power), log_degree=degree,
                uniform_constant=None if payment is None else str(constant*payment))


def expansion(mode, term, depth, engine):
    a, b = term['a'], term['b']
    if type(depth) is not int or not 0 <= depth <= a:
        raise ValueError('bounded centering depth')
    base = (['A']*mode['p']+['B']*mode['q']+['S']*b+['R']*(a-depth)
            +(['K'] if mode['positive_shift'] is not None else []))
    pieces = []
    for centered in range(depth+1):
        drift = depth-centered
        factors = sorted(base+['E']*centered+['C']*drift+['O']*drift)
        coefficient = Q(term['coefficient'])*comb(depth, centered)*(-1)**drift
        proof = engine.solve(factors, 'prefix')
        pieces.append(dict(coefficient=str(coefficient), expression=factors, prefix_proof=proof,
                           energy=energy_bound(engine.nodes[proof], coefficient, mode['coefficient'])))
    return dict(depth=depth, pieces=pieces)


def summary(alternative):
    paid = [p for p in alternative['pieces'] if p['energy']['uniform_constant'] is not None]
    unpaid = [p for p in alternative['pieces'] if p['energy']['uniform_constant'] is None]
    worst = max(((Q(p['energy']['power']), p['energy']['log_degree']) for p in unpaid),
                default=(Q(-1000), 0))
    return len(paid), worst


def choose(alternatives):
    baseline = alternatives[0]
    base_paid, base_worst = summary(baseline)
    eligible = [baseline]
    for candidate in alternatives[1:]:
        paid, worst = summary(candidate)
        if (base_paid == 0 and paid > 0) or worst[0] < base_worst[0]:
            eligible.append(candidate)
    return min(eligible, key=lambda c: (-summary(c)[0], *summary(c)[1], len(c['pieces']), c['depth']))['depth']


def search(row, meter):
    engine = ProofSearch(row['alpha'], row['gamma'], meter)
    terms = []
    for case in row['cases']:
        mode = case['mode']
        for term in case['program']['terms']:
            alternatives = [expansion(mode, term, depth, engine) for depth in range(term['a']+1)]
            terms.append(dict(key=dict(mode=mode['name'], a=term['a'], b=term['b']),
                source_scalar=mode['coefficient'], inverse_coefficient=term['coefficient'],
                alternatives=alternatives, selected_depth=choose(alternatives)))
    selected = [p for t in terms for p in t['alternatives'][t['selected_depth']]['pieces']]
    return dict(schema='core-prefix-proof-search-v1', geometry_id=row['id'], alpha=row['alpha'], gamma=row['gamma'],
        nodes=engine.nodes, terms=terms,
        statistics=dict(proof_nodes=len(engine.nodes), rule_applications=engine.rule_applications,
            original_terms=len(terms), alternatives=sum(len(t['alternatives']) for t in terms),
            selected_centerings=sum(t['selected_depth'] > 0 for t in terms), selected_pieces=len(selected),
            uniformly_paid_pieces=sum(p['energy']['uniform_constant'] is not None for p in selected)),
        whole_signed_bound_proved=False, RH_proved=False)


def channel_cost(construction):
    constant = Q(0)
    for channel in construction['channels']:
        eta = Q(channel['eta'])
        if eta < 0:
            raise ValueError('nonnegative channel weight')
        coefficients = list(map(Q, channel['polynomial']))
        if not coefficients:
            raise ValueError('nonempty polynomial channel')
        variation = abs(coefficients[0])+2*sum(map(abs, coefficients[1:]))
        constant += (2**ceil(eta)*variation)**2
    return constant


def reduction(parent, construction, result):
    """Bind new paid pieces to the exact previous JOINED goal, without refitting."""
    def key(t): return (t['mode'], t['a'], t['b'])
    old_paid = {key(t) for t in parent['paid_component_reduction']['paid_components']}
    all_terms = {key(t['key']) for t in result['terms']}
    if not old_paid <= all_terms:
        raise ValueError('inherited paid source term absent')
    paid, remaining, excluded = [], [], []
    for term in result['terms']:
        chosen = term['alternatives'][term['selected_depth']]
        for i, piece in enumerate(chosen['pieces']):
            ref = dict(source_key=term['key'], depth=chosen['depth'], piece=i)
            if key(term['key']) in old_paid:
                excluded.append(ref)
            elif piece['energy']['uniform_constant'] is not None:
                paid.append(dict(ref, uniform_energy_constant=piece['energy']['uniform_constant']))
            else:
                remaining.append(ref)
    cost = channel_cost(construction)
    paid_constant = len(paid)*cost*sum((Q(p['uniform_energy_constant']) for p in paid), Q(0))
    target = parent['paid_component_reduction']['new_sufficient_goal']
    if Q(target['p']) < 0:
        raise ValueError('constant payment requires a nonnegative target log degree')
    return dict(schema='core-prefix-proof-reduction-v1', parent_obligation_id=parent['parent_obligation_id'],
        geometry_id=result['geometry_id'], channel_abel_constant=str(cost),
        old_paid_excluded=excluded, newly_paid=paid, remaining_signed_pieces=remaining,
        combined_new_paid_constant=str(paid_constant),
        exact_split='Z_old=P_new+Z_new; Z_new=sum(all remaining signed pieces)-e; e=f-g',
        recovery='S_old<=2*S_new+2*C_new; S_new<=2*S_old+2*C_new',
        transport_error_retained=True, all_remaining_crosses_retained=True,
        common_horizon='N=4X-1 for both parent and child',
        goal=dict(expression='S_new(X)<=C*(1+log2X)^p for every dyadicX>=1',
                  p=target['p'], same_finite_constant=True, status='open'),
        analyst_nominated_selected_formula=False, proof_rules_are_supplied=True,
        original_fixed_recurrence_discharged=False, whole_signed_bound_proved=False, RH_proved=False)
