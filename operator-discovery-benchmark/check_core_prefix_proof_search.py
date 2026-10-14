"""Independent exact proof auditor for the supplied finite prefix language.

No generator, source evaluations, or numerical studies are imported. The
checker reconstructs source polynomials, formal centering, every proof rule
and the optimum of the declared finite norm language independently.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import comb, ceil
import re

FACTORS = frozenset('ABCEKORS')
NORMS = ('mass', 'critical', 'prefix')
MAX_FACTORS = 16


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _rational(value, meter):
    _require(type(value) is str and 0 < len(value) <= 1235 and
             re.fullmatch(r'-?\d+(?:/\d+)?', value) is not None,
             'canonical bounded rational string')
    meter.charge(len(value) + 1)
    try:
        result = Q(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError('canonical rational string') from error
    _require(str(result) == value, 'canonical rational string')
    if hasattr(meter, 'number'):
        return meter.number(result)
    _require(max(abs(result.numerator).bit_length(), result.denominator.bit_length()) <= 4096,
             'rational bit cap')
    return result


def _integer(value, lower=0, upper=1000):
    _require(type(value) is int and lower <= value <= upper, 'bounded exact integer')
    return value


def _expression(value):
    _require(type(value) is list and len(value) <= MAX_FACTORS and
             all(type(v) is str and v in FACTORS for v in value) and value == sorted(value),
             'sorted bounded convolution expression')
    return tuple(value)


def _atoms(alpha, gamma):
    # Costs are (N power, log degree, constant, tree size), not numerical fits.
    data = {
        'A': {'mass': [(1, alpha, 0, 'A_mass')], 'critical': [(2, alpha/2, 0, 'A_critical')]},
        'B': {'mass': [(3, gamma/3, 0, 'B_mass')], 'critical': [(7, 0, 0, 'B_critical')]},
        'R': {'mass': [(1, 1, 1, 'R_mass')], 'critical': [(2, Q(1,2), 1, 'R_critical')]},
        'S': {'mass': [(3, Q(1,3), 1, 'S_mass')],
              'critical': [(50, 0, 0, 'S_critical_direct'), (84, -gamma/6, 0, 'S_critical_tail')]},
        'E': {'mass': [(3, 1, 1, 'E_mass')], 'critical': [(6, Q(1,2), 1, 'E_critical')],
              'prefix': [(2, alpha, 0, 'E_prefix')]},
        'O': {'mass': [(1, 1, 0, 'O_mass')], 'critical': [(2, Q(1,2), 0, 'O_critical')]},
        'K': {'mass': [(Q(3,2), Q(2,3), 0, 'K_mass')], 'critical': [(6, Q(1,6), 0, 'K_critical')]},
        'C': {norm: [(2, 0, 0, 'C_'+norm)] for norm in NORMS},
        '': {norm: [(1, 0, 0, 'delta_'+norm)] for norm in NORMS},
    }
    return {((factor,) if factor else (), norm, rule): (Q(e), h, Q(c), 1)
            for factor, norms in data.items() for norm, entries in norms.items()
            for c, e, h, rule in entries}


def _join(left, right):
    return (left[0]+right[0], left[1]+right[1], left[2]*right[2], 1+left[3]+right[3])


def _convert(cost, critical=False):
    return (cost[0]+(Q(1,2) if critical else 0), cost[1], cost[2], cost[3]+1)


def _optimal_costs(expressions, alpha, gamma, meter):
    """Independent bottom-up closure using position subsets then deduplication.

    All unordered multiset bipartitions are visited. Both choices of the
    prefix-carrying side are evaluated; empty factors are identity atoms.
    """
    atoms = _atoms(alpha, gamma)
    needed = {()}
    for expr in set(expressions):
        for size in range(1, len(expr)+1):
            for positions in combinations(range(len(expr)), size):
                meter.charge(len(positions)+1)
                needed.add(tuple(expr[i] for i in positions))
    meter.live(30*len(needed)+4096)
    best = {}
    for expr in sorted(needed, key=lambda e: (len(e), e)):
        options = {norm: [cost for (x, n, _), cost in atoms.items() if x == expr and n == norm]
                   for norm in NORMS}
        splits = set()
        for size in range(1, len(expr)):
            for indices in combinations(range(len(expr)), size):
                index_set = set(indices)
                left = tuple(expr[i] for i in indices)
                right = tuple(v for i, v in enumerate(expr) if i not in index_set)
                meter.charge(2*len(expr)+1)
                if left <= right:
                    splits.add((left, right))
        for left, right in splits:
            for norm in ('mass', 'critical'):
                options[norm].append(_join(best[left, norm], best[right, norm]))
            options['prefix'].append(_join(best[left, 'prefix'], best[right, 'mass']))
            options['prefix'].append(_join(best[left, 'mass'], best[right, 'prefix']))
            meter.charge(24)
        for norm in ('mass', 'critical'):
            _require(bool(options[norm]), 'norm closure missing atomic base')
            best[expr, norm] = min(options[norm])
        options['prefix'].extend((_convert(best[expr, 'mass']), _convert(best[expr, 'critical'], True)))
        best[expr, 'prefix'] = min(options['prefix'])
        meter.charge(12)
    return best


def verify_nodes(nodes, alpha, gamma, meter):
    _require(type(nodes) is list and len(nodes) <= 100000, 'bounded proof DAG')
    meter.live(50*len(nodes)+4096)
    atoms = _atoms(alpha, gamma)
    checked = {}
    norm_keys = set()
    for node in nodes:
        _require(type(node) is dict, 'proof node object')
        keys = {'id','expression','norm','constant','power','log_degree','rule','children','proof_size'}
        _require(set(node) == keys | ({'atom_rule'} if node.get('rule') == 'atom' else set()), 'exact node schema')
        ident = _integer(node['id'], 0, 100000)
        _require(ident not in checked, 'unique earlier proof node ids')
        expr = _expression(node['expression']); norm = node['norm']
        _require(type(norm) is str and norm in NORMS, 'known norm')
        _require((expr,norm) not in norm_keys, 'one best node per expression and norm')
        norm_keys.add((expr,norm))
        cost = (_rational(node['power'], meter), _integer(node['log_degree']),
                _rational(node['constant'], meter), _integer(node['proof_size'], 1, 1000000))
        _require(cost[2] > 0, 'positive proof constant')
        children = node['children']
        _require(type(children) is list and all(type(i) is int and i in checked for i in children),
                 'children must be previously verified ids')
        rule = node['rule']
        if rule == 'atom':
            _require(not children and (expr, norm, node['atom_rule']) in atoms, 'supplied atom rule')
            expected = atoms[expr, norm, node['atom_rule']]
        elif rule in ('mass_to_prefix', 'critical_to_prefix'):
            _require(len(children) == 1 and norm == 'prefix', 'prefix conversion arity and norm')
            child_expr, child_norm, child_cost = checked[children[0]]
            _require(child_expr == expr and child_norm == ('mass' if rule == 'mass_to_prefix' else 'critical'),
                     'prefix conversion premise')
            expected = _convert(child_cost, rule == 'critical_to_prefix')
        else:
            _require(rule in ('mass_convolution','critical_convolution','prefix_convolution') and len(children) == 2,
                     'supplied convolution rule')
            le, ln, lc = checked[children[0]]; rexp, rn, rc = checked[children[1]]
            _require(expr == tuple(sorted(le+rexp)), 'convolution factor recovery')
            if rule == 'prefix_convolution':
                _require(norm == 'prefix' and (ln,rn) in (('prefix','mass'),('mass','prefix')),
                         'prefix needs ordinary mass companion')
            else:
                target = 'mass' if rule == 'mass_convolution' else 'critical'
                _require(norm == ln == rn == target, 'matching multiplicative norms')
            expected = _join(lc, rc)
        _require(cost == expected, 'exact proof rule cost and tree size')
        checked[ident] = (expr,norm,cost)
        meter.charge(20+len(expr))
    return checked


def _source_terms(row, meter):
    _require(type(row) is dict, 'source geometry')
    _integer(row['id'],0,1000000)
    alpha = _rational(row['alpha'], meter); gamma = _rational(row['gamma'], meter)
    _require(0 < alpha < 1 and 0 < gamma < 1, 'strict rational cutoff geometry')
    modes = {'B': ('beta',2,0,'1/3'), 'U': ('-beta',1,1,'1/3'),
             'V': ('-beta',1,0,None), 'power': ('-R_u',0,1,'1/3')}
    _require(type(row['cases']) is list and len(row['cases']) == 4, 'all four original source modes')
    seen = set(); terms = {}
    for case in row['cases']:
        mode = case['mode']; name = mode['name']
        _require(type(name) is str, 'source mode name')
        _integer(mode['p'],0,2); _integer(mode['q'],0,2)
        _require(name in modes and name not in seen, 'unique complete source modes')
        seen.add(name)
        scalar,p,q,shift = modes[name]
        _require(mode == dict(name=name,coefficient=scalar,p=p,q=q,positive_shift=shift), 'exact original source scalar and mode')
        program = case['program']
        _integer(program['p'],0,2); _integer(program['q'],0,2)
        _require(set(program) == {'alpha','gamma','p','q','terms'} and
                 (program['alpha'],program['gamma'],program['p'],program['q']) == (row['alpha'],row['gamma'],p,q),
                 'source inverse program geometry')
        residual = {}; local = set()
        _require(type(program['terms']) is list and bool(program['terms']), 'source inverse polynomial retains unit')
        for term in program['terms']:
            _require(set(term) == {'a','b','coefficient'}, 'inverse term schema')
            a = _integer(term['a'],0,20); b = _integer(term['b'],0,20)
            coefficient = _rational(term['coefficient'], meter)
            _require(coefficient != 0 and (a,b) not in local and alpha*a+gamma*b < 1,
                     'unique nonzero original support-truncated monomials')
            local.add((a,b))
            terms[name,a,b] = (scalar,coefficient, tuple(sorted(['A']*p+['B']*q+['K']*int(shift is not None)+['S']*b)))
            for i in range(p+1):
                for j in range(q+1):
                    residual[a+i,b+j] = residual.get((a+i,b+j),Q(0))+coefficient*(-1)**(i+j)*comb(p,i)*comb(q,j)
                    meter.charge(8)
        residual[0,0] = residual.get((0,0),Q(0))-1
        _require(all(not c or alpha*a+gamma*b >= 1 for (a,b),c in residual.items()),
                 'original inverse polynomial exact recovery below support boundary')
    _require(len(terms) == row['component_count'], 'source component count')
    return alpha,gamma,terms


def _uniform(constant, power, log_degree, meter):
    if power > 0 or power == 0 and log_degree:
        return None
    if power == 0 or not log_degree:
        return constant
    ratio = Q(log_degree)/(-power)
    bits = max(abs(ratio.numerator).bit_length(),ratio.denominator.bit_length())
    _require(log_degree*(bits+1)+max(abs(constant.numerator).bit_length(),constant.denominator.bit_length())+2 <= 4096,
             'uniform payment rational bit cap before exponentiation')
    value = constant*2**log_degree*(1+ratio**log_degree)
    meter.charge(log_degree*10+10)
    if hasattr(meter,'number'):
        return meter.number(value)
    return value


def selection_depth(alternatives, meter):
    """Audit the declared partial-reduction preference, never a fitted value."""
    def metrics(alt):
        pieces = alt['pieces']; unpaid = [p for p in pieces if p['energy']['uniform_constant'] is None]
        paid = len(pieces)-len(unpaid)
        worst = max((_rational(p['energy']['power'],meter) for p in unpaid), default=Q(-1000))
        log = max((p['energy']['log_degree'] for p in unpaid if Q(p['energy']['power']) == worst), default=0)
        return paid,worst,log,len(pieces),alt['depth']
    baseline = metrics(alternatives[0]); eligible = [alternatives[0]]
    for alt in alternatives[1:]:
        candidate = metrics(alt)
        if baseline[0] == 0 and candidate[0] > 0 or candidate[1] < baseline[1]:
            eligible.append(alt)
    return min(eligible,key=lambda alt: (-metrics(alt)[0],)+metrics(alt)[1:])['depth']


def verify_search(row, result, meter):
    alpha,gamma,sources = _source_terms(row,meter)
    _require(type(result) is dict and result.get('schema') == 'core-prefix-proof-search-v1', 'prefix search schema')
    _require(result.get('geometry_id') == row['id'] and result.get('alpha') == row['alpha'] and result.get('gamma') == row['gamma'],
             'matching source geometry')
    _require(result.get('whole_signed_bound_proved') is False and result.get('RH_proved') is False,
             'whole signed target remains open')
    checked = verify_nodes(result['nodes'], alpha,gamma,meter)
    _require(type(result['terms']) is list and len(result['terms']) == len(sources), 'complete original source rows')
    seen = set(); expressions = []; piece_count = 0; selected = []
    for term in result['terms']:
        _require(set(term) == {'key','source_scalar','inverse_coefficient','alternatives','selected_depth'}, 'exact term schema')
        key = term['key']; _require(type(key) is dict and set(key) == {'mode','a','b'}, 'exact source key')
        _integer(key['a'],0,20); _integer(key['b'],0,20)
        _require(type(key['mode']) is str, 'source mode string')
        source_key = (key['mode'],key['a'],key['b'])
        _require(source_key in sources and source_key not in seen, 'missing, duplicate or unexpected source row')
        seen.add(source_key)
        scalar,inv,base = sources[source_key]; a = key['a']
        _require(term['source_scalar'] == scalar and _rational(term['inverse_coefficient'],meter) == inv,
                 'exact source scalar and inverse coefficient')
        alternatives = term['alternatives']
        _require(type(alternatives) is list and len(alternatives) == a+1, 'exhaustive centering depths')
        for depth,alt in enumerate(alternatives):
            _require(set(alt) == {'depth','pieces'} and type(alt['depth']) is int and alt['depth'] == depth,
                     'all ordered centering depths')
            _require(type(alt['pieces']) is list and len(alt['pieces']) == depth+1, 'all binomial and drift pieces')
            expected = {tuple(sorted(base+('R',)*(a-depth)+('E',)*j+('C','O')*(depth-j))):
                        inv*comb(depth,j)*(-1)**(depth-j) for j in range(depth+1)}
            got = {}
            for piece in alt['pieces']:
                _require(set(piece) == {'coefficient','expression','prefix_proof','energy'}, 'exact expanded piece schema')
                expr = _expression(piece['expression']); coefficient = _rational(piece['coefficient'],meter)
                _require(expr not in got and expr in expected and coefficient == expected[expr],
                         'exact complete binomial recovery including drift')
                got[expr] = coefficient
                ident = piece['prefix_proof']
                _require(type(ident) is int and ident in checked and checked[ident][:2] == (expr,'prefix'), 'prefix proof matches exact factors')
                cost = checked[ident][2]
                magnitude = Q(5) if scalar == '-R_u' else Q(9,2)
                constant = 4*(magnitude*abs(coefficient)*cost[2])**2
                power = 2*cost[0]-1; log_degree = 2*cost[1]
                uniform = _uniform(constant,power,log_degree,meter)
                expected_energy = dict(constant=str(constant),power=str(power),log_degree=log_degree,
                                       uniform_constant=None if uniform is None else str(uniform))
                _require(piece['energy'] == expected_energy, 'exact normalized energy and uniform payment')
                expressions.append(expr); piece_count += 1
                meter.charge(30+len(expr))
            _require(got == expected, 'full formal recovery; no centered support truncation')
        _require(type(term['selected_depth']) is int and term['selected_depth'] == selection_depth(alternatives,meter),
                 'declared reduction selection')
        selected.append(alternatives[term['selected_depth']])
    best = _optimal_costs(expressions+[expr for expr,_,_ in checked.values()],alpha,gamma,meter)
    for expr,norm,cost in checked.values():
        _require(cost == best[expr,norm], 'all stored nodes are optimal norm proofs')
    for term in result['terms']:
        for alt in term['alternatives']:
            for piece in alt['pieces']:
                expr,norm,cost = checked[piece['prefix_proof']]
                _require(cost == best[expr,norm], 'exhaustive DP optimum in supplied proof language')
                meter.charge(5)
    applications = 0
    atoms = _atoms(alpha,gamma)
    for expr,norm,_ in checked.values():
        applications += sum(x == expr and n == norm for x,n,_ in atoms)
        applications += 2*int(norm == 'prefix')
        pairs = set()
        for size in range(1,len(expr)):
            for positions in combinations(range(len(expr)),size):
                indices = set(positions)
                left = tuple(expr[i] for i in positions)
                right = tuple(v for i,v in enumerate(expr) if i not in indices)
                meter.charge(2*len(expr)+1)
                if left <= right: pairs.add((left,right))
        applications += sum(1 if norm != 'prefix' or left == right else 2 for left,right in pairs)
    statistics = dict(proof_nodes=len(checked),rule_applications=applications,original_terms=len(sources),
        alternatives=sum(t['key']['a']+1 for t in result['terms']),
        selected_centerings=sum(t['selected_depth'] > 0 for t in result['terms']),
        selected_pieces=sum(len(a['pieces']) for a in selected),
        uniformly_paid_pieces=sum(p['energy']['uniform_constant'] is not None for a in selected for p in a['pieces']))
    _require(result.get('statistics') == statistics, 'exact search accounting statistics')
    return dict(verified=True,geometry_id=row['id'],source_terms=len(sources),
                proof_nodes=len(checked),alternatives=sum(t['key']['a']+1 for t in result['terms']),
                expanded_pieces=piece_count,selected_pieces=sum(len(a['pieces']) for a in selected),
                exact_recovery_verified=True,exhaustive_prefix_optima_verified=True,
                whole_signed_bound_proved=False,RH_proved=False)


def verify_reduction(parent, construction, result, reduction, meter):
    """Check complete selected-piece partition and the signed join payment."""
    _require(type(parent) is dict and type(construction) is dict and type(reduction) is dict,
             'reduction inputs')
    _require(parent['source_geometry_ref'] == result['geometry_id'] and
             parent['source_geometry'] == dict(alpha=result['alpha'], gamma=result['gamma']),
             'reduction is bound to same inherited source geometry')
    inherited = parent['paid_component_reduction']
    _require(inherited.get('whole_signed_bound_proved') is False and inherited.get('older_fixed_recurrence_discharged') is False,
             'inherited signed obligation stays open')
    old = []
    for key in inherited['paid_components']:
        _require(type(key) is dict and set(key) == {'mode','a','b'}, 'inherited source key')
        old.append((key['mode'],key['a'],key['b']))
    _require(len(set(old)) == len(old), 'unique inherited paid keys')
    all_keys = {(t['key']['mode'],t['key']['a'],t['key']['b']) for t in result['terms']}
    _require(set(old) <= all_keys, 'inherited paid source exists')
    paid = []; unpaid = []; excluded = []
    for term in result['terms']:
        key = term['key']; alt = term['alternatives'][term['selected_depth']]
        for index,piece in enumerate(alt['pieces']):
            ref = dict(source_key=key,depth=alt['depth'],piece=index)
            if (key['mode'],key['a'],key['b']) in old:
                excluded.append(ref)
            elif piece['energy']['uniform_constant'] is None:
                unpaid.append(ref)
            else:
                paid.append(dict(ref,uniform_energy_constant=piece['energy']['uniform_constant']))
            meter.charge(8)
    channels = construction['channels']
    _require(type(channels) is list and bool(channels), 'complete channel list')
    channel_constant = Q(0)
    for channel in channels:
        eta = _rational(channel['eta'],meter)
        _require(0 <= eta <= 100, 'nonnegative bounded channel eta')
        coefficients = channel['polynomial']
        _require(type(coefficients) is list and 0 < len(coefficients) <= 100, 'nonempty bounded channel polynomial')
        values = [_rational(c,meter) for c in coefficients]
        variation = abs(values[0])+2*sum((abs(v) for v in values[1:]),Q(0))
        channel_constant += (2**ceil(eta)*variation)**2
        meter.charge(20+len(values))
    total = len(paid)*channel_constant*sum((_rational(p['uniform_energy_constant'],meter) for p in paid),Q(0))
    target = inherited['new_sufficient_goal']
    _require(target.get('status') == 'open' and target.get('same_finite_constant') is True,
             'inherited uniform target')
    _require(_rational(target['p'],meter) >= 0, 'nonnegative inherited target logarithmic degree')
    expected = dict(schema='core-prefix-proof-reduction-v1',parent_obligation_id=parent['parent_obligation_id'],
        geometry_id=result['geometry_id'],channel_abel_constant=str(channel_constant),
        old_paid_excluded=excluded,newly_paid=paid,remaining_signed_pieces=unpaid,
        combined_new_paid_constant=str(total),
        exact_split='Z_old=P_new+Z_new; Z_new=sum(all remaining signed pieces)-e; e=f-g',
        recovery='S_old<=2*S_new+2*C_new; S_new<=2*S_old+2*C_new',
        transport_error_retained=True,all_remaining_crosses_retained=True,
        common_horizon='N=4X-1 for both parent and child',
        goal=dict(expression='S_new(X)<=C*(1+log2X)^p for every dyadicX>=1',
                  p=target['p'],same_finite_constant=True,status='open'),
        analyst_nominated_selected_formula=False,proof_rules_are_supplied=True,
        original_fixed_recurrence_discharged=False,whole_signed_bound_proved=False,RH_proved=False)
    _require(reduction == expected, 'exact complete paid/unpaid partition, Abel payment, transport and open target')
    return dict(verified=True,geometry_id=result['geometry_id'],new_paid_pieces=len(paid),
                remaining_signed_pieces=len(unpaid),old_paid_excluded=len(excluded),
                channel_abel_constant=str(channel_constant),combined_new_paid_constant=str(total),
                transport_error_retained=True,whole_signed_bound_proved=False,RH_proved=False)
