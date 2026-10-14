"""Search auxiliaries for a named, complete signed arithmetic obstruction.

The target is candidate10's R=T+C-m_u*x^(2/3), not a fitted surrogate.
All prospective global drift/correlation estimates remain explicit open leaves.
"""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
from math import isqrt

from flint import arb, ctx
import shifted_quotient_candidates as P

PROGRAM = {'shifts': ['1/3', '2/3']}
EXPONENTS = ['0', '1/6', '1/3', '1/2', '2/3']
SCOPE = dict(source='actual_mu_candidate10', domain='all dyadic integers X>=1',
             quantifiers='for every epsilon>0, exists C_epsilon independent of X')
TARGET = dict(id='candidate10_reduced_energy', scope=SCOPE,
              formula='X^-2 sum_{X<=n<2X}(T(n)+C(n)-m_u*n^(2/3))^2',
              required_bound='C_epsilon*X^epsilon',
              uniform_in=['all dyadic X>=1'], constants_may_depend_on=['epsilon'],
              complete_composite_branches=True, fixed_operator=PROGRAM,
              bridge='SHIFTED_QUOTIENT_CANDIDATE_10_REVIEW_001.txt sections3and5',
              status='open', RH_proved=False)


def root_floor(X, exponent):
    a = Q(exponent)
    if type(X) is not int or X < 1 or str(a) != exponent or not 0 <= a <= 1:
        raise ValueError('positive index and canonical fractional exponent in[0,1]')
    target = X**a.numerator
    low, high = 0, X+1
    while low+1 < high:
        middle = (low+high)//2
        if middle**a.denominator <= target: low = middle
        else: high = middle
    return low


def atom(name): return ['atom', name]
def add(left, right): return ['add', left, right]
def sub(left, right): return ['sub', left, right]


def validate_tree(tree, depth=0):
    if type(tree) is not list or not tree or depth > 16:
        raise ValueError('bounded state expression')
    op = tree[0]
    if op == 'atom' and len(tree) == 2 and tree[1] in ('T', 'V', 'R'):
        return 1
    if op in ('add', 'sub') and len(tree) == 3:
        return 1+sum(validate_tree(child, depth+1) for child in tree[1:])
    if op in ('shift', 'average') and len(tree) == 3 and tree[1] in EXPONENTS:
        return 1+validate_tree(tree[2], depth+1)
    raise ValueError('declared typed state production')


def _key(tree): return tuple(_key(x) if type(x) is list else x for x in tree)


def linear_identity(terms):
    """Exact cancellation in the free linear space of complete transformed atoms."""
    result = {}
    def visit(tree, coefficient):
        op = tree[0]
        if op == 'add':
            visit(tree[1], coefficient); visit(tree[2], coefficient)
        elif op == 'sub':
            visit(tree[1], coefficient); visit(tree[2], -coefficient)
        elif tree == atom('R'):
            visit(atom('T'), coefficient); visit(atom('V'), coefficient)
        else:
            key = _key(tree)
            result[key] = result.get(key, Q(0))+coefficient
    for coefficient, tree in terms:
        validate_tree(tree); visit(tree, Q(coefficient))
    return not any(result.values())


def catalogue():
    rows = [dict(id=0, generation=0, family='baseline', terms=[atom('R')], weights=['1'],
                 lane='baseline', uniform_bound_proved=False)]
    for channel, mode, exponent in product(('T', 'V'), ('shift', 'average'), EXPONENTS):
        old = atom(channel); other = atom('V' if channel == 'T' else 'T')
        transformed = [mode, exponent, old]
        U, D = add(other, transformed), sub(old, transformed)
        rows.append(dict(id=len(rows), generation=0, family='pair', lane=mode+'_'+channel,
                         channel=channel, mode=mode, exponent=exponent,
                         terms=[U, D], weights=['2', '2'],
                         padding_power=str(2*Q(exponent)-1),
                         padding_polylog_proved=Q(exponent) <= Q(1, 2),
                         bound_equivalence_only=True, uniform_bound_proved=False,
                         source_obligation=TARGET['id'], remaining='joint_energy_and_full_majorant_drift'))
    for a0, a1 in (('0', '0'), ('1', '1'), ('4/3', '4/3'), ('2', '0'), ('0', '2')):
        rows.append(dict(id=len(rows), generation=0, family='transport', lane='transport',
                         a0=a0, a1=a1, rho=str((Q(a0)**2+Q(a1)**2)/4),
                         terms=[], weights=[], uniform_bound_proved=False,
                         source_obligation=TARGET['id'], remaining='complete_signed_transport_defect'))
    return rows


def feedback(parent, ordinal, mode, exponent):
    """An unresolved joint-state energy becomes the input of the next production."""
    if parent['family'] != 'pair' or mode not in ('shift', 'average') or exponent not in ('1/3', '1/2'):
        raise ValueError('declared obligation-driven feedback rule')
    U1, D1 = deepcopy(parent['terms'])
    U2 = [mode, exponent, U1]; D2 = sub(U1, U2)
    return dict(id=ordinal, generation=1, family='feedback_pair', lane=parent['lane'],
                parent=parent['id'], feedback_obligation='joint_energy_'+str(parent['id']),
                source_obligation=TARGET['id'], mode=mode, exponent=exponent,
                parent_exponent=parent['exponent'], terms=[U2, D2, D1], weights=['4', '4', '2'],
                padding_power=str(max(2*Q(exponent)-1, Q(parent['padding_power']))),
                padding_polylog_proved=parent['padding_polylog_proved'],
                bound_equivalence_only=True, uniform_bound_proved=False,
                remaining='transformed_joint_energy_and_full_majorant_drift')


def generate_from_obligation(obligation, parent, ordinal, mode, exponent):
    """Dispatch a scoped unresolved energy into a construction on its actual AST."""
    if (obligation.get('status') != 'open' or obligation.get('scope') != SCOPE
            or obligation.get('expression') != ['energy', parent['terms'][0]]
            or obligation.get('id') != 'joint_energy_'+str(parent['id'])):
        raise ValueError('supported open joint-energy obligation with exact source and expression binding')
    program = feedback(parent, ordinal, mode, exponent)
    program['feedback_obligation'] = obligation['id']
    program['obligation_input'] = deepcopy(obligation)
    return program


def source_state(H, meter):
    """Producer: complete convolution, then literal prime-power branch split."""
    P.horizon(H); P.precision()
    workspace = P.Workspace('mu', H, meter)
    left, right = workspace.atom(Q(1, 3)), workspace.atom(Q(2, 3))
    coefficients = workspace.coefficients((Q(1, 3), Q(2, 3)))
    pp_left, pp_right = [arb(0)]*(H+1), [arb(0)]*(H+1)
    prime_power = [False]*(H+1)
    for n in range(2, H+1):
        p = workspace.spf[n]; rest = n
        while rest % p == 0:
            rest //= p; meter.charge(2)
        if rest == 1:
            prime_power[n] = True; pp_left[n] = left[n]; pp_right[n] = right[n]
    pair = P.convolution(pp_left, pp_right, meter)
    m = P.normalizer(PROGRAM, meter)[0]['coefficient']
    atoms = {name: [arb(0)]*(H+1) for name in ('T', 'V', 'R')}
    totals = {name: arb(0) for name in ('T', 'C', 'D', 'S')}
    for n in range(1, H+1):
        d = pair[n] if prime_power[n] else arb(0)
        totals['D'] += d
        totals['T'] += arb(0) if prime_power[n] else pair[n]
        totals['C'] += coefficients[n]-pair[n]
        totals['S'] += coefficients[n]
        meter.charge(64+12)
        main = m*arb(n)**(arb(2)/3)
        atoms['T'][n] = totals['T']
        atoms['V'][n] = totals['C']-main
        atoms['R'][n] = totals['S']-totals['D']-main
    meter.live(20*(H+1)+4096)
    return dict(atoms=atoms, H=H, main_coefficient=m)


def extent(tree, X):
    op = tree[0]
    if op == 'atom': return 0
    if op in ('add', 'sub'): return max(extent(tree[1], X), extent(tree[2], X))
    h = root_floor(X, tree[1])
    return extent(tree[2], X)+(h if op == 'shift' else h-1)


def required_horizon(programs, scales):
    result = 1
    for p in programs:
        for X in scales:
            if p['family'] == 'transport': result = max(result, 4*X-1)
            for tree in p['terms']:
                result = max(result, 4*X-1+extent(tree, 2*X))
    return result


def evaluate_tree(tree, X, start, stop, state, meter):
    if start < 1 or stop-1+extent(tree, X) > state['H']:
        raise ValueError('complete transform lookahead required')
    op = tree[0]
    meter.charge(stop-start+1)
    if op == 'atom': return state['atoms'][tree[1]][start:stop]
    if op in ('add', 'sub'):
        a = evaluate_tree(tree[1], X, start, stop, state, meter)
        b = evaluate_tree(tree[2], X, start, stop, state, meter)
        return [x+y if op == 'add' else x-y for x, y in zip(a, b)]
    h = root_floor(X, tree[1])
    if op == 'shift': return evaluate_tree(tree[2], X, start+h, stop+h, state, meter)
    values = evaluate_tree(tree[2], X, start, stop+h-1, state, meter)
    prefix = [arb(0)]
    for v in values: prefix.append(prefix[-1]+v)
    meter.charge(len(values)+2*(stop-start))
    return [(prefix[j+h]-prefix[j])/h for j in range(stop-start)]


def _inner(left, right, X, meter):
    meter.charge(2*len(left)+1)
    return sum((a*b for a, b in zip(left, right)), arb(0))/(X*X)


def measure(program, X, state, meter, evaluator=evaluate_tree):
    if type(X) is not int or X < 1:
        raise ValueError('positive complete scale')
    if program['family'] == 'transport':
        if 4*X-1 > state['H']: raise ValueError('complete two-child block')
        parent = state['atoms']['R'][X:2*X]
        child = [state['atoms']['R'][2*X:4*X:2], state['atoms']['R'][2*X+1:4*X:2]]
        a = list(map(P.real, (program['a0'], program['a1'])))
        residual = [[v-a[j]*r for v, r in zip(child[j], parent)] for j in (0, 1)]
        meter.charge(4*X)
        E = _inner(parent, parent, X, meter)
        Echild = sum((_inner(c, c, X, meter) for c in child), arb(0))/4
        cross = sum((2*a[j]*_inner(parent, residual[j], X, meter) for j in (0, 1)), arb(0))/4
        positive = sum((_inner(d, d, X, meter) for d in residual), arb(0))/4
        drift = Echild-P.real(program['rho'])*E
        if not drift.overlaps(cross+positive): raise ArithmeticError('complete transport identity')
        return dict(X=X, energy=E, child_energy=Echild, majorant=E, child_majorant=Echild,
                    drift=drift, cross=cross, positive=positive,
                    open_quantity=drift, correction=positive)
    if not linear_identity([('1', atom('R'))]+[('-1', t) for t in program['terms']]):
        raise ValueError('exact complete target decomposition required')
    values = []
    for base in (X, 2*X):
        rows = [evaluator(tree, base, base, 2*base, state, meter) for tree in program['terms']]
        gram = [[_inner(a, b, base, meter) for b in rows] for a in rows]
        energy = _inner(state['atoms']['R'][base:2*base], state['atoms']['R'][base:2*base], base, meter)
        total = sum((value for row in gram for value in row), arb(0))
        if not energy.overlaps(total): raise ArithmeticError('full signed Gram complement retained')
        diagonal = [gram[i][i] for i in range(len(rows))]
        F = sum((P.real(w)*g for w, g in zip(program['weights'], diagonal)), arb(0))
        # Compare against the exact Young gap without inferring a universal theorem from samples.
        if program['family'] == 'pair':
            gap = gram[0][0]+gram[1][1]-2*gram[0][1]
        elif program['family'] == 'feedback_pair':
            gap = (2*(gram[0][0]+gram[1][1]-2*gram[0][1])
                   +gram[0][0]+gram[1][1]+gram[2][2]+2*gram[0][1]-2*gram[0][2]-2*gram[1][2])
        else: gap = arb(0)
        if not (F-energy).overlaps(gap): raise ArithmeticError('whole Young gap')
        values.append(dict(energy=energy, F=F, correction=sum(diagonal[1:], arb(0)),
                           joint=diagonal[0], cross=total-sum(diagonal, arb(0))))
    first, second = values
    return dict(X=X, energy=first['energy'], child_energy=second['energy'],
                majorant=first['F'], child_majorant=second['F'], drift=second['F']-first['F'],
                cross=first['cross'], positive=first['joint'],
                open_quantity=first['joint'], correction=first['correction'])


def encoded(row):
    return {k: v if k == 'X' else v.str(45, radius=True) for k, v in row.items()}


def fitted_drift(rows, meter):
    upper = arb(0)
    for row in rows:
        upper = max(upper, row['drift'].upper())
        meter.charge(3)
    return str(Q(max(0, int((upper*2**32).ceil().unique_fmpz())), 2**32))


def score(rows, constant, meter):
    cap = P.real(constant)
    meter.charge(3*len(rows))
    return dict(failed=sum(not bool(row['drift'] <= cap) for row in rows),
                passed=[bool(row['drift'] <= cap) for row in rows],
                max_drift=max(float(row['drift'].mid()) for row in rows),
                finite_drift_only=True, uniform_bound_proved=False)


def rank(record):
    p = record['program']
    # A proved correction exponent is useful, but is never called a proved target exponent.
    power = Q(p.get('padding_power', '0'))
    return (0 if p.get('padding_polylog_proved', False) else 1,
            max(Q(0), power), record['validation_score']['failed'],
            sum(validate_tree(t) for t in p['terms']), p['id'])


def select_parents(records):
    result = []
    for lane in ('shift_T', 'shift_V', 'average_T', 'average_V'):
        options = [r for r in records if r['program']['lane'] == lane
                   and r['program']['family'] == 'pair' and r['program']['exponent'] != '0']
        result.append(min(options, key=rank)['program'])
    return result


def next_obligations(program):
    """The surviving expression, scope and dependency become generator inputs."""
    if program['family'] == 'transport':
        return [dict(id='transport_defect_'+str(program['id']), scope=SCOPE, status='open',
                     expression='1/4 sum_j [2*a_j*<R,D_j>_X+||D_j||_X^2]',
                     bound='a finite constant independent of X', depends_on=[],
                     next_productions=['paired_average_split', 'largest_prime_three_channel_transfer'],
                     equivalent_to_target_not_certified=True)]
    if program['family'] == 'baseline': return [deepcopy(TARGET)]
    return [dict(id='joint_energy_'+str(program['id']), scope=SCOPE, status='open',
                 expression=['energy', program['terms'][0]], bound='C_epsilon*X^epsilon',
                 proved_padding=program['padding_polylog_proved'],
                 equivalence_class=TARGET['id'] if program['padding_polylog_proved'] else None,
                 next_productions=['shift_joint_state', 'average_joint_state',
                                   'largest_prime_three_channel_transfer'],
                 new_arithmetic_bound_proved=False),
            dict(id='majorant_drift_'+str(program['id']), scope=SCOPE, status='open',
                 expression=['dyadic_difference', ['weighted_energy', program['weights'], program['terms']]],
                 bound='a finite constant independent of X',
                 depends_on=[], finite_fit_is_not_a_premise=True)]
