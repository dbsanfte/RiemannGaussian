"""Search signed arithmetic pairings with complete, priced residuals.

Policies read indices, floor/profile labels and actual source signs. They
cannot choose edges by inspecting numerical magnitudes. Cost observations
rank the resulting programs; no finite growth fit becomes a uniform bound.
"""
from collections import defaultdict, deque
from fractions import Fraction as Q
from math import fsum, gcd, isfinite

from prime_transfer_algebra_058 import Meter

MAX_POLICY_STEPS = 2
MAX_POWER_BITS = 1_000_000
MAX_TOKENS = 400_000
BETAS = ['1/3', '2/5', '1/2', '3/5', '2/3', '1']
CONSTANTS = [Q(2)**j for j in range(-30, 9)]


def _q(value):
    if type(value) is not str or len(value) > 2500: raise ValueError('bounded canonical rational')
    result = Q(value)
    if str(result) != value or max(abs(result.numerator).bit_length(), result.denominator.bit_length()) > 4096:
        raise ValueError('canonical rational within resource domain')
    return result


def floor_power(N, theta, meter=None):
    meter = meter or Meter(); t = _q(theta)
    if type(N) is not int or N < 2 or not 0 <= t <= 1: raise ValueError('integer scale and block exponent in[0,1]')
    if t == 0: return 1
    if t == 1: return N
    bits = N.bit_length()*max(t.numerator, t.denominator)
    if bits > MAX_POWER_BITS: raise OverflowError('exact block-power work cap')
    meter.charge(bits)
    target = pow(N, t.numerator); low, high = 1, N+1
    while high-low > 1:
        mid = (low+high)//2
        meter.charge(bits)
        if pow(mid,t.denominator) <= target: low = mid
        else: high = mid
    return low


def exponent_grid(max_denominator=8):
    if type(max_denominator) is not int or not 1 <= max_denominator <= 32:
        raise ValueError('finite exponent enumeration budget')
    return sorted({Q(a,b) for b in range(1,max_denominator+1) for a in range(1,b+1)}
                  |{Q(1,257),Q(2,11),Q(3,11)})


def _scan(group='all', order='asc', method='stack', **kw):
    return {'kind':'scan','group':group,'order':order,'method':method,**kw}


def normalize_kernel(terms):
    """sum c_b Phi(b*d) -> common normalized kernel at an exact scaled d."""
    if type(terms) is not list or not 1 <= len(terms) <= 16: raise ValueError('finite kernel expression')
    coefficients={}
    for term in terms:
        if type(term) is not list or len(term)!=2: raise ValueError('exact base/coefficient kernel term')
        base,c=term
        if type(base) is not int or not 1<=base<=1_000_000: raise ValueError('positive bounded kernel base')
        coefficients[base]=coefficients.get(base,Q(0))+_q(c)
    coefficients={b:c for b,c in coefficients.items() if c}
    if not coefficients: raise ValueError('nonzero formal kernel')
    anchor=min(coefficients)
    return anchor,tuple((Q(b,anchor),c) for b,c in sorted(coefficients.items()))


def source_kernel_expressions(p,q):
    if type(p) is not int or type(q) is not int or not 2<=p<q: raise ValueError('ordered source bases')
    return {'P':[[p,'1']],'Q':[[q,'1']],'D':[[p,'1'],[q,'-1']],'S':[[p,'1'],[q,'1']]}


def validate_policy(policy):
    if type(policy) is not dict or set(policy) != {'steps'} or type(policy['steps']) is not list or len(policy['steps']) > MAX_POLICY_STEPS:
        raise ValueError('bounded exact pairing policy')
    for step in policy['steps']:
        if type(step) is not dict: raise ValueError('typed pairing step')
        if step.get('kind') == 'scan':
            fields = {'kind','group','order','method'}
            group = step.get('group')
            if group == 'profile_block': fields.add('theta')
            elif group == 'profile_residue': fields.add('modulus')
            elif group not in ('all','profile','sector','profile_quotient'): raise ValueError('declared arithmetic grouping')
            if set(step) != fields or step['order'] not in ('asc','desc') or step['method'] not in ('stack','fifo'):
                raise ValueError('exact scan semantics')
            if group == 'profile_block' and not 0 <= _q(step['theta']) <= 1: raise ValueError('block exponent in[0,1]')
            if group == 'profile_residue' and (type(step['modulus']) is not int or not 2 <= step['modulus'] <= 100000):
                raise ValueError('bounded positive residue modulus')
        elif step.get('kind') == 'kernel_scan':
            if set(step)!={'kind','kernels','order','method'} or step['order'] not in ('asc','desc') or step['method'] not in ('stack','fifo'):
                raise ValueError('exact shared-kernel scan')
            if type(step['kernels']) is not dict or set(step['kernels'])!={'P','Q','D','S'}: raise ValueError('complete source kernel dictionary')
            for terms in step['kernels'].values(): normalize_kernel(terms)
        elif step.get('kind') == 'prime_ratio':
            if set(step) != {'kind','group','order'} or step['group'] not in ('all','profile') or step['order'] not in ('asc','desc'):
                raise ValueError('complete prime-ratio semantics')
        else: raise ValueError('unknown pairing construction')
    return policy


def family(policy):
    if not policy['steps']: return 'unmatched_control'
    if any(s['kind'] == 'prime_ratio' for s in policy['steps']): return 'prime_ratio'
    if any(s['kind'] == 'kernel_scan' for s in policy['steps']): return 'shared_kernel_scan'
    groups = {s['group'] for s in policy['steps']}
    if groups <= {'all'}: return 'global_scan'
    if groups <= {'all','profile'}: return 'profile_scan'
    return 'arithmetic_partition'


def grammar(max_denominator=8,kernels=None):
    scans = []
    groups = [(g,{}) for g in ('all','profile','sector','profile_quotient')]
    groups += [('profile_residue',{'modulus':r}) for r in (7,11,13)]
    groups += [('profile_block',{'theta':str(t)}) for t in exponent_grid(max_denominator)]
    for group, params in groups:
        for order in ('asc','desc'):
            for method in ('stack','fifo'): scans.append(_scan(group,order,method,**params))
    primes = [{'kind':'prime_ratio','group':g,'order':o} for g in ('all','profile') for o in ('asc','desc')]
    kernel_passes=[] if kernels is None else [
        {'kind':'kernel_scan','kernels':kernels,'order':order,'method':method}
        for order in ('asc','desc') for method in ('stack','fifo')]
    policies = [{'steps':[]}]
    seen = {()}
    for first in scans+primes+kernel_passes:
        for tail in (None, _scan(), _scan('profile')):
            if tail is not None and first == tail: continue
            steps = [first] if tail is None else [first,tail]
            # A literal canonical program key is an algorithmic deduplication
            # key, not a file/protocol hash. Kernel dictionaries are finite.
            key = tuple(repr(sorted(s.items())) for s in steps)
            if key in seen: continue
            seen.add(key); policies.append(validate_policy({'steps':steps}))
    return [{'id':'mobius_transport_'+str(i).zfill(4),'policy':p,'family':family(p)} for i,p in enumerate(policies)]


def profile_dominance(programs):
    """Universal cost comparison; does not give the reference a growth bound.

    Each profile has a positive decreasing Laplace kernel in d. Its sorted
    adjacent cancellation realizes integral |signed threshold discrepancy|.
    Any within-profile matching pays at least that amount, including all
    unmatched terms sent to zero. See the independent059 mathematical review.
    """
    reference = next(r for r in programs if r['policy'] == {'steps':[_scan('profile')]})
    scored, excluded = [], []
    for r in programs:
        steps = validate_policy(r['policy'])['steps']
        separated = all(s['kind']!='kernel_scan' and s['group']!='all' for s in steps)
        if steps and separated and r['id'] != reference['id']:
            excluded.append({'id':r['id'],'reference_id':reference['id'],
                'status':'DOMINATED_BY_PROFILE_OPTIMUM',
                'cost_comparison':'B_reference(N)<=B_policy(N) at every integerN in the source domain',
                'uniform_cost_comparison_proved':True,'uniform_growth_bound_proved':False})
        else: scored.append(r)
    return {'reference_id':reference['id'],'scored':scored,'excluded':excluded}


class Context:
    def __init__(self): self.powers, self.edges = {}, {}


def _tokens(tokens):
    if type(tokens) is not list or len(tokens) > MAX_TOKENS: raise ValueError('bounded complete token table')
    by_d = {}
    for t in tokens:
        if type(t) is not dict or type(t.get('d')) is not int or t['d'] < 1 or t.get('profile') not in ('P','Q','D','S'):
            raise ValueError('typed arithmetic token')
        if type(t.get('sign')) is not int or t['sign'] not in (-1,1) or type(t.get('kernel_sign')) is not int or t['kernel_sign'] not in (-1,1):
            raise ValueError('exact nonzero signs')
        if type(t.get('mu')) is not int or t['mu'] not in (-1,1) or t['sign'] != t['mu']*t['kernel_sign']:
            raise ValueError('source sign must include ordinarymu and kernel sign')
        if t['d'] in by_d: raise ValueError('one token per cofactor')
        by_d[t['d']] = t
    return by_d


def _prime_edges(ids, context, meter):
    key = tuple(ids)
    if key in context.edges: meter.charge(); return context.edges[key]
    available = set(ids); edges = []
    for d in ids:
        n, p = d, 2
        while p*p <= n:
            meter.charge(4)
            if n % p == 0:
                if d//p in available: edges.append((p,d//p,d))
                while n % p == 0: n //= p; meter.charge()
            p = 3 if p == 2 else p+2
        if n > 1 and d//n in available: edges.append((n,d//n,d))
    edges.sort(); meter.charge(4*len(edges))
    context.edges[key] = edges
    return edges


def build_plan(N, tokens, policy, meter=None, context=None):
    meter = meter or Meter(); context = context or Context()
    validate_policy(policy)
    if type(N) is not int or N < 2: raise ValueError('integer parent scale')
    by_d = _tokens(tokens); ids = sorted(by_d); available = set(ids); pairs = []
    meter.reserve(1024+512*len(ids)); meter.charge(8*len(ids))

    def pair(a,b):
        if by_d[a]['sign'] == by_d[b]['sign'] or a not in available or b not in available:
            raise ArithmeticError('distinct available opposite source signs')
        pairs.append([a,b] if by_d[a]['sign'] > 0 else [b,a])
        available.remove(a); available.remove(b); meter.charge(8)

    for step in policy['steps']:
        if step['kind'] == 'prime_ratio':
            edges = _prime_edges(ids,context,meter)
            for p,a,b in edges if step['order'] == 'asc' else reversed(edges):
                meter.charge(4)
                if a in available and b in available and by_d[a]['sign'] != by_d[b]['sign']:
                    if step['group'] == 'all' or by_d[a]['profile'] == by_d[b]['profile']: pair(a,b)
            continue
        if step['kind']=='kernel_scan':
            normalized={tag:normalize_kernel(terms) for tag,terms in step['kernels'].items()}
            groups=defaultdict(list)
            for d in ids:
                if d not in available: continue
                anchor,key=normalized[by_d[d]['profile']]
                groups[key].append((anchor*d,d));meter.charge(8)
            for key in sorted(groups):
                waiting=deque()
                for index,d in sorted(groups[key],reverse=step['order']=='desc'):
                    if waiting and by_d[waiting[-1]]['sign']!=by_d[d]['sign']:
                        a=waiting.pop() if step['method']=='stack' else waiting.popleft()
                        pair(a,d)
                    else: waiting.append(d)
                    meter.charge(4)
            continue
        group = step['group']; width = None
        if group == 'profile_block':
            key = (N,step['theta'])
            if key not in context.powers: context.powers[key] = floor_power(N,step['theta'],meter)
            width = context.powers[key]
        groups = defaultdict(list)
        for d in ids if step['order'] == 'asc' else reversed(ids):
            if d not in available: continue
            token = by_d[d]; profile = token['profile']
            if group == 'all': key = ()
            elif group == 'profile': key = (profile,)
            elif group == 'sector': key = (profile,token['kernel_sign'])
            elif group == 'profile_quotient': key = (profile,N//d)
            elif group == 'profile_residue': key = (profile,d%step['modulus'])
            else: key = (profile,d//width)
            groups[key].append(d); meter.charge(6)
        for key in sorted(groups):
            waiting = deque()
            for d in groups[key]:
                if waiting and by_d[waiting[-1]]['sign'] != by_d[d]['sign']:
                    a = waiting.pop() if step['method'] == 'stack' else waiting.popleft()
                    pair(a,d)
                else: waiting.append(d)
                meter.charge(4)
    return {'pairs':pairs,'unmatched':sorted(available)}


def plan_cost(tokens,plan,meter=None):
    meter = meter or Meter(); by_d = _tokens(tokens)
    if type(plan) is not dict or set(plan) != {'pairs','unmatched'}: raise ValueError('complete pairing plan')
    used = [] ; charges = []
    for pair in plan['pairs']:
        if type(pair) is not list or len(pair) != 2: raise ValueError('two indices per pair')
        a,b = pair
        if a not in by_d or b not in by_d or by_d[a]['sign'] == by_d[b]['sign']: raise ValueError('opposite source terms')
        charges.append(abs(by_d[a]['magnitude']-by_d[b]['magnitude'])); used += pair
    for d in plan['unmatched']:
        if d not in by_d: raise ValueError('retained actual unmatched token')
        charges.append(by_d[d]['magnitude']); used.append(d)
    if sorted(used) != sorted(by_d): raise ValueError('every source term exactly once')
    if any(not isfinite(v) or v < 0 for v in charges): raise ArithmeticError('finite positive transport charges')
    meter.charge(16*len(by_d))
    return fsum(charges)


def evaluate_policies(N,tokens,programs,meter=None):
    meter = meter or Meter(); context = Context(); results = []; costs = {}
    for r in programs:
        plan = build_plan(N,tokens,r['policy'],meter,context)
        key = (tuple(sorted(tuple(pair) for pair in plan['pairs'])),tuple(plan['unmatched']))
        if key not in costs:
            meter.reserve(1024+128*(len(costs)+1)*(len(tokens)+1))
            costs[key] = plan_cost(tokens,plan,meter)
        else: meter.charge()
        cost = costs[key]
        results.append({'id':r['id'],'cost':cost,'paired_tokens':2*len(plan['pairs']),
            'unmatched_tokens':len(plan['unmatched'])})
    return results


def hypotheses(programs,observations):
    if not observations: raise ValueError('nonempty discovery observations')
    result = []
    values = {n:{v['id']:v['cost'] for v in row['costs']} for n,row in observations.items()}
    for program in programs:
        for beta in BETAS:
            b = float(Q(beta))
            required = max(values[n][program['id']]/n**b for n in values)
            C = next((v for v in CONSTANTS if float(v) >= required*(1+1e-10)),None)
            ratios = [values[n][program['id']]/observations[n]['absolute_sum'] for n in values
                      if observations[n]['absolute_sum'] > 0]
            result.append({'program_id':program['id'],'family':program['family'],
                'claim':{'C':str(C),'beta':beta} if C is not None else None,
                'required_C_float':required,'worst_cost_over_L1_float':max(ratios,default=0),
                'mean_cost_over_L1_float':fsum(ratios)/len(ratios) if ratios else 0,
                'policy_steps':len(program['policy']['steps']),
                'screening_only':True,'uniform_bound_proved':False,'RH_proved':False})
    return result


def select(rows,programs):
    selected = []; seen = set()
    def add(r,reason):
        if r is None: return
        key = (r['program_id'],r['claim']['C'],r['claim']['beta'])
        if key not in seen: selected.append({**r,'selection_reason':reason}); seen.add(key)
    def rank(r):
        return (Q(r['claim']['C']),r['required_C_float'],r['policy_steps'],r['program_id'])
    fitted = [r for r in rows if r['claim'] is not None]
    for beta in BETAS:
        pool = [r for r in fitted if r['claim']['beta'] == beta]
        add(min(pool,key=rank) if pool else None,'best declared exponent class')
    for name in ('global_scan','profile_scan','shared_kernel_scan','arithmetic_partition','prime_ratio'):
        pool = [r for r in fitted if r['family'] == name and r['claim']['beta'] == '1/2']
        add(min(pool,key=rank) if pool else None,'sqrt-scale mechanism diversity')
    control = next((r for r in fitted if r['family'] == 'unmatched_control' and r['claim']['beta'] == '1/2'),None)
    add(control,'complete absolute-sum control')
    if control is not None:
        add({**control,'claim':{'C':'0','beta':'1/2'}},'declared zero-cost negative control')
    return [{'id':'transport_claim_'+str(i).zfill(3),**r} for i,r in enumerate(selected)]
