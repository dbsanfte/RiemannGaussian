"""Search exact prime pairings of a signed Mobius residual stencil.

Search never receives Mobius values. Its finite coefficient bound is proved;
the growth of that bound across parents remains an arithmetic obligation.
"""
from fractions import Fraction as Q
from math import isqrt

import mobius_count_control_076 as C


MAX_PARENT = 16_000_003
MAX_TERMS = 1_000_000
MAX_COMPONENTS = 100_000
MAX_POLY_TERMS = 256


def poly(value):
    if type(value) is not dict or len(value) > MAX_POLY_TERMS:
        raise ValueError('bounded symbolic coefficient')
    result = {}
    for token, coefficient in value.items():
        if type(token) is not str or not 1 <= len(token) <= 256:
            raise ValueError('bounded real token name')
        a = C.S.B.rational(coefficient)
        if not a:
            raise ValueError('omit zero symbolic coefficients')
        result[token] = a
    return result


def add(target, value, scale=Q(1)):
    for token, a in value.items():
        new = target.get(token, Q(0)) + scale*a
        if new:
            target[token] = new
        else:
            target.pop(token, None)


def saved(value):
    return {token: str(a) for token, a in sorted(value.items()) if a}


def read_stencil(coefficients, meter):
    if type(coefficients) is not dict or len(coefficients) > MAX_TERMS:
        raise ValueError('bounded sparse stencil')
    terms = sum(len(v) for v in coefficients.values() if type(v) is dict)
    if terms > MAX_TERMS:
        raise ValueError('sparse term budget')
    meter.reserve(4096*(terms+len(coefficients)+1))
    result = {}
    for n, value in coefficients.items():
        if type(n) is not int or not 1 <= n <= MAX_PARENT:
            raise ValueError('positive bounded Mobius index')
        parsed = poly(value)
        if not parsed:
            raise ValueError('omit zero stencil rows')
        result[n] = parsed
    meter.charge(terms+len(coefficients))
    return result


def stencil_intervals(components, meter=None):
    """Collect prefix endpoint events before expanding any interval."""
    meter = meter or C.S.Meter()
    if type(components) is not list or len(components) > MAX_COMPONENTS:
        raise ValueError('bounded component list')
    term_budget = sum(len(c.get('weight', {})) for c in components if type(c) is dict)
    if term_budget > MAX_TERMS:
        raise ValueError('component term budget')
    meter.reserve(16384*(term_budget+len(components)+1))
    events = {}
    for component in components:
        if type(component) is not dict or set(component) != {'parent','weight'}:
            raise ValueError('exact component schema')
        parent = component['parent']
        if type(parent) is not int or not 0 <= parent <= MAX_PARENT:
            raise ValueError('bounded nonnegative source parent')
        weight = poly(component['weight'])
        for divisor, sign in ((8,1),(10,-1),(4,-1),(5,1)):
            endpoint = parent//divisor
            if endpoint:
                add(events.setdefault(1, {}), weight, Q(sign))
                add(events.setdefault(endpoint+1, {}), weight, Q(-sign))
        meter.charge(8*max(1,len(weight)))
    active, intervals, previous = {}, [], 1
    for endpoint in sorted(events):
        if endpoint > previous and active:
            intervals.append(dict(left=previous-1, right=endpoint-1, weight=saved(active)))
        add(active, events[endpoint])
        previous = endpoint
    if active:
        raise ArithmeticError('unpaid infinite stencil boundary')
    return intervals


def materialize(intervals, meter=None):
    meter = meter or C.S.Meter()
    total = sum((r['right']-r['left'])*len(r['weight']) for r in intervals)
    if total > MAX_TERMS:
        raise ValueError('stencil expansion term budget')
    meter.reserve(4096*(total+1))
    result, previous = {}, 0
    for row in intervals:
        left, right = row['left'], row['right']
        if type(left) is not int or type(right) is not int or not previous <= left < right <= MAX_PARENT:
            raise ValueError('ordered disjoint finite intervals')
        weight = saved(poly(row['weight']))
        if not weight:
            raise ValueError('omit empty interval')
        for n in range(left+1, right+1):
            result[n] = weight.copy()
        previous = right
    meter.charge(total)
    return result


def prime(p):
    return type(p) is int and 2 <= p <= 100_000 and all(p%d for d in range(2,isqrt(p)+1))


def fold(coefficients, p, prior_primes=(), meter=None):
    """Exact mu(pm)=-mu(m), including every squareful and boundary term."""
    meter = meter or C.S.Meter()
    if not prime(p) or len(prior_primes) > 32 or len(set(prior_primes)) != len(prior_primes) or any(not prime(r) for r in prior_primes) or p in prior_primes:
        raise ValueError('distinct bounded prime fold schedule')
    before = read_stencil(coefficients, meter)
    if any(n%r == 0 for n in before for r in prior_primes):
        raise ValueError('retained support must exclude prior primes')
    result = {}
    for n, weight in before.items():
        if n % (p*p) == 0:
            continue
        child, sign = (n//p, -1) if n%p == 0 else (n, 1)
        add(result.setdefault(child, {}), weight, Q(sign))
    meter.charge(10*sum(len(v) for v in before.values()))
    return {n: saved(value) for n,value in sorted(result.items()) if value}


def intervals_for_tokens(token_intervals):
    if type(token_intervals) is not dict or len(token_intervals) > MAX_TERMS:
        raise ValueError('bounded real token intervals')
    parsed = {}
    for token, endpoints in token_intervals.items():
        if type(token) is not str or type(endpoints) not in (list,tuple) or len(endpoints) != 2:
            raise ValueError('token interval schema')
        lo, hi = map(C.S.B.rational, endpoints)
        if lo > hi:
            raise ValueError('ordered token endpoints')
        parsed[token] = lo,hi
    return parsed


def coefficient_bound(coefficients, token_intervals, meter=None):
    meter = meter or C.S.Meter()
    terms = read_stencil(coefficients,meter)
    tokens = intervals_for_tokens(token_intervals)
    bound = Q(0)
    for weight in terms.values():
        lo = hi = Q(0)
        for token,a in weight.items():
            if token not in tokens:
                raise ValueError('missing token enclosure')
            ends = a*tokens[token][0],a*tokens[token][1]
            lo += min(ends); hi += max(ends)
        bound += max(abs(lo),abs(hi))
    return bound


def search_pairings(coefficients, token_intervals, primes=(2,3,5,7,11,13), depth=3, width=4, meter=None):
    """Beam search for a fully paid finite bound, without inspecting mu signs."""
    meter = meter or C.S.Meter()
    if not primes or len(primes)>16 or any(not prime(p) for p in primes) or len(set(primes))!=len(primes) or type(depth) is not int or not 0<=depth<=8 or type(width) is not int or not 1<=width<=16:
        raise ValueError('bounded prime construction grammar')
    terms = read_stencil(coefficients,meter)
    # Gates cover simultaneous retained states plus two transient proposals.
    meter.reserve(4096*(width*(depth+1)+2)*(1+sum(len(v) for v in terms.values())))
    initial = coefficient_bound(coefficients,token_intervals,meter)
    states = [((),coefficients,initial)]
    proposals = []
    for level in range(depth):
        children, seen = [], set()
        for schedule, before, previous_bound in states:
            for p in primes:
                if p in schedule:
                    continue
                canonical = tuple(sorted(schedule+(p,)))
                if canonical in seen:
                    continue
                seen.add(canonical)
                after = fold(before,p,schedule,meter)
                bound = coefficient_bound(after,token_intervals,meter)
                if bound>previous_bound:
                    raise ArithmeticError('coefficient l1 triangle budget increased')
                full = schedule+(p,)
                children.append((full,after,bound))
                proposals.append(dict(primes=list(full),l1_upper=str(bound),support=len(after)))
        if not children:
            break
        states = sorted(children,key=lambda s:(s[2],len(s[1]),s[0]))[:width]
        if not states[0][2]:
            break
    schedule,after,bound = min(states,key=lambda s:(s[2],len(s[1]),s[0]))
    return dict(schema='finite-residual-prime-pairing-search-v1',prime_schedule=list(schedule),
        coefficients=after,initial_l1_upper=str(initial),l1_upper=str(bound),
        reduction_ratio=str(bound/initial) if initial else None,proposals=proposals,
        mobius_values_used_for_selection=False,finite_constructive_bound_only=True,
        uniform_bound_proved=False,RH_proved=False,
        next_obligation='prove the folded signed aggregate or its paid coefficient norm is O(u^(q/2)) uniformly, with every excluded-prime condition and boundary retained')


def residual_components(program, row, prime_groups, precision=20):
    """Compile a proposed residual from separately admitted child groups.

    Prime groups map integer child to actual prime multiplicity. Their
    arithmetic completeness is a required external source admission, not
    supplied by a formal stencil or fold certificate.
    """
    spec = program['spec']
    C.admit_atoms(program['atoms'],spec)
    split = len(spec['theta'])-1
    if len(prime_groups)!=split or len(row['counts'])!=len(C.S.labels(spec)) or len(program['operator'])!=len(program['atoms']):
        raise ValueError('matching complete operator/source dimensions')
    u = row['u']
    if type(u) is not int or not 1<=u<=MAX_PARENT:
        raise ValueError('positive bounded source parent')
    weights = [{} for _ in row['counts']]
    tokens, definitions = {'1':['1','1']}, {'1':dict(kind='constant',value='1')}
    for atom, coefficient in zip(program['atoms'],program['operator']):
        column,gamma = C.atom_key(atom)
        count = row['counts'][column]
        if type(count) is not int or count<0 or (column>=split and count!=1):
            raise ValueError('actual nonnegative counts; direct count1')
        token = '1' if count<=1 or gamma==0 else 'count:'+str(count)+'^(-'+str(gamma)+')'
        if token not in tokens:
            lo,hi = C.count_bounds(count,gamma,precision)
            tokens[token] = [str(1/hi),str(1/lo)]
            definitions[token] = dict(kind='inverse_rational_count_power',count=count,gamma=str(gamma))
        add(weights[column],{token:C.S.B.rational(coefficient)},Q(-1))
    components = [dict(parent=u,weight={'1':'1'})]
    for i,group in enumerate(prime_groups):
        if type(group) is not dict or len(group)>MAX_COMPONENTS:
            raise ValueError('bounded prime child multiplicities')
        if any(type(j) is not int or not 0<=j<=u//2 or type(m) is not int or m<1 for j,m in group.items()) or sum(group.values())!=row['counts'][i]:
            raise ValueError('prime multiplicities and smaller children')
        for j,m in sorted(group.items()):
            if weights[i]:
                components.append(dict(parent=j,weight=saved({t:m*a for t,a in weights[i].items()})))
    for offset,d in enumerate(spec['multipliers']):
        if weights[split+offset]:
            components.append(dict(parent=u//d,weight=saved(weights[split+offset])))
    return dict(components=components,token_intervals=tokens,token_definitions=definitions,
        source_dependency='complete prime child groups and actual counts must match independent arithmetic admission',
        source_admission_supplied=False,uniform_bound_proved=False,RH_proved=False)


def certify_search(components, token_intervals, result):
    """Independent finite identities and bound, separate from source admission."""
    import check_mobius_residual_pairing_076 as CHECK
    before = materialize(stencil_intervals(components))
    stencil_check = CHECK.verify_stencil(components,before)
    if stencil_check['status']!='VERIFIED_IDENTITY':
        return dict(status='INVALID',stencil=stencil_check,uniform_bound_proved=False,RH_proved=False)
    certificates, prior = [], []
    for p in result['prime_schedule']:
        after = fold(before,p,prior)
        checked = CHECK.verify_fold(before,after,p,prior)
        certificates.append(checked)
        if checked['status']!='VERIFIED_IDENTITY':
            return dict(status='INVALID',folds=certificates,uniform_bound_proved=False,RH_proved=False)
        prior.append(p); before=after
    if before!=result['coefficients']:
        return dict(status='INVALID',reason='final coefficients changed',uniform_bound_proved=False,RH_proved=False)
    bound = CHECK.bound_coefficients(before,token_intervals)
    valid = bound['status']=='VERIFIED_BOUND' and bound['bound']==result['l1_upper']
    return dict(status='VERIFIED_FINITE_CONSTRUCTION' if valid else 'INVALID',
        stencil=stencil_check,folds=certificates,bound=bound,
        source_and_token_enclosure_admission_still_required=True,
        uniform_bound_proved=False,RH_proved=False)


def feedback_jobs(programs, dispositions):
    """Bind new construction searches to exact old formulas and obstructions."""
    lookup = {item['id']:item for item in dispositions}
    if len(lookup)!=len(dispositions) or {p['id'] for p in programs}!=set(lookup):
        raise ValueError('complete unique formula/disposition binding')
    jobs = []
    for item in programs:
        verdict = lookup[item['id']]
        formula = item['program']
        residual_refuted = any(x['lemma']=='innovation' and x['status']=='FINITE_COUNTEREXAMPLE' for x in verdict['unpaid_leaves'])
        jobs.append(dict(id=item['id'],program=formula,previous_status=verdict['status'],
            previous_domain=verdict['last_domain'],unpaid_leaves=verdict['unpaid_leaves'],
            baseline_control=not bool(formula['atoms']),
            current_residual_C_refuted=residual_refuted,
            fixed_false_C_is_not_a_proof_target=residual_refuted,
            requested_new_construction='shared Mobius stencil -> prime-toggle schedule -> certified coefficient bound or explicitly unpaid signed aggregate lemma',
            target=dict(q=formula['q'],all_integer_parents_above=formula['base_u'],
                finite_test_C=formula['innovation_C'],
                constant_policy='any replacement bound must come from a new verified construction; preserve the original counterexample'),
            proof_dependencies=['matching admitted actual prime child groups and count-power intervals',
                'exact source-to-stencil conservation', 'every prime fold and retained coprime domain',
                'uniform bound for the entire folded aggregate, including the unit and endpoint costs',
                'all previously unpaid correlation and original head/core/RH transfer leaves'],
            uniform_bound_proved=False,RH_proved=False))
    return dict(schema='signed-residual-construction-jobs-v1',jobs=jobs,
        construction_api=dict(compile='residual_components',endpoints='stencil_intervals',
            search='search_pairings',independent_admission='certify_search'),
        search_observes_mobius_values=False,new_scientific_pairing_search_run=False,
        prime_schedule_uniformity='a fixed schedule or a parameterized schedule needs a proof of its bound on every parent; pointwise winning schedules alone are not a theorem',
        untouched_parent_band='u//5 < n <= u//4 has coefficient -1 before arithmetic folding',
        all_uniform_arithmetic_obligations_paid=False,RH_proved=False)
