"""Generate signed arithmetic structures with scoped semantics and exposure plans.

Selection nominates unproved candidates. Neither the supplied grammar nor its
mechanism labels are exhaustive descriptions of arithmetic cancellation.
"""
from copy import deepcopy
from fractions import Fraction as Q
from math import gcd

from potential_candidate_discovery import (
    canonical, integer, variable, root, floor_div, prefix, add, scale, product,
    node_count, complexity, state_program, remap, fit_constants, assess,
    anchored_cost, FLAGS, LEVELS, obligation as base_obligation,
)
import potential_candidate_semantics as S

FAMILIES = ('calibration', 'source_mixture', 'factor_bank', 'prime_bank', 'index_switch')
TRAIN = (1, 2, 4, 8, 16, 32, 64, 128)
VALIDATION = (192, 256, 384, 512)
FINAL = (1536, 2048, 3072, 4096)
DISCOVERY_MAX = 1024
CALIBRATION = ('lag', 'mask', 'bounded_root', 'target_copy')
SLOTS = ('calibration', 'coupled_sum', 'coupled_bank', 'nonlinear', 'exploration')


class SelectorDomainCap(ValueError):
    """An unsupported local selector envelope, distinct from spent work limits."""


def _power(n, exponent, meter):
    bits=max(1,abs(n).bit_length())*exponent
    if bits>meter.max_bits: raise SelectorDomainCap('selector power bit preflight')
    meter.charge(bits+1)
    return meter.number(n**exponent)


def _floor_root(n, a, b, meter):
    if n < 0 or a < 0 or b < 1:
        raise ValueError('nonnegative exact selector root')
    common=gcd(a,b); a//=common; b//=common
    if a==0: return 1
    if n in (0,1): return n
    target = _power(n,a,meter)
    low, high = 0, 1 << ((target.bit_length()+b-1)//b)
    while low + 1 < high:
        meter.charge(b + 2)
        mid = (low + high) // 2
        if _power(mid,b,meter) <= target:
            low = mid
        else:
            high = mid
    return low


def _index(tree, context, meter):
    meter.charge()
    op = tree[0]
    if op == 'int': return tree[1]
    if op == 'v': return context[tree[1]]
    if op == 'root': return _floor_root(_index(tree[1], context, meter), tree[2], tree[3], meter)
    if op not in ('max', 'min', 'iadd', 'isub', 'imul', 'idiv', 'imod', 'gcd'):
        raise ValueError('unsupported selector')
    left, right = (_index(t, context, meter) for t in tree[1:])
    if op == 'max': return max(left, right)
    if op == 'min': return min(left, right)
    if op == 'iadd': return meter.number(left + right)
    if op == 'isub': return meter.number(left - right)
    if op == 'imul':
        if abs(left).bit_length()+abs(right).bit_length()>meter.max_bits+1:
            raise SelectorDomainCap('selector multiplication bit preflight')
        return meter.number(left * right)
    if op == 'idiv': return left // right
    if op == 'imod': return left % right
    return gcd(left, right)


def _variables(tree):
    if tree[0] == 'v': return {tree[1]}
    return set().union(*(_variables(x) for x in tree[1:] if isinstance(x, list)))


def _prime(n, meter):
    if n < 2: return False
    d = 2
    while d*d <= n:
        meter.charge()
        if n % d == 0: return False
        d += 1
    return True


def _squarefree(n, meter):
    d = 2
    while d*d <= n:
        meter.charge()
        if n % (d*d) == 0: return False
        d += 1
    return n >= 1


def _radical(n, meter):
    if n < 1: raise ValueError('positive moving modulus')
    answer, d = 1, 2
    while d*d <= n:
        meter.charge()
        if n % d == 0:
            answer *= d
            while n % d == 0:
                meter.charge(); n //= d
        d += 1
    return answer*n


def selectors(program, meter):
    """Finite AST descriptors; unsupported index maps retain unknown coverage."""
    found = []; other_roots=[]
    def walk(tree, path, parent=None):
        meter.charge()
        op = tree[0]
        if op in ('imod', 'gcd'):
            selector = tree[2]
            if _variables(selector) == {'X'}:
                coprime=op=='gcd' and parent is not None and parent[0]=='eq' and (
                    parent[1]==tree and parent[2]==integer(1) or parent[2]==tree and parent[1]==integer(1))
                found.append(dict(path=path+[2], kind='coprime_radical' if coprime else 'gcd_modulus' if op=='gcd' else 'residue_modulus',
                                  tree=deepcopy(selector), scope='effective modulus, not a weighted-correlation estimate'))
        if op == 'sum' and _variables(tree[3]) == {'X'}:
            binder, body = tree[1], tree[4]
            is_prime = body[0]=='guard' and body[1]==['prime', variable(binder)]
            point = ['x', variable(binder)]
            is_mu = body[0]=='mul' and (body[1]==point or body[2]==point)
            found.append(dict(path=path+[3], kind='prime_bank' if is_prime else 'mobius_bank' if is_mu else 'integer_bank',
                              tree=deepcopy(tree[3]), lower=deepcopy(tree[2]),
                              scope='admitted nonzero-coefficient indices; further state cancellation unknown' if is_mu
                                  else 'admitted index domain; further state cancellation unknown'))
        if op == 'root' and tree[1] == variable('t'):
            found.append(dict(path=path, kind='t_root_range', tree=deepcopy(tree),
                              scope='raw selector range; does not assert a change of a surrounding mask or state'))
        elif op=='root':
            other_roots.append(dict(path=path,kind='scale_root_range' if tree[1]==variable('X') else 'nested_root_unknown',
                                    tree=deepcopy(tree),scope='raw argument map; effective state changes unclassified'))
        for index, child in enumerate(tree[1:], 1):
            if isinstance(child, list): walk(child, path+[index],tree)
    for i, state in enumerate(program['states']): walk(state['tree'], ['states', i, 'tree'])
    supported_paths=[item['path'] for item in found if item['kind']!='t_root_range']
    for item in other_roots:
        if not any(item['path'][:len(path)]==path for path in supported_paths): found.append(item)
    # Full descriptor equality, no digest or sampled-response aliases.
    unique = []
    for item in found:
        if not any(item['kind']==old['kind'] and item['tree']==old['tree'] and
                   item.get('lower')==old.get('lower') for old in unique):
            unique.append(item)
    return unique


def selector_value(descriptor, X, meter):
    kind = descriptor['kind']; tree = descriptor['tree']
    if kind=='nested_root_unknown': raise ValueError('unsupported nested root exposure')
    if kind == 't_root_range':
        return [_index(tree, {'X':X, 't':X}, meter), _index(tree, {'X':X, 't':2*X-1}, meter)]
    top = _index(tree, {'X':X}, meter)
    if kind == 'coprime_radical': return _radical(top, meter)
    if kind in ('prime_bank', 'mobius_bank', 'integer_bank'):
        lo = _index(descriptor['lower'], {'X':X}, meter)
        if top-lo > 4096: raise SelectorDomainCap('bounded selector domain')
        values = []
        for n in range(lo, top+1):
            meter.charge()
            if kind=='integer_bank' or (kind=='prime_bank' and _prime(n,meter)) or (kind=='mobius_bank' and _squarefree(n,meter)):
                values.append(n)
        return values
    return top


def exposure_plan(program, meter):
    descriptions = selectors(program, meter)
    contexts = sorted(set(TRAIN+VALIDATION) | {2*x for x in TRAIN+VALIDATION})
    rows, nominations = [], []
    for descriptor in descriptions:
        meter.charge()
        row = dict(descriptor=descriptor, contexts=[], next_transition=None, transition_value=None, next_transition_status='unknown')
        try:
            row['contexts'] = [dict(X=x, value=selector_value(descriptor,x,meter)) for x in contexts]
            if descriptor['kind'] in ('t_root_range','scale_root_range'):
                # Raw root intervals are exposure only; no false effective activation claim.
                row['next_transition_status']='raw_range_only'
            else:
                last = selector_value(descriptor, max(contexts), meter)
                transition = None
                for x in range(max(contexts)+1, 2*DISCOVERY_MAX+1):
                    meter.charge()
                    if selector_value(descriptor,x,meter) != last:
                        transition = x; break
                row['next_transition'] = transition
                if transition: row['transition_value']=selector_value(descriptor,transition,meter)
                row['next_transition_status'] = 'planned' if transition else 'unexposed_beyond_discovery_cap'
                if transition:
                    # Child scale first enters the new domain at ceil(transition/2).
                    boundary = (transition+1)//2
                    nominations.extend(x for x in (boundary-1,boundary) if x>=1 and x<=DISCOVERY_MAX)
        except SelectorDomainCap:
            row['next_transition_status']='unexposed_selector_domain_cap'
        except (KeyError, ValueError, ZeroDivisionError):
            row['next_transition_status']='unsupported_selector'
        rows.append(row)
    diagnostics = sorted(set(nominations)-set(TRAIN)-set(VALIDATION))[:2]
    for row in rows:
        row['diagnostic_contexts'] = []
        try:
            for x in sorted(set(diagnostics) | {2*x for x in diagnostics}):
                row['diagnostic_contexts'].append(dict(X=x,value=selector_value(row['descriptor'],x,meter)))
            if row['next_transition_status']=='planned' and not any(
                c['X']>=row['next_transition'] and c['value']==row['transition_value'] for c in row['diagnostic_contexts']):
                row['next_transition_status']='unexposed_diagnostic_quota_or_skipped_regime'
        except SelectorDomainCap:
            row['next_transition_status']='unexposed_selector_domain_cap'
        except (KeyError, ValueError, ZeroDivisionError):
            row['next_transition_status']='unsupported_selector'
    return dict(base_training=list(TRAIN),base_validation=list(VALIDATION),
                diagnostic_scales=diagnostics,selectors=rows,response_values_used=False,
                scope='finite source-free selector coverage; no signed estimate or extrapolation')


def record(identifier, generation, family, tree, origin, meter):
    program = dict(states=[]) if tree is None else state_program(tree)
    meter.charge(complexity(program)+1)
    return dict(id=identifier, generation=generation, family=family, program=program,
                complexity=complexity(program), origin=origin,
                semantics=S.analyze(program,meter), exposure=exposure_plan(program,meter))


def generate_initial(meter):
    t, X = variable('t'), variable('X'); base=prefix(t)
    pool={family:[] for family in FAMILIES}
    def put(family, tree, **origin): pool[family].append((tree,origin))
    for d in (2,3): put('calibration',prefix(floor_div(t,integer(d))),kind='lag',divisor=d)
    for q in (2,3,6): put('calibration',prefix(root(t,q)),kind='standalone_root',order=q)
    for q in (2,6): put('calibration',product(['x',root(t,q)],prefix(floor_div(t,integer(2)))),kind='whole_state_norm_mask',order=q)
    put('calibration',base,kind='target_copy')
    for q in (2,3,6):
        for d in (2,3):
            sign=-1 if d==2 else 1
            put('source_mixture',add(base,scale(sign,product(['x',root(t,q)],prefix(floor_div(t,integer(d)))))),
                kind='point_factor_in_summand',order=q,divisor=d,sign=sign)
    put('source_mixture',add(base,scale(-1,product(['x',t],prefix(floor_div(t,integer(2)))))),kind='output_factor_in_summand')
    put('source_mixture',add(prefix(floor_div(t,integer(2))),product(['x',root(t,3)],prefix(floor_div(t,integer(3))))),kind='two_lag_signed_coupling')
    d=variable('d'); quotient=floor_div(t,d); small=prefix(quotient)
    for q in (2,3,6):
        body=product(['x',d],add(small,scale(-1,product(['x',quotient],prefix(root(quotient,2))))))
        put('factor_bank',['sum','d',integer(1),root(X,q),body],kind='factor_internal_point_mix',order=q)
        body=product(['x',d],add(base,scale(-1,small)))
        put('factor_bank',['sum','d',integer(1),root(X,q),body],kind='factor_difference_bank',order=q)
    body=product(['x',d],['guard',['eq',['gcd',d,t],integer(1)],small])
    put('factor_bank',['sum','d',integer(1),root(X,3),body],kind='coprime_factor_bank',order=3)
    body=product(['x',d],add(product(['x',t],small),scale(-1,product(['x',quotient],prefix(root(quotient,3))))))
    put('factor_bank',['sum','d',integer(1),root(X,3),body],kind='factor_two_point_mix',order=3)
    p=variable('p'); quotient=floor_div(t,p); small=prefix(quotient)
    def prime_sum(q,body): return ['sum','p',integer(2),root(X,q),['guard',['prime',p],body]]
    for q in (2,3,6):
        body=add(small,scale(-1,product(['x',quotient],prefix(root(quotient,2)))))
        put('prime_bank',prime_sum(q,body),kind='prime_internal_point_mix',order=q)
        body=add(product(['x',quotient],prefix(floor_div(t,integer(2)))),scale(-1,product(['x',t],small)))
        put('prime_bank',prime_sum(q,body),kind='prime_two_point_mix',order=q)
    put('prime_bank',prime_sum(3,add(small,scale(-1,prefix(root(t,3))))),kind='prime_root_difference',order=3)
    body=['guard',['eq',['gcd',t,p],integer(1)],add(product(['x',quotient],small),prefix(root(t,6)))]
    put('prime_bank',prime_sum(3,body),kind='coprime_prime_point_mix',order=3)
    previous=['max',integer(0),['isub',t,integer(1)]]
    for q in (2,3,6):
        a=product(['x',root(t,q)],add(base,scale(-1,prefix(floor_div(t,integer(2))))))
        b=product(['x',root(['max',integer(1),previous],q)],add(prefix(previous),scale(-1,prefix(floor_div(previous,integer(2))))))
        put('index_switch',add(a,scale(-1,b)),kind='point_weighted_difference',order=q)
        shifted=['max',integer(0),['isub',t,root(X,q)]]
        a=product(base,prefix(root(t,q)))
        b=product(prefix(shifted),prefix(root(shifted,q)))
        put('index_switch',add(a,scale(-1,b)),kind='bilinear_moving_difference',order=q)
    body=product(['x',d],['guard',['divides',d,t],prefix(floor_div(t,d))])
    put('index_switch',['sum','d',integer(1),root(X,2),body],kind='divisor_output_bank',order=2)
    g=['gcd',t,d]; quotient=floor_div(t,d)
    body=product(['x',d],add(product(['x',quotient],prefix(g)),scale(-1,product(['x',g],prefix(quotient)))))
    put('index_switch',['sum','d',integer(1),root(X,3),body],kind='gcd_quotient_commutator',order=3)
    records=[record(0,0,'baseline',None,dict(kind='unmodified_target_control'),meter)]
    attempts=[]; seen=[records[0]['program']]
    for family in FAMILIES:
        for tree,origin in pool[family]:
            program=state_program(tree); meter.charge(node_count(tree)+1)
            reason='duplicate_syntax' if program in seen else 'node_cap' if complexity(program)>256 else None
            attempts.append(dict(family=family,origin=origin,program=program,status='rejected' if reason else 'generated',reason=reason))
            if reason: continue
            seen.append(program); records.append(record(len(records),0,family,tree,origin,meter))
    return dict(records=records,attempts=attempts,response_values_used=False)


def _factor_first_sum(tree, factor):
    if tree[0]=='add': return add(tree[1],product(factor,tree[2])),True
    result=deepcopy(tree)
    for index,child in enumerate(tree[1:],1):
        if isinstance(child,list):
            changed,found=_factor_first_sum(child,factor)
            if found:
                result[index]=changed; return result,True
    return result,False


def generate_mutations(parents, initial, meter):
    t,X=variable('t'),variable('X'); records=[]; attempts=[]
    seen=[r['program'] for r in initial]
    transforms=('factor_in_summand','signed_pair','gcd_conditioned_mix','quotient_commutator')
    for k,transform in enumerate(transforms):
        accepted=0
        for offset in range(len(parents)):
            position=(offset+k)%len(parents); parent=parents[position]
            tree=parent['program']['states'][0]['tree']; origin=dict(kind=transform,parent=parent['id'])
            if transform=='factor_in_summand':
                candidate,found=_factor_first_sum(tree,['x',root(t,3)])
                if not found: candidate=add(tree,product(['x',root(t,3)],prefix(floor_div(t,integer(3)))))
                origin['existing_sum_rewritten']=found
            elif transform=='signed_pair':
                other=parents[(position+1)%len(parents)]
                candidate=add(tree,scale(-1,product(['x',root(t,6)],other['program']['states'][0]['tree'])))
                origin['other_parent']=other['id']
            elif transform=='gcd_conditioned_mix':
                mask=['eq',['gcd',t,['max',integer(2),root(X,3)]],integer(1)]
                candidate=add(tree,scale(-1,['guard',mask,prefix(floor_div(t,integer(2)))]))
            else:
                half=floor_div(t,integer(2)); a=product(['x',t],remap(tree,half))
                b=product(['x',['max',integer(1),half]],tree); candidate=add(a,scale(-1,b))
            program=state_program(candidate); meter.charge(node_count(candidate)+1)
            reason='duplicate_syntax' if program in seen else 'node_cap' if complexity(program)>256 else 'mutation_quota' if accepted>=6 else None
            attempts.append(dict(origin=origin,program=program,status='rejected' if reason else 'generated',reason=reason))
            if reason: continue
            seen.append(program); accepted+=1
            records.append(record(len(initial)+len(records),1,parent['family'],candidate,origin,meter))
    return dict(records=records,attempts=attempts,response_values_used=True)


def _slot(mechanism):
    if mechanism in CALIBRATION: return 'calibration'
    if mechanism in ('unknown','multi_state'): return 'exploration'
    return mechanism


def selection_mechanism(record):
    annotation=record['semantics']; mechanism=annotation['mechanism']
    if mechanism=='mask' and len(annotation['states'])==1:
        core=annotation['states'][0]['core_mechanism']
        if core in ('coupled_sum','coupled_bank','nonlinear'): return core
    return mechanism


def choose(records,evidence,meter,limit=8):
    by_id={r['id']:r for r in records}; ranked=[]
    for e in evidence:
        meter.charge(12)
        if e.get('status')!='available' or e['id']==0: continue
        r=by_id[e['id']]; costs=anchored_cost(e['initial'],e['constants'],max(VALIDATION),meter)
        key=(sum(not s['passed'] for s in e['validation_scores']),
             tuple(Q(costs[str(q)]) for q in reversed(LEVELS)),Q(e['initial']['W']),r['complexity'],r['id'])
        ranked.append((key,r))
    ranked.sort(key=lambda pair:pair[0]); chosen=[]
    def available(r): return all(r['id']!=c['id'] for c in chosen)
    def count(group): return sum(_slot(selection_mechanism(r))==group for r in chosen)
    for group in SLOTS:
        candidate=next((r for _,r in ranked if _slot(selection_mechanism(r))==group),None)
        if candidate is not None and len(chosen)<limit: chosen.append(candidate)
    for distinct in (True,False):
        for _,r in ranked:
            if len(chosen)>=limit: break
            group=_slot(selection_mechanism(r)); pair=(selection_mechanism(r),r['family'])
            if not available(r) or count(group)>=(2 if group=='calibration' else 3): continue
            if distinct and any((selection_mechanism(c),c['family'])==pair for c in chosen): continue
            chosen.append(r)
    for _,r in ranked:
        if len(chosen)>=limit: break
        if available(r) and _slot(selection_mechanism(r))!='calibration': chosen.append(r)
    return chosen


def obligation(record):
    result=base_obligation(record)
    result.update(semantics=record['semantics'],exposure=record['exposure'],
        analytic_tasks=[
            'Establish source and domain scoped identities for the complete signed state.',
            'Bound every retained mixed correlation with constants uniform in all moving parameters.',
            'Control added and removed child selector domains, complements and W(1).',
            'Show how the estimate is proved without assuming the target subpower energy bound.'
        ])
    return result
