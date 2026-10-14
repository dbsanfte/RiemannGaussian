"""Cost-bounded exact search over prime-adjunction stencils.

The source laws are supplied. The stencils and their cancellation orders are
enumerated without nominated winners or numerical fitting. A small transformed
correlation is distinct from domination/recovery of the original signed energy.
"""
from fractions import Fraction as Q
from itertools import combinations,product
from math import gcd
import time

PAIRS=tuple(product(range(3),repeat=2))
SOURCE_LABELS=['B=a_u*a_v','a_u','a_v']
REVIEW='ORDERED_PRIME_PAIRING_REVIEW_001.txt'


class Meter:
    def __init__(self,cap=150000000,seconds=1800):
        self.operations=0;self.cap=cap;self.deadline=time.monotonic()+seconds;self.peak_cells=0
    def charge(self,n=1):
        if type(n) is not int or n<0:raise ValueError('integer nonnegative work')
        if self.operations+n>self.cap:raise OverflowError('prime-slide work cap')
        self.operations+=n
        if time.monotonic()>self.deadline:raise TimeoutError('prime-slide runtime cap')
    def live(self,cells):
        if type(cells) is not int or cells<0:raise ValueError('nonnegative scalar-cell count')
        self.charge();self.peak_cells=max(self.peak_cells,cells)
        if cells>12000000:raise MemoryError('twelve-million symbolic scalar-cell cap')
    def counts(self):return dict(operations=self.operations,peak_cells=self.peak_cells)


def add(a,b,meter,scale=1):
    out=dict(a)
    for e,c in b.items():out[e]=out.get(e,0)+scale*c;meter.charge(2)
    return {e:c for e,c in out.items() if c}


def multiply(a,b,meter):
    out={}
    for i,c in a.items():
        for j,d in b.items():
            e=tuple(x+y for x,y in zip(i,j));out[e]=out.get(e,0)+c*d;meter.charge(4)
    return {e:c for e,c in out.items() if c}


def serial(poly):return [[list(e),c] for e,c in sorted(poly.items()) if c]


def validate(program):
    if type(program) is not dict or set(program)!={'binding','terms'}:raise ValueError('exact program schema')
    binding=program['binding']
    if type(binding) is not str:raise ValueError('typed prime binding')
    arity={'same_prime':1,'distinct_primes':2}.get(binding)
    if arity is None or type(program['terms']) is not list or not 1<=len(program['terms'])<=256:raise ValueError('nonempty bounded typed stencil')
    seen=set()
    for term in program['terms']:
        if type(term) is not dict or set(term)!={'coefficient','left','right'}:raise ValueError('term schema')
        if type(term['coefficient']) is not int or not 0<abs(term['coefficient'])<=2:raise ValueError('bounded integer coefficient')
        for side in ('left','right'):
            if (type(term[side]) is not list or len(term[side])!=arity or
                any(type(e) is not int or not 0<=e<=6 for e in term[side])):raise ValueError('bounded exponent vectors')
        if sum(term['left'])+sum(term['right'])>6:raise ValueError('bounded total prime power')
        key=tuple(term['left']+term['right'])
        if key in seen:raise ValueError('coalesced action terms')
        seen.add(key)
    return binding,arity


class Engine:
    def __init__(self,meter):
        self.meter=meter;self.cache={};one={(0,):1};self.locals=[]
        # Rational generating series. B has numerator(1-z)^2 and denominator
        # (1-t*z)(1-t^2*z); the other two have numerator1-z.
        for denominator,numerator in (
            ([{(1,):1,(2,):1},{(3,):-1}],[1,-2,1]),
            ([{(1,):1}],[1,-1]),([{(2,):1}],[1,-1])):
            rows=[one]
            for n in range(1,7):
                row={(0,):numerator[n]} if n<len(numerator) and numerator[n] else {}
                for shift,coefficient in enumerate(denominator,1):
                    if n>=shift:row=add(row,multiply(coefficient,rows[n-shift],meter),meter)
                rows.append(row)
            self.locals.append(rows)

    def column(self,binding,left,right):
        key=(binding,tuple(left),tuple(right))
        if key in self.cache:self.meter.charge();return self.cache[key]
        arity=len(left);columns=[]
        for i,j in PAIRS:
            row={(0,)*arity:1}
            for variable in range(arity):
                for source,power in ((i,left[variable]),(j,right[variable])):
                    factor={tuple(e[0] if k==variable else 0 for k in range(arity)):c
                            for e,c in self.locals[source][power].items()}
                    row=multiply(row,factor,self.meter)
            columns.append(row)
        self.cache[key]=columns;return columns

    def facts(self,program):
        binding,arity=validate(program);rows=[{} for _ in PAIRS]
        for term in program['terms']:
            columns=self.column(binding,term['left'],term['right'])
            rows=[add(a,b,self.meter,term['coefficient']) for a,b in zip(rows,columns)]
        valuations=[[min(e[k] for e in row) for k in range(arity)] if row else None for row in rows]
        nonzero=[v for v in valuations if v is not None]
        common=[min(v[k] for v in nonzero) for k in range(arity)] if nonzero else None
        l1=[sum(abs(c) for c in row.values()) for row in rows];self.meter.charge(sum(map(len,rows))+9*arity)
        return dict(multipliers=[serial(row) for row in rows],component_valuations=valuations,
                    component_l1=l1,common_valuations=common,free_prime_count=arity,binding=binding,
                    whole_signed_bound_proved=False)


def actions_same(maximum):
    return [(e,f) for total in range(maximum+1) for e in range(total+1) for f in [total-e]]


def normalized_coefficients(size):
    for row in product((-2,-1,1,2),repeat=size):
        if row[0]<0 or gcd(*row)!=1:continue
        yield row


def make_same(actions,coefficients):
    return dict(binding='same_prime',terms=[dict(coefficient=c,left=[e],right=[f]) for (e,f),c in zip(actions,coefficients)])


def programmes():
    """Frozen finite grammar: sparse stencils, rectangles, two-label transfers."""
    actions=actions_same(4)
    for size in (1,2,3):
        for chosen in combinations(actions,size):
            for coefficients in normalized_coefficients(size):
                yield 'same_prime_sparse',make_same(chosen,coefficients)
    for a in range(7):
        for b in range(a,7):
            for c in range(7-b):
                for d in range(c,7-b):
                    rectangle=[(e,f) for e in range(a,b+1) for f in range(c,d+1)]
                    rectangle.sort(key=lambda pair:(sum(pair),pair[0],pair[1]))
                    yield 'same_prime_rectangles',make_same(rectangle,[1]*len(rectangle))
    actions=[([1,1],[0,0]),([1,0],[0,1]),([0,1],[1,0]),([0,0],[1,1])]
    for size in range(1,5):
        for chosen in combinations(actions,size):
            for coefficients in normalized_coefficients(size):
                yield 'distinct_prime_sparse',dict(binding='distinct_primes',terms=[
                    dict(coefficient=c,left=list(left),right=list(right)) for (left,right),c in zip(chosen,coefficients)])


def support_bound(binding,weights,theta_text,meter):
    arity={'same_prime':1,'distinct_primes':2}.get(binding)
    if arity is None or len(weights)!=arity:raise ValueError('all independently bound prime weights required')
    theta=Q(theta_text);bs=[Q(b) for b in weights]
    if str(theta)!=theta_text or not Q(1,2)<=theta<1 or any(b<=0 for b in bs):raise ValueError('strictly positive tail weights')
    power=1-theta*sum(bs);meter.charge(12+8*arity)
    return dict(geometry='smooth_bank' if arity==1 else 'bank_bank',binding=binding,
                weights=[str(b) for b in bs],theta=theta_text,energy_power=str(power),
                prime_count=arity,independent_labels=['q'] if arity==1 else ['q','r'],
                index_support='h<=n,k<=n/q' if arity==1 else 'h<=n/q,k<=n/r',
                distinct_and_coprime_domain_required=True,
                logs_retained=True,cofinal_auxiliary=power<=0,
                constant_template='2^max(2-theta*sum(b),0)*product(1+1/b_j)*C',
                logarithmic_factor='(1+log(2X))^2',
                premises='full declared kernel; every tensor coefficient bounded by C*d_2(h)*d_2(k)',
                original_target_recovered=False,whole_signed_bound_proved=False,
                analytic_provenance=REVIEW)


def record(identity,family,program,engine):
    facts=engine.facts(program);common=facts['common_valuations']
    weights=[str(Q(v,3)) for v in common] if common is not None else None
    bound=None
    tensor=[2,-1,-1,-2,1,1,-2,1,1] if program['binding']=='same_prime' else [4,-2,-2,-2,1,1,-2,1,1]
    kernel_C=Q(81,4)*sum(abs(a)*b for a,b in zip(tensor,facts['component_l1']));engine.meter.charge(20)
    if weights and all(Q(w)>0 for w in weights):
        bound=support_bound(program['binding'],weights,'3/4',engine.meter)
        bound['C']=str(kernel_C)
    baseline=sum(t['coefficient'] for t in program['terms'] if not any(t['left']+t['right']))
    return dict(id=identity,family=family,program=program,
                multipliers=facts['multipliers'],
                common_valuations=common,component_valuations=facts['component_valuations'],
                component_l1=facts['component_l1'],prime_weights=weights,bound=bound,
                baseline_coefficient=baseline,term_count=len(program['terms']),
                coefficient_l1=sum(abs(t['coefficient']) for t in program['terms']),
                tensor_coefficients=tensor,kernel_polynomial_constant=str(kernel_C),
                exact_zero_all_components=common is None,
                auxiliary_cofinal_bound_proved=bool(bound and bound['cofinal_auxiliary']),
                algebraic_identity_verified=True,original_target_recovered=False,
                recovery_obligations=[dict(term=t,obligation='bound/cancel complete lifted support and inverse-image complements')
                    for t in program['terms'] if any(t['left']+t['right'])] if baseline else [],
                whole_signed_bound_proved=False)


def selected(records):
    """Keep coverage and complete recovery distinct from large component gains."""
    chosen=[]
    for family in ('same_prime_sparse','same_prime_rectangles','distinct_prime_sparse'):
        lane=[r for r in records if r['family']==family and not r['exact_zero_all_components']]
        for recover in (True,False):
            pool=[r for r in lane if bool(r['baseline_coefficient'])==recover]
            if not pool:continue
            chosen.append(min(pool,key=lambda r:(
                not (r['bound'] is not None and r['bound']['cofinal_auxiliary']),
                Q(r['bound']['energy_power']) if r['bound'] else Q(100),
                r['term_count'],r['coefficient_l1'],r['id']))['id'])
    # A mixed channel can suggest a new auxiliary even when the common channel
    # has no positive weight. Its universal scope remains component-only.
    for binding in ('same_prime','distinct_primes'):
        pool=[r for r in records if r['program']['binding']==binding and r['component_valuations'][5] is not None]
        if pool:chosen.append(min(pool,key=lambda r:(
            -sum(r['component_valuations'][5]),r['term_count'],r['coefficient_l1'],r['id']))['id'])
    return list(dict.fromkeys(chosen))
