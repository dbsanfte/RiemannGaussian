"""Source-generated global Dirichlet inverse/floor-prefix constraints.

These exact arithmetic relations supply constraints, not a prefix bound.
Weights are retained without division, including zero and parameter weights.
"""
from copy import deepcopy
from fractions import Fraction as Q
import time


class Meter:
    def __init__(self,cap=1_000_000,seconds=60,cells=2_000_000):
        self.cap=cap;self.operations=0;self.peak_cells=0;self.cells=cells
        self.started=time.monotonic();self.deadline=self.started+seconds
    def charge(self,n=1):
        if type(n) is not int or n<0:raise ValueError('nonnegative work')
        self.operations+=n
        if self.operations>self.cap:raise OverflowError('arithmetic relation work cap')
        if time.monotonic()>self.deadline:raise TimeoutError('arithmetic relation deadline')
    def live(self,n):
        self.charge();self.peak_cells=max(self.peak_cells,n)
        if n>self.cells:raise MemoryError('arithmetic relation cell cap')
    def counts(self):
        return dict(operations=self.operations,peak_cells=self.peak_cells,elapsed_seconds=time.monotonic()-self.started)


def _integer(value,meter,positive=False):
    if type(value) is not int or (positive and value<1) or value.bit_length()>4096:
        raise ValueError('strict4096bit integer')
    meter.charge(1+value.bit_length()//32)


def _rational(value,meter):
    if type(value) is not str or not 1<=len(value)<=2500:raise ValueError('canonical rational string')
    meter.charge(1+len(value))
    q=Q(value)
    if str(q)!=value or max(abs(q.numerator).bit_length(),q.denominator.bit_length())>4096:
        raise ValueError('canonical4096bit rational')
    return q


def validate_source(source,meter=None):
    meter=Meter() if meter is None else meter
    if type(source) is not dict or set(source)!={'lattice','channels'}:raise ValueError('exact source fields')
    _integer(source['lattice'],meter,True)
    channels=source['channels']
    if type(channels) is not list or not 1<=len(channels)<=64:raise ValueError('one..64 source channels')
    for channel in channels:
        meter.charge()
        if type(channel) is not dict or set(channel)!={'atoms','weight'}:raise ValueError('exact channel fields')
        atoms,weight=channel['atoms'],channel['weight']
        if type(atoms) is not list or len(atoms)>32:raise ValueError('at most32 source atoms; empty is delta')
        if type(weight) is not list or len(weight)!=2:raise ValueError('affine constant/R weight')
        for w in weight:_rational(w,meter)
        for atom in atoms:
            if type(atom) is not dict or set(atom)!={'kind','shift'} or atom['kind'] not in ('power','mu'):
                raise ValueError('exact power/mu atom')
            _integer(atom['shift'],meter)
    return True


def _powers(shifts,lattice):
    return dict(op='dirichlet_convolution',factors=[dict(op='power',exponent=str(Q(-s,lattice))) for s in shifts])


def generate(source,meter=None):
    meter=Meter() if meter is None else meter
    validate_source(source,meter)
    relations=[];lattice=source['lattice']
    for i,channel in enumerate(source['channels']):
        meter.charge(8+8*len(channel['atoms']))
        mu=sorted(a['shift'] for a in channel['atoms'] if a['kind']=='mu')
        powers=sorted(a['shift'] for a in channel['atoms'] if a['kind']=='power')
        relations.append(dict(channel=i,weight=channel['weight'][:],kernel=_powers(mu,lattice),rhs=_powers(powers,lattice),
            local_identity=dict(variable='t',basis='q=p^(-1/lattice)',
                left_numerator=mu,left_denominator=sorted(mu+powers),
                right_numerator=[],right_denominator=powers),
            prefix_identity='sum_d kernel(d)*W_channel(floor(N/d)) = weight*prefix(rhs)(N)',
            scope=dict(all_primes=True,all_valuations=True,all_integer_N=True,unit_retained=True)))
    meter.live(16+sum(32+12*len(c['atoms']) for c in source['channels']))
    return dict(schema='arithmetic-prefix-relations-v1',source_binding=deepcopy(source),relations=relations,
                uniform_bound_proved=False,RH_proved=False)


def _key(previous,k,e,meter):
    meter.charge(2+len(previous))
    values={a:Q(b) for a,b in previous}
    if k!=1:values[k]=values.get(k,Q(0))+e
    return tuple((a,str(b)) for a,b in sorted(values.items()) if b)


def _tables(exponents,N,meter):
    meter.charge(2*(N+1));meter.live(8*(N+1))
    table=[{} for _ in range(N+1)]
    if N>=1:table[1]={():1}
    entries=1
    for text in exponents:
        exponent=Q(text);meter.charge(N+1)
        next_table=[{} for _ in range(N+1)]
        new_entries=0
        for d in range(1,N+1):
            meter.charge()
            if not table[d]:continue
            for k in range(1,N//d+1):
                for previous,count in table[d].items():
                    key=_key(previous,k,exponent,meter)
                    target=next_table[d*k]
                    if key not in target:new_entries+=1
                    meter.live(8*(N+1)+40*(entries+new_entries))
                    target[key]=target.get(key,0)+count
        table=next_table;entries=new_entries
    return table


def _encode(terms,meter):
    meter.charge(1+sum(1+len(key) for key in terms))
    return dict(op='positive_power_sum',terms=[dict(coefficient=str(count),
        factors=[dict(argument=a,exponent=b) for a,b in key]) for key,count in sorted(terms.items()) if count])


def _same(a,b,meter):
    meter.charge()
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(_same(a[k],b[k],meter) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_same(x,y,meter) for x,y in zip(a,b))
    return a==b


def prefix_rows(certificate,N,meter=None):
    """Complete finite rows for symbolic channel prefixes at every floor N/d.

    Generalized-power monomials are exact expressions; no real powers are
    numerically evaluated. Budget failure prevents unbounded expansion.
    """
    meter=Meter() if meter is None else meter
    _integer(N,meter)
    if N<0:raise ValueError('N nonnegative')
    if type(certificate) is not dict or 'source_binding' not in certificate:raise ValueError('source-bound certificate')
    expected=generate(certificate['source_binding'],meter)
    # Producer self-check is supplemental; separate verifier performs replay.
    if not _same(certificate,expected,meter):raise ValueError('complete generated certificate')
    rows=[]
    for relation in certificate['relations']:
        kernel=_tables([f['exponent'] for f in relation['kernel']['factors']],N,meter)
        rhs=_tables([f['exponent'] for f in relation['rhs']['factors']],N,meter)
        total={}
        for n in range(1,N+1):
            for key,count in rhs[n].items():
                meter.charge();total[key]=total.get(key,0)+count
        lhs=[dict(kernel_argument=d,prefix_floor=N//d,coefficient=_encode(kernel[d],meter))
             for d in range(1,N+1) if kernel[d]]
        rows.append(dict(schema='arithmetic-floor-prefix-row-v1',N=N,channel=relation['channel'],
                         prefix_kind='weighted_channel',lhs=lhs,
                         rhs=dict(weight=relation['weight'][:],coefficient=_encode(total,meter))))
    return rows


generate_relations=generate
