"""Independent replay of source-generated all-valuation prefix constraints.

No producer import. Euler identities are checked as exact factor multisets;
finite coefficients are rebuilt by divisor-factorization recursion.
"""
from collections import Counter
from fractions import Fraction
import time


class Meter:
    def __init__(self,cap=1_000_000,seconds=60):
        self.operations=0;self.cap=cap;self.peak_cells=0;self.deadline=time.monotonic()+seconds
    def charge(self,n=1):
        self.operations+=n
        if self.operations>self.cap:raise OverflowError('relation replay work cap')
        if time.monotonic()>self.deadline:raise TimeoutError('relation replay deadline')
    def live(self,n):
        self.charge();self.peak_cells=max(self.peak_cells,n)
        if n>2_000_000:raise MemoryError('relation replay cell cap')


def _same(a,b,m):
    m.charge()
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(_same(a[k],b[k],m) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_same(x,y,m) for x,y in zip(a,b))
    return a==b


def _q(x,m):
    if type(x) is not str or not 1<=len(x)<=2500:raise ValueError('rational text')
    m.charge(1+len(x));r=Fraction(x)
    if str(r)!=x or max(abs(r.numerator).bit_length(),r.denominator.bit_length())>4096:raise ValueError('canonical rational')
    return r


def _source(source,m):
    if type(source) is not dict or set(source)!={'lattice','channels'}:raise ValueError('source fields')
    l=source['lattice']
    if type(l) is not int or l<1 or l.bit_length()>4096:raise ValueError('lattice')
    m.charge(1+l.bit_length()//32)
    channels=source['channels']
    if type(channels) is not list or not 1<=len(channels)<=64:raise ValueError('channel count')
    for c in channels:
        if type(c) is not dict or set(c)!={'weight','atoms'}:raise ValueError('channel fields')
        if type(c['weight']) is not list or len(c['weight'])!=2:raise ValueError('affine weight')
        for x in c['weight']:_q(x,m)
        if type(c['atoms']) is not list or len(c['atoms'])>32:raise ValueError('atom count')
        for a in c['atoms']:
            m.charge()
            if type(a) is not dict or set(a)!={'kind','shift'} or a['kind'] not in ('mu','power'):raise ValueError('atom fields')
            s=a['shift']
            if type(s) is not int or abs(s).bit_length()>4096:raise ValueError('shift integer')
            m.charge(1+abs(s).bit_length()//32)
    return channels,l


def _expected(source,m):
    channels,lattice=_source(source,m);relations=[]
    for i,c in enumerate(channels):
        numerator=Counter(a['shift'] for a in c['atoms'] if a['kind']=='mu')
        remaining=Counter(a['shift'] for a in c['atoms'] if a['kind']=='power')
        denominator=numerator+remaining
        # Exact rational factor cancellation; no finite jets are used.
        if denominator-numerator!=remaining:raise ValueError('Euler cancellation')
        inverse_shifts=sorted(numerator.elements());power_shifts=sorted(remaining.elements())
        def powers(shifts):
            return {'op':'dirichlet_convolution','factors':[{'op':'power','exponent':str(Fraction(-s,lattice))} for s in shifts]}
        relations.append(dict(channel=i,weight=c['weight'][:],kernel=powers(inverse_shifts),rhs=powers(power_shifts),
            local_identity=dict(variable='t',basis='q=p^(-1/lattice)',left_numerator=inverse_shifts,
                                left_denominator=sorted(denominator.elements()),right_numerator=[],right_denominator=power_shifts),
            prefix_identity='sum_d kernel(d)*W_channel(floor(N/d)) = weight*prefix(rhs)(N)',
            scope=dict(all_primes=True,all_valuations=True,all_integer_N=True,unit_retained=True)))
    return dict(schema='arithmetic-prefix-relations-v1',source_binding=source,relations=relations,
                uniform_bound_proved=False,RH_proved=False)


def verify_certificate(source,certificate,meter=None):
    m=Meter() if meter is None else meter
    if not _same(_expected(source,m),certificate,m):raise ValueError('source-generated relation mismatch')
    return True


def _coefficient(n,exponents,m):
    """Enumerate ordered integer factorizations, separately from producer DP."""
    if not exponents:return {():1} if n==1 else {}
    result={}
    m.charge(n)
    for d in range(1,n+1):
        if n%d:continue
        for old,count in _coefficient(n//d,exponents[1:],m).items():
            m.charge(3+len(old));values={a:Fraction(b) for a,b in old}
            if d>1:values[d]=values.get(d,Fraction(0))+exponents[0]
            key=tuple((a,str(b)) for a,b in sorted(values.items()) if b)
            result[key]=result.get(key,0)+count
            m.live(40*(1+len(result))+8*n)
    return result


def _encode(terms,m):
    m.charge(1+sum(1+len(k) for k in terms))
    return {'op':'positive_power_sum','terms':[{'coefficient':str(c),
        'factors':[{'argument':a,'exponent':b} for a,b in k]} for k,c in sorted(terms.items()) if c]}


def verify_prefix_row(source,certificate,row,meter=None):
    m=Meter() if meter is None else meter
    verify_certificate(source,certificate,m)
    if type(row) is not dict or type(row.get('N')) is not int or row['N']<0 or row['N'].bit_length()>4096:
        raise ValueError('nonnegative integer row horizon')
    N=row['N'];i=row.get('channel')
    if type(i) is not int or not 0<=i<len(source['channels']):raise ValueError('source channel')
    m.charge(N+1);m.live(8*(N+1))
    relation=_expected(source,m)['relations'][i]
    inverse=[Fraction(f['exponent']) for f in relation['kernel']['factors']]
    powers=[Fraction(f['exponent']) for f in relation['rhs']['factors']]
    lhs=[];total={}
    for d in range(1,N+1):
        coefficient=_coefficient(d,inverse,m)
        if coefficient:lhs.append(dict(kernel_argument=d,prefix_floor=N//d,coefficient=_encode(coefficient,m)))
        for k,c in _coefficient(d,powers,m).items():
            m.charge();total[k]=total.get(k,0)+c
    expected=dict(schema='arithmetic-floor-prefix-row-v1',N=N,channel=i,prefix_kind='weighted_channel',
                  lhs=lhs,rhs=dict(weight=relation['weight'][:],coefficient=_encode(total,m)))
    if not _same(expected,row,m):raise ValueError('complete floor-prefix row mismatch')
    return True
