"""Independent finite Walsh energy bound, conditional on SAME-parent 064 admission.
No scientific arrays or discovery producer are read or imported.
"""
from fractions import Fraction as Q
from math import gcd, isqrt
import check_mobius_mass_conservation_060 as BASE
Meter = BASE.Meter
MAX_MEMORY_BYTES = 512 * 1024 * 1024
MAX_ENTRIES = 250000
MAX_BITS = 32768
FIELDS = ('schema','N','y','H','K','conditioned_primes','endpoints','budget')
EFIELDS = ('ratio','weights','energy_terms','cycles','weight_mass','energy_l1','energy_upper','variation_bound')

class _Context:
    def __init__(self,m):
        self.m=m; self.storage=8192; self.entries=0; self.factors={}
    def entry(self,n=1):
        self.m.charge(n); self.entries+=n; self.storage+=512*n
        if self.entries>MAX_ENTRIES: raise OverflowError('energy entry capacity')
        if self.storage>MAX_MEMORY_BYTES: raise MemoryError('energy prospective storage cap')
    def bounded(self,v):
        b=max(abs(v.numerator).bit_length(),v.denominator.bit_length())
        self.m.charge(1+b)
        if b>MAX_BITS: raise OverflowError('energy rational intermediate capacity')
        self.storage+=(b+7)//8
        if self.storage>MAX_MEMORY_BYTES: raise MemoryError('energy prospective storage cap')
        return v
    def mul(self,a,b):
        self.m.charge(1+max(abs(a.numerator).bit_length(),a.denominator.bit_length())*max(abs(b.numerator).bit_length(),b.denominator.bit_length()))
        return self.bounded(a*b)
    def q(self,v):
        self.entry(); return BASE._rational(v,self.m)
    def factor(self,n):
        if n in self.factors:return self.factors[n]
        self.entry(); rest=n; fs=[]; d=2
        while d*d<=rest:
            self.m.charge(6)
            if rest%d==0:
                fs.append(d);rest//=d
                if rest%d==0:raise ValueError('squarefree monomial required')
            d+=1
        if rest>1:fs.append(rest)
        self.factors[n]=fs;return fs
    def product(self,a,b):
        self.m.charge(8+a.bit_length()*b.bit_length());g=gcd(a,b)
        value=(a//g)*(b//g)
        if value.bit_length()>MAX_BITS:raise OverflowError('energy character product bit capacity')
        return value

def _terms(items,c,bound,conditioned):
    if type(items) is not list or len(items)>MAX_ENTRIES:raise ValueError('bounded monomial list')
    result={};last=0
    for item in items:
        c.entry();BASE._fields(item,('index','coefficient'));i=item['index']
        if type(i) is not int or not last<i<=bound:raise ValueError('sorted distinct positive bounded indices')
        if any(p in conditioned for p in c.factor(i)):raise ValueError('conditioned prime remains in monomial')
        v=c.q(item['coefficient'])
        if not v:raise ValueError('nonzero terms required')
        result[i]=v;last=i
    return result

def verify_energy(parent,cert,meter=None):
    m=Meter() if meter is None else meter;c=_Context(m)
    BASE._fields(parent,FIELDS);BASE._fields(cert,FIELDS)
    BASE._expect(parent['schema'],'mobius-quadratic-contraction-v1')
    BASE._expect(cert['schema'],'mobius-walsh-energy-bound-v1')
    N,y,H,K=(parent[k] for k in ('N','y','H','K'))
    if type(N) is not int or not 2<=N<2**64 or type(y) is not int or not 1<=y<2**64:raise ValueError('finite positive scale/prefix')
    if type(H) is not int or not 1<=H<=4096 or type(K) is not int or not 0<=K<=65536 or K!=y//(H+1) or H*K>1000000:raise ValueError('finite parent horizons')
    for k in ('N','y','H','K','conditioned_primes'):BASE._expect(cert[k],parent[k])
    ps=parent['conditioned_primes']
    if type(ps) is not list or len(ps)>max(H,K):raise ValueError('bounded conditioned primes')
    for p in ps:
        if type(p) is not int or not 2<=p<=max(H,K):raise ValueError('conditioned radius')
        BASE._prime(p,m);c.entry()
    if ps!=sorted(set(ps)):raise ValueError('canonical prime list')
    conditioned=set(ps);bound=max(H,H*K)
    for obj in (parent,cert):
        if type(obj['endpoints']) is not list or len(obj['endpoints'])!=2:raise ValueError('both endpoints required')
    outputs=[];parent_costs=[];ratios=[]
    for e,(pe,ce) in enumerate(zip(parent['endpoints'],cert['endpoints'])):
        BASE._fields(pe,('ratio','rows','l1'));BASE._fields(ce,EFIELDS)
        ratio=c.q(pe['ratio']);ratios.append(ratio)
        if (e==0 and not 0<ratio<=1) or (e==1 and ratio!=1) or c.q(ce['ratio'])!=ratio:raise ValueError('endpoint ratio mismatch')
        rows=pe['rows'];weights=ce['weights']
        if type(rows) is not list or len(rows)!=H or type(weights) is not list or len(weights)!=H:raise ValueError('complete rows and weights')
        energy={};cost=Q(0);mass=Q(0);plus=Q(0);minus=Q(0)
        for j,(row,wt) in enumerate(zip(rows,weights),1):
            c.entry();BASE._fields(row,('j','terms'))
            if type(row['j']) is not int or row['j']!=j:raise ValueError('ascending complete j rows')
            terms=_terms(row['terms'],c,bound,conditioned);w=c.q(wt)
            if (terms and w<=0) or (not terms and w!=0):raise ValueError('positive weights exactly on nonzero rows')
            mass=c.bounded(mass+w);pv=Q(0);mv=Q(0)
            ts=list(terms.items())
            for i,a in ts:
                cost=c.bounded(cost+abs(a));pv=c.bounded(pv+a);mv=c.bounded(mv+(-a if len(c.factor(i))%2 else a))
            plus=c.bounded(plus+abs(pv));minus=c.bounded(minus+abs(mv))
            for u,(i,a) in enumerate(ts):
                for v in range(u,len(ts)):
                    k,b=ts[v];key=c.product(i,k);value=c.mul(a,b)
                    if u!=v:value=c.mul(Q(2),value)
                    value=c.mul(value,c.bounded(1/w));c.entry()
                    energy[key]=c.bounded(energy.get(key,Q(0))+value)
        energy={i:a for i,a in energy.items() if a}
        if c.q(pe['l1'])!=cost:raise ValueError('parent L1 mismatch')
        parent_costs.append(cost)
        recorded=_terms(ce['energy_terms'],c,bound*bound,conditioned)
        if recorded!=energy:raise ValueError('exact complete coalesced energy coefficients')
        constant=energy.get(1,Q(0))
        if constant<0:raise ArithmeticError('SOS constant nonnegative')
        l1=constant
        for i,a in energy.items():
            if i!=1:l1=c.bounded(l1+abs(a))
        cycles=ce['cycles']
        if type(cycles) is not list or len(cycles)>MAX_ENTRIES:raise ValueError('bounded cycle list')
        consumed={};cycle_mass=Q(0)
        for cycle in cycles:
            c.entry();BASE._fields(cycle,('indices','mass'));indices=cycle['indices'];cm=c.q(cycle['mass'])
            if type(indices) is not list or not 3<=len(indices)<=len(energy) or cm<=0:raise ValueError('positive mass and at least three cycle terms')
            last=1;key=1;sign=1
            for i in indices:
                c.entry()
                if type(i) is not int or not last<i or i not in energy:raise ValueError('distinct ascending existing nonconstant cycle indices')
                key=c.product(key,i);sign*=1 if energy[i]>0 else -1;last=i
                consumed[i]=c.bounded(consumed.get(i,Q(0))+cm)
                if consumed[i]>abs(energy[i]):raise ValueError('cycle capacity overconsumption')
            if key!=1 or sign!=-1:raise ValueError('negative frustrated character cycle')
            cycle_mass=c.bounded(cycle_mass+cm)
        penalty=c.mul(Q(2),cycle_mass);upper=c.bounded(l1-penalty);vb=c.q(ce['variation_bound'])
        if upper<0 or vb<0 or c.mul(vb,vb)<c.mul(mass,upper):raise ValueError('nonnegative upper and weighted Cauchy direction')
        for field,expected in (('weight_mass',mass),('energy_l1',l1),('energy_upper',upper)):
            if c.q(ce[field])!=expected:raise ValueError('exact energy aggregate '+field)
        if not mass and (energy or l1 or upper or vb):raise ValueError('all zero rows require zero bound')
        outputs.append(dict(weight_mass=str(mass),energy_l1=str(l1),energy_upper=str(upper),variation_bound=str(vb),cycle_count=len(cycles),cycle_penalty=str(penalty),all_free_plus_l1=str(plus),all_free_minus_l1=str(minus)))
    if c.q(parent['budget'])!=max(parent_costs):raise ValueError('parent budget mismatch')
    budget=max(Q(o['variation_bound']) for o in outputs)
    if c.q(cert['budget'])!=budget:raise ValueError('maximum endpoint variation budget')
    return dict(verified=True,schema='verified-mobius-walsh-energy-bound-v1',N=N,y=y,H=H,K=K,conditioned_primes=ps,endpoint_ratios=list(map(str,ratios)),endpoints=outputs,budget=str(budget),prospective_peak_storage_bytes=c.storage,finite_variation_bound_proved=True,endpoint_convexity_proved=True,energy_affine_in_ratio_required=False,bound_domain='every remaining prime sign assignment and every real ratio between the parent endpoints at fixed N,y,H,K',source_binding_condition='064 source admission and verify_contraction must independently admit the SAME supplied parent with its linked lift and repair',independent_parent_064_admission_required=True,original_source_binding_proved=False,uniform_N_growth_proved=False,whole_signed_target_bound_proved=False,RH_proved=False,scientific_source_or_LP_evaluated=False)
