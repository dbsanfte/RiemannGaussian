#!/usr/bin/env python3
"""Streamed exact Proposition 3.4 contraction over rational truncated jets.
No layout construction, full truth tables, fibre lists, or factoring oracle.
Zero-based variables/groups/factors; interpolation nodes are 1,...,Q.
"""
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import combinations
from math import comb
from typing import Callable


@dataclass(frozen=True)
class Factor:
    scope: tuple
    entry: Callable


@dataclass
class Stats:
    counts: dict = field(default_factory=dict)
    numerator_bits: int = 0
    denominator_bits: int = 0

    def inc(self,key,amount=1):self.counts[key]=self.counts.get(key,0)+amount
    def note(self,value):
        value=Fraction(value)
        self.numerator_bits=max(self.numerator_bits,abs(value.numerator).bit_length())
        self.denominator_bits=max(self.denominator_bits,value.denominator.bit_length())
        return value
    def output(self):
        return dict(self.counts,maximum_recorded_numerator_bits=self.numerator_bits,
                    maximum_recorded_denominator_bits=self.denominator_bits)


class Jets:
    def __init__(self,precision,stats):self.J=precision;self.stats=stats
    def const(self,value):return (self.stats.note(value),)+(Fraction(0),)*(self.J-1)
    def add(self,a,b):
        self.stats.inc('jet_additions')
        return tuple(self.stats.note(x+y) for x,y in zip(a,b))
    def scale(self,a,value):
        value=Fraction(value);self.stats.inc('jet_scalings')
        return tuple(self.stats.note(x*value) for x in a)
    def mul(self,a,b):
        self.stats.inc('jet_multiplications');out=[Fraction(0)]*self.J
        for i,x in enumerate(a):
            if not x:continue
            for j in range(self.J-i):
                if b[j]:out[i+j]=self.stats.note(out[i+j]+x*b[j])
        return tuple(out)
    def inverse(self,a):
        if not a[0]:raise ZeroDivisionError('jet constant must be a known nonzero rational')
        self.stats.inc('jet_unit_inversions');out=[self.stats.note(1/a[0])]
        for k in range(1,self.J):
            out.append(self.stats.note(-out[0]*sum(a[i]*out[k-i] for i in range(1,k+1))))
        return tuple(out)


@dataclass
class ExplicitDesign:
    n: int
    r: int
    Q: int
    R: int
    D: int
    partitions: dict
    sigma: dict
    measurements: dict
    forms: dict
    tau: Fraction = Fraction(1,2)

    def groups(self,t):return self.partitions[t]
    def factor_group(self,t,f):return self.sigma[t][f]
    def measurement_rows(self,t,g):return self.measurements[t][g]
    def form(self,f,v):return self.forms[f,v]


@dataclass(frozen=True)
class CounterResult:
    value: object
    stats: dict
    method: str = 'proposition_3_4_streamed_exact'
    def as_dict(self):
        value=Fraction(self.value)
        return dict(method=self.method,value_numerator=value.numerator,
                    value_denominator=value.denominator,stats=self.stats)


def boolean_vectors(length):
    for mask in range(1<<length):yield tuple((mask>>i)&1 for i in range(length))


def measurement_vectors(length,D,bounds=None):
    """Mixed-radix stream with O(length*log(D+2)) retained bits."""
    if not length:
        yield ();return
    radii=[D]*length if bounds is None else list(bounds)
    if len(radii)!=length or any(not 0<=radius<=D for radius in radii):
        raise ValueError("invalid measurement radii")
    current=[-radius for radius in radii]
    while True:
        yield tuple(current)
        pos=0
        while pos<length and current[pos]==radii[pos]:current[pos]=-radii[pos];pos+=1
        if pos==length:return
        current[pos]+=1


def _poly_value(coefficients,t):
    out=Fraction(0)
    for coefficient in reversed(coefficients):out=out*t+Fraction(coefficient)
    return out


def _row_basis(rows,width):
    basis=[]
    for original in rows:
        row=[Fraction(x) for x in original]
        for pivot,b in basis:
            c=row[pivot]
            if c:row=[x-c*y for x,y in zip(row,b)]
        pivot=next((i for i,x in enumerate(row) if x),None)
        if pivot is not None:
            c=row[pivot];row=[x/c for x in row]
            basis.append((pivot,row))
            basis.sort(key=lambda item:item[0])
    return basis


def _in_span(vector,basis):
    row=list(map(Fraction,vector))
    for pivot,b in basis:
        c=row[pivot]
        if c:row=[x-c*y for x,y in zip(row,b)]
    return not any(row)


def validate(n,factors,layout,require_quantitative=False):
    """Exact polynomial-time design check; no tensor truth-table enumeration.
    Restoration, degree, row ranges, and kernel conditions are mandatory.
    Balance/summary-count promises affect cost only and are reported separately.
    """
    if not isinstance(n,int) or n<0:raise ValueError('n must be a nonnegative integer')
    if any(not isinstance(getattr(layout,key),int) for key in ('n','r','Q','R','D')):
        raise ValueError('design dimensions must be integers')
    if layout.n!=n or layout.r<2 or not 1<=layout.R<layout.Q or layout.D<1:
        raise ValueError('invalid design dimensions/parameters')
    for factor in factors:
        if not callable(factor.entry):raise ValueError('factor entry must be callable')
        if len(set(factor.scope))!=len(factor.scope) or any(not isinstance(v,int) or not 0<=v<n for v in factor.scope):
            raise ValueError('factor scopes must be sets of declared variables')
    for f,factor in enumerate(factors):
        for v in factor.scope:
            row=layout.form(f,v)
            if any(not isinstance(x,(int,Fraction)) for coefficients in row.values() for x in coefficients):
                raise ValueError('form coefficients must be exact integers or Fractions')
            if any(not isinstance(i,int) or not 0<=i<n for i in row):raise ValueError('form references undeclared variable')
            if any(any(Fraction(x) for x in coeffs[layout.R+1:]) for coeffs in row.values()):
                raise ValueError('replacement degree exceeds R')
            for i in range(n):
                coefficients=row.get(i,())
                if (Fraction(coefficients[0]) if coefficients else 0)!=(i==v):
                    raise ValueError('replacement fails restoration at T=0')
    balanced=True;summary_bound=hasattr(layout,'tau')
    for t in range(1,layout.Q+1):
        groups=layout.groups(t)
        if (len(groups)!=layout.r or any(not isinstance(v,int) or not 0<=v<n for group in groups for v in group)
                or sorted(v for group in groups for v in group)!=list(range(n))):
            raise ValueError('groups must partition declared variables')
        balanced &= all(len(group)*layout.r<=2*n for group in groups)
        bases=[];total_rows=0
        for g,group in enumerate(groups):
            rows=tuple(layout.measurement_rows(t,g));total_rows+=len(rows)
            if any(len(row)!=len(group) for row in rows):raise ValueError('measurement column mismatch')
            if any(any(not isinstance(x,int) for x in row) for row in rows):raise ValueError('measurements must be integral')
            if any(sum(abs(x) for x in row)>layout.D for row in rows):
                raise ValueError('measurement range exceeds D')
            bases.append(_row_basis(rows,len(group)))
        tau=getattr(layout,'tau',None)
        if tau is not None:
            summary_bound &= isinstance(tau,(int,Fraction)) and 0<Fraction(tau)<=Fraction(1,2)
            summary_bound &= total_rows<=2*Fraction(tau)*n
        for f,factor in enumerate(factors):
            assigned=layout.factor_group(t,f)
            if not isinstance(assigned,int) or not 0<=assigned<layout.r:raise ValueError('invalid factor group')
            for v in factor.scope:
                row=layout.form(f,v)
                for g,group in enumerate(groups):
                    if g==assigned:continue
                    vector=[_poly_value(row.get(i,()),t) for i in group]
                    if not _in_span(vector,bases[g]):
                        raise ValueError('kernel invariance fails')
    quantitative=balanced and summary_bound
    if require_quantitative and not quantitative:raise ValueError('quantitative design promises fail')
    return dict(algebraic_design_valid=True,balanced_groups=balanced,
                summary_count_bound=summary_bound,quantitative_promises_valid=quantitative)


def multilinear_extension(factor,inputs,ops,stats):
    """Exact nonlinear extension by a streamed Boolean-assignment/product sum."""
    if len(inputs)!=len(factor.scope):raise ValueError('factor input arity mismatch')
    complements=[ops.add(ops.const(1),ops.scale(x,-1)) for x in inputs]
    total=ops.const(0)
    for eta in boolean_vectors(len(factor.scope)):
        stats.inc('local_boolean_entry_evaluations')
        raw=factor.entry(eta)
        if not isinstance(raw,(int,Fraction)):raise TypeError('entry must return an exact integer or Fraction')
        value=Fraction(raw);stats.note(value)
        if value not in (0,1):stats.inc('non_boolean_entry_evaluations')
        if not value:continue
        term=ops.const(value)
        for bit,yes,no in zip(eta,inputs,complements):term=ops.mul(term,yes if bit else no)
        total=ops.add(total,term)
    return total


def separated_fibre_sum(n,groups,measurements,D,evaluate_group,forced,ops,stats):
    """Lemma 3.2, retaining only one representative per group.
    evaluate_group(g,x) is a jet and must satisfy the supplied invariance.
    """
    counts=[len(rows) for rows in measurements];c=sum(counts)
    total=ops.const(0);forced=set(forced)
    bounds=[sum(abs(x) for x in row) for rows in measurements for row in rows]
    for combined in measurement_vectors(c,D,bounds):
        stats.inc('measurement_tuples');ys=[];offset=0
        for count in counts:ys.append(combined[offset:offset+count]);offset+=count
        representatives=[]
        for g,group in enumerate(groups):
            found=None
            for u in boolean_vectors(len(group)):
                stats.inc('representative_boolean_scans')
                measured=tuple(sum(a*b for a,b in zip(row,u)) for row in measurements[g])
                if measured==ys[g]:found=u;break
            if found is None:break
            representatives.append(found)
        if len(representatives)!=len(groups):continue
        x=[0]*n
        for group,u in zip(groups,representatives):
            for i,bit in zip(group,u):x[i]=bit
        product=ops.const(1)
        for g,group in enumerate(groups):
            subtotal=ops.const(0)
            for u in boolean_vectors(len(group)):
                stats.inc('fibre_boolean_scans')
                if any(i in forced and bit!=1 for i,bit in zip(group,u)):continue
                measured=tuple(sum(a*b for a,b in zip(row,u)) for row in measurements[g])
                if measured!=ys[g]:continue
                for i,bit in zip(group,u):x[i]=bit
                stats.inc('separated_group_evaluations')
                subtotal=ops.add(subtotal,evaluate_group(g,tuple(x)))
            product=ops.mul(product,subtotal)
            for i,bit in zip(group,representatives[g]):x[i]=bit
        total=ops.add(total,product)
    return total


def hermite_at_zero(taylor,ops):
    """Exact rational CRT/Hermite recovery; only known nonzero scalar divisors."""
    Q=len(taylor);J=ops.J;answer=Fraction(0)
    for t in range(1,Q+1):
        local=ops.const(1);at_zero=Fraction(1)
        for other in range(1,Q+1):
            if other==t:continue
            difference=t-other
            local=ops.mul(local,tuple(Fraction(comb(J,k),difference**k) for k in range(J)))
            at_zero*=Fraction(-other,difference)**J
        quotient=ops.mul(taylor[t],ops.inverse(local))
        contribution=at_zero*sum(coefficient*Fraction(-t)**j for j,coefficient in enumerate(quotient))
        answer=ops.stats.note(answer+contribution)
    return answer


def count(n,factors,layout,*,validate_design=True,require_quantitative=False):
    """Execute Proposition 3.4 on an arbitrary supplied algebraically valid design.
    Factor entries may be rational; a Boolean tensor contraction returns int.
    No hidden direct-count fallback or diagnostic enumeration is invoked.
    Polynomial-space/bit-height guarantees require Boolean entries, or a supplied
    common polynomial-bit denominator and height bound for entry values. General
    rational callbacks are supported algebraically but have no such resource
    guarantee merely from a bound on each individual entry's bit length.
    """
    if not isinstance(n,int) or n<0:raise ValueError('n must be a nonnegative integer')
    factors=tuple(Factor(tuple(f.scope),f.entry) for f in factors)
    validity=validate(n,factors,layout,require_quantitative) if validate_design else {'design_validation_skipped':True}
    stats=Stats();degree=sum(len(f.scope) for f in factors)
    q=degree*layout.R//layout.Q;J=q+1;ops=Jets(J,stats);taylor={}
    for t in range(1,layout.Q+1):
        stats.inc('interpolation_nodes')
        groups=tuple(tuple(group) for group in layout.groups(t))
        measurements=tuple(tuple(tuple(row) for row in layout.measurement_rows(t,g)) for g in range(layout.r))
        assigned=[[] for _ in range(layout.r)]
        for f in range(len(factors)):assigned[layout.factor_group(t,f)].append(f)
        form_data={}
        for f,factor in enumerate(factors):
            for v in factor.scope:
                data={}
                for i,coefficients in layout.form(f,v).items():
                    shifted=[Fraction(0)]*J
                    for d,coefficient in enumerate(coefficients):
                        for k in range(min(d,J-1)+1):
                            shifted[k]+=Fraction(coefficient)*comb(d,k)*Fraction(t)**(d-k)
                    delta=list(shifted);delta[0]=Fraction(0)
                    data[i]=(shifted[0],tuple(delta))
                form_data[f,v]=data
        H=ops.const(0)
        for size in range(min(q,n)+1):
            for E in combinations(range(n),size):
                for ubits in boolean_vectors(size):
                    U={i for i,bit in zip(E,ubits) if bit};stats.inc('mobius_pairs')
                    correction={}
                    for key,data in form_data.items():
                        value=ops.const(0)
                        for i in U:
                            if i in data:value=ops.add(value,data[i][1])
                        correction[key]=value
                    def evaluate_group(g,x):
                        result=ops.const(1)
                        for f in assigned[g]:
                            inputs=[]
                            for v in factors[f].scope:
                                base=sum(value*x[i] for i,(value,delta) in form_data[f,v].items())
                                inputs.append(ops.add(ops.const(base),correction[f,v]))
                            stats.inc('factor_jet_evaluations')
                            result=ops.mul(result,multilinear_extension(factors[f],inputs,ops,stats))
                        return result
                    term=separated_fibre_sum(n,groups,measurements,layout.D,evaluate_group,E,ops,stats)
                    H=ops.add(H,ops.scale(term,-1 if (size-len(U))%2 else 1))
        taylor[t]=H
    value=hermite_at_zero(taylor,ops)
    output_stats=stats.output()
    output_stats.update(validity,n=n,factors=len(factors),scope_degree_bound=degree,
                        Taylor_order_q=q,jet_precision=J,
                        diagnostics_invoked=False,truth_tables_materialized=False,fibre_lists_materialized=False,
                        only_boolean_entry_values_observed=stats.counts.get('non_boolean_entry_evaluations',0)==0,
                        resource_contract='Boolean entries or a common polynomial-bit entry denominator/height bound')
    return CounterResult(value.numerator if value.denominator==1 else value,output_stats)


def direct_count(n,factors):
    """Explicitly separate exponential diagnostic; never called by count()."""
    factors=tuple(factors);total=Fraction(0);assignments=0
    for x in boolean_vectors(n):
        term=Fraction(1)
        for factor in factors:term*=Fraction(factor.entry(tuple(x[i] for i in factor.scope)))
        total+=term;assignments+=1
    return CounterResult(total.numerator if total.denominator==1 else total,
                         {'diagnostic_boolean_assignments':assignments},
                         method='diagnostic_direct_boolean_sum')
