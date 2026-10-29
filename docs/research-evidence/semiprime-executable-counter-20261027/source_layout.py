"""Actual pinned complete-block/cleared-defect source layout (exact arithmetic).

Independent reimplementation of OpenAI math 7ef5c0cc generic layout definitions.
See ATTRIBUTION.md. No Lean execution certificate or factoring-speed claim.
"""
from collections import Counter,defaultdict
from dataclasses import dataclass,field
from fractions import Fraction as F
from itertools import combinations,product
from math import comb
from pathlib import Path
import importlib.util
import sys
from source_parameters import Parameters,scope_statistics,check_stats

FROZEN=Path('/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-shared-counter-20261026/shared_counter.py')


def frozen_counter():
    name='_frozen_shared_counter_20261026'
    if name not in sys.modules:
        spec=importlib.util.spec_from_file_location(name,FROZEN)
        module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module)
    return sys.modules[name]


@dataclass
class Work:
    counts: Counter=field(default_factory=Counter)
    numerator_bits: int=0
    denominator_bits: int=0
    def inc(self,key,n=1):self.counts[key]+=n
    def note(self,x):
        x=F(x);self.numerator_bits=max(self.numerator_bits,abs(x.numerator).bit_length())
        self.denominator_bits=max(self.denominator_bits,x.denominator.bit_length());return x
    def output(self):return dict(counts=dict(self.counts),maximum_numerator_bits=self.numerator_bits,
                                  maximum_denominator_bits=self.denominator_bits)


class ResourceLimit(RuntimeError):pass


def poly_add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    return trim(c)


def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:a.pop()
    return tuple(a)


def poly_scale(a,c):return trim([x*c for x in a])


def poly_mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return trim(out)


def poly_value(a,t):
    out=F(0)
    for x in reversed(a):out=out*t+x
    return out


def exact_solve(matrix,target,work=None):
    """Unique rational solve; used only for the source binomial coefficient vector."""
    n=len(matrix);a=[list(map(F,row))+[F(y)] for row,y in zip(matrix,target)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i][j]),None)
        if pivot is None:raise ArithmeticError('singular binomial matrix')
        a[j],a[pivot]=a[pivot],a[j];z=a[j][j];a[j]=[x/z for x in a[j]]
        for i in range(n):
            if i!=j and a[i][j]:
                z=a[i][j];a[i]=[x-z*y for x,y in zip(a[i],a[j])]
                if work:work.inc('binomial_elimination_rows')
        if work:
            for row in a:
                for x in row:work.note(x)
    return tuple(row[-1] for row in a)


def parity_coefficients(A,R,work=None):
    cs=exact_solve([[comb(A+i,j) for j in range(R)] for i in range(R)],
                   [(-1)**(A+i) for i in range(R)],work)
    if any(c.denominator!=1 for c in cs):raise ArithmeticError('noninteger parity coefficient')
    cs=tuple(int(c) for c in cs)
    assert all(sum(c*comb(A+i,j) for j,c in enumerate(cs))==(-1)**(A+i) for i in range(R))
    return cs


def conditional_score(n,scopes,p,av,df,work=None):
    """Exact conditional mean of source y²*incidenceEnergy+x²*headEnergy."""
    words=p.r**p.Q;D=words*words;inc=[(f,v) for f,s in enumerate(scopes) for v in s];M=len(inc)
    x=p.epsilon*F(M,D);y=F(n,2*p.r)
    def eq(table,a,b,t=None):
        if a==b:return F(1)
        if a in table and b in table:return F(table[a]==table[b] if t is None else table[a][t]==table[b][t])
        return F(1,words if t is None else p.r)
    incidence=F(0);head=F(0)
    for f,v in inc:
        for ff,vv in inc:
            incidence+=eq(av,v,vv)*eq(df,f,ff)
            if work:work.inc('conditional_incidence_terms')
    for t in range(p.Q):
        for v in range(n):
            for vv in range(n):
                head+=eq(av,v,vv,t)
                if work:work.inc('conditional_head_terms')
    ans=y*y*(incidence-F(M*M,D))+x*x*(head-F(p.Q*n*n,p.r))
    return work.note(ans) if work else ans


def computed_words(n,scopes,p,work):
    alphabet=tuple(product(range(p.r),repeat=p.Q));av={};df={};history=[conditional_score(n,scopes,p,av,df,work)]
    # Source indices enumeration: all original variables, then all factors.
    for table,index in [(av,v) for v in range(n)]+[(df,f) for f in range(len(scopes))]:
        chosen=None;best=None
        for word in alphabet:
            table[index]=word;score=conditional_score(n,scopes,p,av,df,work);work.inc('word_candidates')
            if best is None or score<best:best=score;chosen=word
        table[index]=chosen
        if best>history[-1]:raise ArithmeticError('conditional expectation increased')
        history.append(best)
    return tuple(av[v] for v in range(n)),tuple(df[f] for f in range(len(scopes))),tuple(history)


def swap_positions(u,positions):
    a,b=map(list,u)
    for t in positions:a[t],b[t]=b[t],a[t]
    return tuple(a),tuple(b)


def numerator_operator_row(u,t,Q,R,cs,work=None):
    """Literal integerDifference expansion of LayoutNumerator.entry.

    Active positions EXCLUDE t. It is not the old Q-coordinate eigenbasis matrix.
    """
    active=tuple(k for k in range(Q) if k!=t);start=swap_positions(u,active);out=defaultdict(int)
    for j in range(min(R,Q)):
        for S in combinations(active,j):
            coefficient=cs[j]*2**(R-1-j)
            for mask in range(1<<j):
                positions=tuple(S[k] for k in range(j) if mask>>k&1)
                y=swap_positions(start,positions)
                out[y]+=coefficient*(-1 if mask.bit_count()%2 else 1)
                if work:work.inc('integer_difference_terms')
    return {y:c for y,c in out.items() if c}


def interpolation_basis(nodes,t):
    # z/t * product_(s!=t) (z-s)/(t-s), exactly SubexpRowInterpolation.basis.
    out=(F(0),F(1,t))
    for s in nodes:
        if s!=t:out=poly_mul(out,(F(-s,t-s),F(1,t-s)))
    return out


class Universal:
    def __init__(self,p,work):
        self.p=p;self.words=tuple(product(range(p.r),repeat=p.Q));self.types=tuple(product(self.words,repeat=2))
        self.index={u:i for i,u in enumerate(self.types)};self.denominator=2**(p.R-1)
        self.cs=parity_coefficients(p.A0,p.R,work);self.N={};self.joints={}
        for t in range(p.Q):
            for g in range(p.r):
                joint=tuple(u for u in self.types if u[0][t]==g and u[1][t]!=g);self.joints[t,g]=joint
                for u in joint:
                    row=numerator_operator_row(u,t,p.Q,p.R,self.cs,work)
                    if any(y not in joint for y in row):raise ArithmeticError('joint support failed')
                    self.N[t,g,u]=row
        self.rows={};basis_cache={}
        for u in self.types:
            row={}
            for y in self.types:
                mismatch=tuple(t+1 for t in range(p.Q) if y[0][t]!=u[1][t])
                coeff=(F(u==y),)
                if len(mismatch)<=p.R:
                    for node in mismatch:
                        t=node-1;g=y[0][t]
                        value=-F(self.N.get((t,g,u),{}).get(y,0),self.denominator)
                        if value:
                            key=(mismatch,node)
                            if key not in basis_cache:basis_cache[key]=interpolation_basis(mismatch,node)
                            coeff=poly_add(coeff,poly_scale(basis_cache[key],value));work.inc('row_interpolation_terms')
                elif any(self.N.get((t,y[0][t],u),{}).get(y,0) for t in range(p.Q)):
                    raise ArithmeticError('source mismatch support bound failed')
                if any(coeff):row[y]=coeff
                for c in coeff:work.note(c)
            self.rows[u]=row


def select_actual_rows(rows,width,work):
    """Gaussian scratch pivots may be normalized; SELECTED ROWS NEVER ARE."""
    basis=[];selected=[];indices=[]
    for index,original in enumerate(rows):
        row=list(map(F,original))
        if len(row)!=width:raise ValueError('constraint width')
        for pivot,b in basis:
            c=row[pivot]
            if c:row=[x-c*y for x,y in zip(row,b)];work.inc('constraint_elimination_rows')
        pivot=next((i for i,x in enumerate(row) if x),None)
        if pivot is not None:
            c=row[pivot];row=[x/c for x in row];basis.append((pivot,row));basis.sort()
            selected.append(tuple(original));indices.append(index)
        for c in row:work.note(c)
    return tuple(selected),tuple(indices)


class Layout:
    def groups(self,t):return self._groups[t]
    def factor_group(self,t,f):return self.factor_words[f][t-1]
    def measurement_rows(self,t,g):return self._measurements[t][g]
    def form(self,f,v):return self._forms[f,v]
    def validate(self,quantitative=False):
        frozen=frozen_counter();factors=[frozen.Factor(s,lambda _:1) for s in self.scopes]
        ans=frozen.validate(self.n,factors,self,quantitative)
        if self.require_guard:
            M=sum(map(len,self.scopes));eps=self.parameters.epsilon
            if self.block_count*self.universal_dimension<(1-eps)*M:raise AssertionError('complete-block coverage')
            for t in range(1,self.Q+1):
                if any(2*self.r*len(g)>3*self.n for g in self.groups(t)):raise AssertionError('source head bound')
                if sum(len(self.measurement_rows(t,g)) for g in range(self.r))>2*eps*M:raise AssertionError('source rank bound')
        return ans


def construct_layout(n,scopes,parameters,*,labels=None,require_guard=True,max_dimension=None):
    scopes=tuple(tuple(s) for s in scopes);st=scope_statistics(n,scopes);p=parameters
    if n<1 or not st['covered']:raise ValueError('all original variables must occur; no unary tensors added')
    if p.r<2 or p.Q<2 or not 1<=p.R<p.Q:raise ValueError('counter-compatible dimensions required')
    guard=check_stats(n,st['M'],st['B'],st['w'],p)
    if require_guard and not guard['accepted']:raise ValueError('source guard failed before construction: '+repr(guard['reasons']))
    if max_dimension is not None and p.dimension>max_dimension:raise ResourceLimit('explicit auxiliary dimension limit')
    work=Work()
    if labels is None:av,df,history=computed_words(n,scopes,p,work)
    else:
        av,df=tuple(map(tuple,labels[0])),tuple(map(tuple,labels[1]));history=None
        if len(av)!=n or len(df)!=len(scopes) or any(len(w)!=p.Q or any(type(g) is not int or not 0<=g<p.r for g in w) for w in av+df):
            raise ValueError('invalid explicit word labels')
    U=Universal(p,work);incidences=tuple((f,v) for f,s in enumerate(scopes) for v in s)
    buckets={u:[] for u in U.types}
    for inc in incidences:buckets[av[inc[1]],df[inc[0]]].append(inc)
    block_count=min(map(len,buckets.values()));placement={};copies=[]
    for j in range(block_count):
        copy={u:buckets[u][j] for u in U.types};copies.append(copy)
        for u,inc in copy.items():placement[inc]=(j,u)
    leftovers=tuple(inc for inc in incidences if inc not in placement)
    forms={}
    for inc in incidences:
        f,v=inc
        if inc not in placement:forms[inc]={v:(F(1),)};continue
        j,u=placement[inc];row={}
        for y,coeff in U.rows[u].items():
            target=copies[j][y][1];row[target]=poly_add(row.get(target,(F(0),)),coeff)
        forms[inc]={v:coeff for v,coeff in row.items() if any(coeff)}
    obj=Layout();obj.n=n;obj.r=p.r;obj.Q=p.Q;obj.R=p.R;obj.parameters=p;obj.scopes=scopes
    obj.require_guard=require_guard;obj.guard=guard;obj.variable_words=av;obj.factor_words=df
    obj.conditional_history=history;obj.universal=U;obj.universal_dimension=p.dimension
    obj.block_count=block_count;obj.placement=placement;obj.leftovers=leftovers;obj._forms=forms
    # Frozen interface D means MEASUREMENT L1 RADIUS, not auxiliary dimension.
    W0=2*(8*p.Q)**(2*p.R);obj.constraint_entry_bound=st['B']*W0
    obj.D=max(1,n*obj.constraint_entry_bound);obj.tau=p.epsilon*F(st['M'],n)
    obj._groups={};obj._measurements={};obj.raw_constraints={};obj.selected_indices={}
    for t in range(1,p.Q+1):
        groups=tuple(tuple(v for v in range(n) if av[v][t-1]==g) for g in range(p.r));obj._groups[t]=groups
        obj._measurements[t]={}
        for g,group in enumerate(groups):
            raw=[]
            for j,copy in enumerate(copies):
                joint=U.joints[t-1,g]
                for u in joint:
                    full=[0]*n
                    for y in joint:
                        value=(U.denominator if u==y else 0)-U.N[t-1,g,u].get(y,0)
                        full[copy[y][1]]+=value
                    raw.append(tuple(full[v] for v in group))
            for f,v in leftovers:
                if av[v][t-1]==g:raw.append(tuple(int(v==vv) for vv in group))
            if any(any(abs(c)>obj.constraint_entry_bound for c in row) for row in raw):
                raise ArithmeticError('source literal constraint height bound failed')
            selected,indices=select_actual_rows(raw,len(group),work)
            obj.raw_constraints[t,g]=tuple(raw);obj.selected_indices[t,g]=indices;obj._measurements[t][g]=selected
            work.inc('raw_constraint_rows',len(raw));work.inc('selected_measurement_rows',len(selected))
    obj.work=work
    obj.validate(quantitative=require_guard)
    return obj
