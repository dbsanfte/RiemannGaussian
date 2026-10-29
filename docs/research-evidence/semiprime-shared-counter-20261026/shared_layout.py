"""Exact constructive Lemma 4.7 layout (paper Section 4).

Dense, polynomial-time reference implementation, NOT a fast contraction.
Variables, factors and groups are zero based; sample points are 1,...,Q.
`require_lemma=False` disables quantitative hypotheses for tiny algebra controls
only; the returned object still verifies restoration, degree and kernel separation.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from collections import Counter


def _poly_mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return tuple(c)


def _eval(a,t):
    z=F(0)
    for x in reversed(a): z=z*t+x
    return z


def _rank(rows):
    a=[list(map(F,row)) for row in rows]
    if not a:return 0
    k=0
    for j in range(len(a[0])):
        p=next((i for i in range(k,len(a)) if a[i][j]),None)
        if p is None:continue
        a[k],a[p]=a[p],a[k]
        z=a[k][j];a[k]=[x/z for x in a[k]]
        for i in range(k+1,len(a)):
            z=a[i][j]
            if z:a[i]=[x-z*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a):break
    return k


def tail_probability(r,Q,R,A0):
    return F(sum(comb(Q,j)*(r-1)**j*(r+1)**(Q-j)
                 for j in range(Q+1) if not A0<=j<A0+R),(2*r)**Q)


def lemma_hypotheses(n,scopes,r,Q,R,A0,tau):
    counts=Counter(v for s in scopes for v in s)
    b=max(counts.values(),default=0);w=max(map(len,scopes),default=0)
    M=sum(map(len,scopes));D=r**(2*Q) if r>=2 and Q>=1 else 0
    checks={"positive_covered_input":n>=1 and b>=1 and w>=1 and set(counts)==set(range(n)) and n<=M<=b*n,
            "parameter_range":r>=2 and 1<=R<Q and F(0)<tau<=F(1,2),
            "interval":0<=A0 and A0+R<=Q+1,
            "incidence_balance":2*(b+w)*D*D<=M,
            "group_balance":2*Q*r*r<=n}
    checks['tail']=(checks['parameter_range'] and checks['interval'] and
                    tail_probability(r,Q,R,A0)<=tau/(r*b)) if b else False
    return checks


def deterministic_labels(n,scopes,r,Q):
    """Lemma 4.5 exact conditional expectation, labels fixed as whole words.

    Indicator probabilities are computed analytically, equivalent to enumerating
    at most (r^Q)^4 assignments per indicator. All choices use exact Fractions.
    """
    words=tuple(product(range(r),repeat=Q));K=len(words);D=K*K
    M=sum(map(len,scopes));b=max(Counter(v for s in scopes for v in s).values());w=max(map(len,scopes))
    incidences=[(f,v) for f,s in enumerate(scopes) for v in s]
    av={};df={f:(0,)*Q for f,s in enumerate(scopes) if not s}
    def eq(tab,i,j,t=None):
        if i==j:return F(1)
        if i in tab and j in tab:return F(tab[i]==tab[j] if t is None else tab[i][t]==tab[j][t])
        return F(1,K if t is None else r)
    def score():
        phi=sum((eq(av,v,vv)*eq(df,f,ff) for f,v in incidences for ff,vv in incidences),F(0))-F(M*M,D)
        xi=sum((eq(av,v,vv,t) for t in range(Q) for v in range(n) for vv in range(n)),F(0))-F(Q*n*n,r)
        return phi/(M*(b+w))+xi/(Q*n)
    history=[score()]
    for tab,key in [(av,v) for v in range(n)]+[(df,f) for f,s in enumerate(scopes) if s]:
        best=None;chosen=None
        for word in words:
            tab[key]=word;value=score()
            if best is None or value<best:best=value;chosen=word
        tab[key]=chosen
        if best>history[-1]:raise AssertionError('conditional expectation increased')
        history.append(best)
    return tuple(av[v] for v in range(n)),tuple(df[f] for f in range(len(scopes))),tuple(history)


def _auxiliary(r,Q,R,A0):
    words=tuple(product(range(r),repeat=Q))
    labels=tuple(product(words,repeat=2));D=len(labels)
    # One-coordinate orthogonal eigenvectors of exchange, entries in {0,+1,-1}.
    local=[]
    for a in range(r):local.append(({(a,a):1},0))
    for a in range(r):
        for d in range(a+1,r):
            local.extend([({(a,d):1,(d,a):1},0),({(a,d):1,(d,a):-1},1)])
    basis=[];CB=[];M0=[[F(0)]*D for _ in range(D)]
    for choices in product(local,repeat=Q):
        j=sum(c[1] for c in choices)
        psi=tuple(__import__('functools').reduce(lambda x,s:x*choices[s][0].get((a[s],d[s]),0),range(Q),1) for a,d in labels)
        norm=sum(x*x for x in psi)
        # f_I(j)=(-1)^A0 sum (-2)^k binom(j-A0,k), generalized binomial.
        term=F(1);f=F(0)
        for k in range(R):
            if k:term*=F(j-A0-k+1,k)
            f+=(-1)**A0*(-2)**k*term
        eig=(-1)**j*f
        if not A0<=j<A0+R:CB.append(psi)
        for u,x in enumerate(psi):
            if x:
                for y,z in enumerate(psi):
                    if z:M0[u][y]+=eig*x*z/norm
        basis.append((psi,j,eig))
    # Universal rows δ_u + M0[u,y](φ_u,y−1).
    rows=[]
    for u,(au,du) in enumerate(labels):
        row=[]
        for y,(ay,dy) in enumerate(labels):
            coeff=[F(u==y)]+[F(0)]*(R-1)
            if M0[u][y]:
                bad=[s+1 for s in range(Q) if ay[s]!=du[s]]
                if len(bad)>R-1:raise AssertionError('M0 support lemma failed')
                phi=(F(1),)
                for s in bad:phi=_poly_mul(phi,(F(1),F(-1,s)))
                for k,c in enumerate(phi):coeff[k]+=M0[u][y]*(c-(k==0))
            row.append(tuple(coeff))
        rows.append(tuple(row))
    return labels,tuple(CB),tuple(rows),tuple(tuple(x) for x in M0),tuple(basis)


class Layout:
    def groups(self,t):return self._groups[t]
    def factor_group(self,t,f):return self.df[f][t-1]
    def measurement_rows(self,t,g):return self._measurements[t][g]
    def form(self,f,v):return self._forms[(f,v)]
    def validate(self,quantitative=True):
        errors=[]
        for f,s in enumerate(self.scopes):
            for v in s:
                row=self.form(f,v)
                if any(_eval(row.get(y,(F(0),)),0)!=F(y==v) for y in range(self.n)):errors.append(('initial',f,v))
                if any(len(c)>self.R for c in row.values()):errors.append(('degree',f,v))
                for t in range(1,self.Q+1):
                    for g,group in enumerate(self.groups(t)):
                        if g==self.factor_group(t,f):continue
                        C=self.measurement_rows(t,g)
                        p=tuple(_eval(row.get(y,(F(0),)),t) for y in group)
                        if _rank(C)!=_rank(tuple(C)+(p,)):errors.append(('kernel',f,v,t,g))
        for t in range(1,self.Q+1):
            flat=[v for g in self.groups(t) for v in g]
            if sorted(flat)!=list(range(self.n)):errors.append(('partition',t))
            for g in range(self.r):
                for row in self.measurement_rows(t,g):
                    if any(not isinstance(x,int) for x in row) or sum(map(abs,row))>self.D:errors.append(('measurement',t,g))
            if quantitative:
                if any(len(g)*self.r>2*self.n for g in self.groups(t)):errors.append(('group_bound',t))
                if sum(len(self.measurement_rows(t,g)) for g in range(self.r))>2*self.tau*self.n:errors.append(('measurement_count',t))
        if errors:raise AssertionError(errors[:10])
        return True


def construct_layout(n,scopes,*,r,Q,R,A0,tau,labels=None,require_lemma=True):
    """Construct all supplied-design data; no hidden independent Boolean copies.

    labels=(av,df) optionally supplies diagnostic labels. They are checked for
    balance when quantitative mode is enabled. No scopes/factors are added.
    """
    if any(type(x)!=int for x in (n,r,Q,R,A0)):raise ValueError('integer dimensions required')
    scopes=tuple(tuple(s) for s in scopes);tau=F(tau)
    if n<1 or any(len(set(s))!=len(s) or any(type(v)!=int or not 0<=v<n for v in s) for s in scopes):raise ValueError('invalid scopes')
    if set(v for s in scopes for v in s)!=set(range(n)):raise ValueError('scopes must cover every variable; add explicit constant-one factors if necessary')
    if not(r>=2 and Q>=1 and 1<=R<=Q and 0<=A0 and A0+R<=Q+1 and 0<tau<=F(1,2)):raise ValueError('invalid parameters')
    checks=lemma_hypotheses(n,scopes,r,Q,R,A0,tau)
    if require_lemma and not all(checks.values()):raise ValueError('Lemma 4.7 hypotheses failed: '+repr(checks))
    obj=Layout();obj.n=n;obj.scopes=scopes;obj.r=r;obj.Q=Q;obj.R=R;obj.D=r**(2*Q);obj.tau=tau;obj.hypotheses=checks
    if labels is None:obj.av,obj.df,obj.conditional_history=deterministic_labels(n,scopes,r,Q)
    else:
        obj.av,obj.df=tuple(map(tuple,labels[0])),tuple(map(tuple,labels[1]));obj.conditional_history=None
    if len(obj.av)!=n or len(obj.df)!=len(scopes) or any(len(x)!=Q or any(type(g)!=int or not 0<=g<r for g in x) for x in obj.av+obj.df):raise ValueError('invalid supplied labels')
    if any(not s and obj.df[f]!=(0,)*Q for f,s in enumerate(scopes)):raise ValueError('empty factors must use group zero')
    auxiliary,CB,auxrows,M0,basis=_auxiliary(r,Q,R,A0)
    if any((factorial(R-1)*x).denominator!=1 for row in M0 for x in row):raise AssertionError('M0 denominator failed')
    index={u:i for i,u in enumerate(auxiliary)};buckets={};placement={}
    for f,s in enumerate(scopes):
        for v in s:
            u=index[(obj.av[v],obj.df[f])];copy=buckets.get(u,0);buckets[u]=copy+1;placement[f,v]=(copy,u)
    h=max(buckets.values());occupied={p:v for (f,v),p in placement.items()}
    if require_lemma and h*obj.D>2*sum(map(len,scopes)):raise AssertionError('label multiplicity bound failed')
    Chat=[]
    for c in range(h):
        for psi in CB:
            row=[0]*n
            for u,x in enumerate(psi):
                v=occupied.get((c,u))
                if v is not None:row[v]+=x
            Chat.append(tuple(row))
    forms={}
    for (f,v),(c,u) in placement.items():
        form={}
        for y,coeff in enumerate(auxrows[u]):
            vv=occupied.get((c,y))
            if vv is not None:
                old=form.get(vv,(F(0),)*R)
                form[vv]=tuple(a+b for a,b in zip(old,coeff))
        forms[f,v]={y:coef for y,coef in form.items() if any(coef)}
    obj._groups={t:tuple(tuple(v for v in range(n) if obj.av[v][t-1]==g) for g in range(r)) for t in range(1,Q+1)}
    obj._measurements={t:tuple(tuple(tuple(row[v] for v in group) for row in Chat) for group in obj.groups(t)) for t in range(1,Q+1)}
    obj._forms=forms;obj.copy_count=h;obj.placement=placement;obj.common_measurements=tuple(Chat)
    obj.aux_labels=auxiliary;obj.aux_measurements=CB;obj.aux_rows=auxrows;obj.M0=M0;obj.eigenbasis=basis
    obj.denominator=factorial(R-1)*factorial(Q)
    if any((obj.denominator*c).denominator!=1 for row in forms.values() for coeff in row.values() for c in coeff):raise AssertionError('common denominator failed')
    obj.validate(quantitative=require_lemma)
    return obj


def build_layout(n,scopes,r,Q,R,A0,*,tau=F(1,2),labels=None,require_lemma=False):
    """Algebraic constructor API used by the supplied-design counter.

    Root-owned shared_parameters.py decides whether to contract or use the finite
    fallback. Set require_lemma=True to enforce all asymptotic design bounds here.
    """
    return construct_layout(n,scopes,r=r,Q=Q,R=R,A0=A0,tau=tau,
                            labels=labels,require_lemma=require_lemma)
