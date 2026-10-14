"""Independent math-only native366-square/403-relation/full15 reconstruction.

No archives, optional closure verifications or cryptographic digests. Ordered
factor declarations preserve the functional legacy coordinate order explicitly.
"""
from fractions import Fraction as F
import math

FACTOR_ORDER=[('1/2','one'),('1/2','a'),('1/3','one'),('1/2','b'),('2/3','one'),('1/3','a'),('1/3','b'),('1/2','a_minus_b'),('1/4','one'),('2/3','b'),('1/4','a'),('2/3','a'),('1/4','b'),('1/5','one'),('1/3','a_minus_b'),('1/4','a_minus_b'),('1/6','one'),('2/5','one'),('3/4','one'),('1/5','b'),('1/5','a'),('2/3','a_minus_b'),('3/5','one'),('2/5','a'),('3/4','a'),('2/5','b'),('1/6','b'),('3/4','b'),('1/6','a'),('1/5','a_minus_b'),('2/5','a_minus_b'),('3/4','a_minus_b'),('3/5','a'),('3/5','b'),('1/6','a_minus_b'),('4/5','one'),('4/5','a'),('4/5','b'),('3/5','a_minus_b'),('5/6','one'),('4/5','a_minus_b'),('5/6','b'),('5/6','a'),('5/6','a_minus_b')]

class Algebra:
    """Independent sparse rational arithmetic, no producer polynomial helpers."""
    def __init__(self,max_operations,max_terms,max_bits,max_retained_cells):
        self.limit=max_operations;self.used=0;self.terms=max_terms;self.bits=max_bits;self.cell_limit=max_retained_cells;self.retained=0
    def charge(self,n):
        if n>self.limit-self.used:raise OverflowError('independent native scalar work cap')
        self.used+=n
    def checked(self,p):
        if len(p)>self.terms:raise OverflowError('independent native polynomial term cap')
        for q in p.values():
            if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>self.bits:raise OverflowError('independent native rational bit cap')
        return p
    def add(self,*ps):
        out={}
        for p in ps:
            for m,q in p.items():
                self.charge(1);v=out.get(m,F(0))+q
                if v:out[m]=v
                else:out.pop(m,None)
        return self.checked(out)
    def scale(self,p,q):
        self.charge(len(p));return self.checked({m:v*q for m,v in p.items() if v*q})
    def mul(self,p,q):
        out={}
        for m,a in p.items():
            for n,b in q.items():
                self.charge(1);key=tuple(sorted(m+n));v=out.get(key,F(0))+a*b
                if v:out[key]=v
                else:out.pop(key,None)
                if len(out)>self.terms:raise OverflowError('independent native product allocation cap')
        return self.checked(out)
    def serial(self,p):
        self.checked(p)
        if len(p)>self.cell_limit-self.retained:raise OverflowError('independent native retained cell cap')
        self.retained+=len(p);self.charge(len(p))
        return [dict(m=list(m),c=str(p[m])) for m in sorted(p)]

class _Atoms:
    @staticmethod
    def constant(q):return {():F(q)} if q else {}
    @staticmethod
    def variable(n):return {(n,):F(1)}
    @staticmethod
    def factor_witness(n,**unused):
        out=[];d=2
        while d*d<=n:
            e=0
            while n%d==0:n//=d;e+=1
            if e:out.append([d,e])
            d+=1
        if n>1:out.append([n,1])
        return out
L=_Atoms()
def _ceilroot(n,k):
    lo=0;hi=n+1
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**k<n:lo=mid
        else:hi=mid
    return hi

def floor_scaled_power(n,spec):
    c=F(spec['coefficient']);p=F(spec['power']);lo=0;hi=n+2
    rhs=c.numerator**p.denominator*n**p.numerator;den=c.denominator**p.denominator
    while hi**p.denominator*den<=rhs:hi*=2
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**p.denominator*den<=rhs:lo=mid
        else:hi=mid
    return lo


def build_affine(program,X,*,max_horizon=27,max_operations=50000000,max_terms=100000,max_coefficient_bits=4096,max_retained_cells=4000000):
    if program!=dict(target='mu',q=6,C='32',claim='critical')or type(X)is not int or not 1<=X<=7 or 4*X-1>max_horizon:raise ValueError('fixed bounded critical native source')
    A=Algebra(max_operations,max_terms,max_coefficient_bits,max_retained_cells);H=4*X-1;one=L.constant(1);zero={};squares=[];relations=[]
    factors={n:L.factor_witness(n,max_n=H,max_operations=4*H+16)for n in range(1,H+1)}
    sf={n:int(all(e==1 for p,e in factors[n]))for n in factors}
    prime=lambda n:factors.get(n)==[[n,1]]
    prefix=[{}]
    for n in range(1,H+1):prefix.append(A.add(prefix[-1],L.variable(n)))
    def K(Y,t):return max(0,2*Y-max(Y,t))
    def J(t):return K(2*X,t)-4*K(X,t)
    def rowmass(i):
        lo=max(2*X,i);return sum(range(lo,4*X))
    def region(r,i):return r=='all'or r=='head'and i<=2*X or r=='tail'and i>2*X or r=='initial'and i<X or r=='parent'and X<=i<2*X or r=='child'and 2*X<=i<4*X
    def square(poly,w=1):return dict(weight=str(F(w)),poly=A.serial(poly))
    def relation(spec,m):return dict(spec=spec,multiplier=A.serial(m))
    def weight(w,i):return 1 if w=='one'else X if w=='X'else X*X if w=='X2'else J(i)if w=='defect_kernel'else rowmass(i)
    # Exactly the original52 grouped squares, including empty fixed positions.
    squares.append([square(one,X*X*_ceilroot(X,6))])
    for r in ('all','head','tail'):
        for w in ('one','X','X2'):squares.append([square(L.variable(i),weight(w,i))for i in range(1,H+1)if region(r,i)])
    for r in ('all','initial','parent','child'):
        for w in ('one','X'):squares.append([square(prefix[i],weight(w,i))for i in range(1,H+1)if region(r,i)])
    for domain in ('all','coprime','noncoprime','divides'):
        for sign in (1,-1):
            for w in ('one','child_kernel','abs_defect_kernel'):
                group=[]
                for a in range(1,H+1):
                    for b in range(a+1,H+1):
                        if domain=='coprime'and math.gcd(a,b)!=1 or domain=='noncoprime'and math.gcd(a,b)==1 or domain=='divides'and b%a:continue
                        group.append(square(A.add(L.variable(a),A.scale(L.variable(b),sign)),1 if w=='one'else K(2*X,b)if w=='child_kernel'else abs(J(b))))
                squares.append(group)
    for r in ('all','head','tail'):
        for w in ('one','X'):squares.append([square(A.add(*(L.variable(d)for d in range(1,i+1)if i%d==0)),weight(w,i))for i in range(2,H+1)if region(r,i)])
    for domain in ('all','coprime'):
        for w in ('one','child_kernel'):squares.append([square({(a,b):F(1)},1 if w=='one'else K(2*X,b))for a in range(1,H+1)for b in range(a+1,H+1)if domain=='all'or math.gcd(a,b)==1])
    specs={f:[]for f in ('norm','prime_power','squarefree_zero','inverse_row','coprime_product','gcd_product','unit')};specs['unit']=[dict(kind='unit')]
    for n in range(1,H+1):
        specs['norm'].append(dict(kind='norm',n=n,factors=factors[n]))
        if len(factors[n])==1:p,e=factors[n][0];specs['prime_power'].append(dict(kind='prime_power',p=p,e=e))
        if not sf[n]:specs['squarefree_zero'].append(dict(kind='squarefree_zero',n=n))
        if n>=2:specs['inverse_row'].append(dict(kind='inverse_row',n=n))
    for a in range(1,H+1):
        for b in range(a,H+1):
            specs['gcd_product'].append(dict(kind='gcd_product',a=a,b=b,factors_a=factors[a],factors_b=factors[b]))
            if a>=2 and a*b<=H and math.gcd(a,b)==1:specs['coprime_product'].append(dict(kind='coprime_product',a=a,b=b))
    def anchor(s):return s['a']*s['b']if s['kind']=='coprime_product'else s['b']if s['kind']=='gcd_product'else s['p']**s['e']if s['kind']=='prime_power'else s.get('n',1)
    def base_rel(f,r,w,m):
        group=[]
        for spec in specs[f]:
            i=anchor(spec)
            if region(r,i):group.append(relation(spec,A.scale(one if m=='one'else L.variable(i)if m=='anchor'else prefix[H]if m=='global_prefix'else prefix[i],weight(w,i))))
        relations.append(group)
    for f in ('norm','prime_power','squarefree_zero','inverse_row','coprime_product'):
        for r in ('all','head','tail'):
            for w in ('one','X','defect_kernel','child_rowmass'):
                for m in ('one','anchor','prefix'):base_rel(f,r,w,m)
    for r in ('all','head','tail'):
        for w in ('one','X','defect_kernel','child_rowmass'):base_rel('gcd_product',r,w,'one')
    for m in ('one','anchor','global_prefix'):base_rel('unit','all','one',m)
    # Exact signed masks and growing-prime sources; no AST archive/compiler hash.
    atoms=('prefix','half','even','mod3one','prime')
    def atom(kind,t):return prefix[t]if kind=='prefix'else prefix[t//2]if kind=='half'else {(n,):F(1)for n in range(1,t+1)if n%2==0}if kind=='even'else {(n,):F(1)for n in range(1,t+1)if n%3==1}if kind=='mod3one'else {(n,):F(1)for n in range(1,t+1)if prime(n)}
    signed=[(r,a,None,1,None)for r in ('parent','child')for a in atoms]
    signed.extend((r,a,b,sign,None)for r in ('parent','child')for i,a in enumerate(atoms)for b in atoms[i+1:]for sign in (1,-1))
    signed.extend((r,None,None,1,k)for r in ('parent','child')for k in (2,3))
    for r,a,b,sign,k in signed:
        group=[]
        for t in range(X,2*X)if r=='parent'else range(2*X,4*X):
            p=atom(a,t)if k is None and b is None else A.add(atom(a,t),A.scale(atom(b,t),sign))if k is None else A.add(*(L.variable(j)for p in range(2,_ceilroot(X,k)+1)if prime(p)for j in range(1,t//p+1)if math.gcd(j,p)==1))
            group.append(square(p))
        squares.append(group)
    for f in ('norm_core','gcd_pair','prime_transport'):
        for r in ('all','head','tail'):
            for m in ('product','difference'):
                for w in ('one','defect_kernel'):
                    group=[]
                    for a in range(1,H+1):
                        for b in range(1 if f=='prime_transport'else a,H+1):
                            i=b
                            if f=='prime_transport':
                                if not prime(a)or a*b>H or math.gcd(a,b)!=1:continue
                                i=a*b;spec=dict(kind='coprime_product',a=a,b=b);p=A.mul(L.variable(a),L.variable(b))if m=='product'else A.mul(L.variable(b),A.add(prefix[i],A.scale(prefix[b],-1)))
                            else:
                                g=math.gcd(a,b);u,v=(a//g,b//g)if f=='norm_core'else(a,b);spec=dict(kind='norm',n=g,factors=factors[g])if f=='norm_core'else dict(kind='gcd_product',a=a,b=b,factors_a=factors[a],factors_b=factors[b]);p=A.mul(L.variable(u),L.variable(v))if m=='product'else A.mul(A.add(L.variable(u),A.scale(L.variable(v),-1)),A.add(L.variable(u),A.scale(L.variable(v),-1)))
                            if region(r,i):group.append(relation(spec,A.scale(p,1 if w=='one'else J(i))))
                    relations.append(group)
    #44 ordered factor blocks; every ordered coprime pair and complement retained.
    for theta,kernel in FACTOR_ORDER:
        cut=floor_scaled_power(H,dict(coefficient='1',power=theta));normal=F(1,H**(0 if kernel=='one'else 1));parts=[]
        for inside in (True,False):
            B={};C={};terms=[]
            for a in range(1,H+1):
                for b in range(1,H//a+1):
                    if math.gcd(a,b)!=1 or(a<=cut)!=inside:continue
                    q=F(1 if kernel=='one'else a if kernel=='a'else b if kernel=='b'else a-b);B=A.add(B,A.scale({tuple(sorted((a,b))):F(1)},q));C=A.add(C,A.scale(L.variable(a*b),q));terms.append((dict(kind='coprime_product',a=a,b=b),q))
            B=A.scale(B,normal);C=A.scale(C,normal);T=A.add(B,A.scale(C,-1));plus=A.add(B,C);parts.append((B,C,terms,T,plus))
        squares.extend([[square(part[i])for part in parts]for i in (0,1)])
        for i in (4,3):relations.append([relation(spec,A.scale(part[i],normal*q))for part in parts for spec,q in part[2]])
        contrast=A.add(parts[0][1],A.scale(parts[1][1],-1));squares.extend([[square(A.add(prefix[H],contrast))],[square(A.add(prefix[H],A.scale(contrast,-1)))]] )
    # Complete divisor-localizer sources, with allordered inverse pairs.
    for r in ('parent','child'):
        ts=range(X,2*X)if r=='parent'else range(2*X,4*X)
        for power in (-1,0,1):
            sq={k:[]for k in ('plain','squarefree_plain','modulated','plus','minus')};norms={};inverse={}
            for t in ts:
                weights={a:F(a,t)**power for a in range(1,t+1)}
                for d in range(1,t+1):
                    p={(a,):weights[a]for a in range(d,t+1,d)};mod={tuple(sorted((d,a))):q for(a,),q in p.items()}
                    for form,poly in [('plain',p),('squarefree_plain',p),('modulated',mod),('plus',A.add(p,mod)),('minus',A.add(p,A.scale(mod,-1)))]:sq[form].append(square(poly,sf[d]if form=='squarefree_plain'else 1))
                    norms[d]=A.add(norms.get(d,{}),A.mul(p,p))
                for a in range(1,t+1):
                    for b in range(1,t+1):
                        g=math.gcd(a,b);inverse[g]=A.add(inverse.get(g,{}),{tuple(sorted((a,b))):weights[a]*weights[b]})
            squares.extend(sq[k]for k in ('plain','squarefree_plain','modulated','plus','minus'));relations.append([relation(dict(kind='norm',n=d,factors=factors[d]),p)for d,p in sorted(norms.items())]);relations.append([relation(dict(kind='unit')if g==1 else dict(kind='inverse_row',n=g),p)for g,p in sorted(inverse.items())])
    #18 cells retain exact inclusive floor cut and full complement. State usesD.
    contrasts={}
    for r in ('parent','child'):
        ts=range(X,2*X)if r=='parent'else range(2*X,4*X)
        for theta in ('1/3','1/2','2/3'):
            for power in (-1,0,1):
                sq={k:[]for k in ('contrast','prefix_plus','prefix_minus')};rel={k:{}for k in ('one','prefix','contrast','normalization')}
                for t in ts:
                    cut=floor_scaled_power(t,dict(coefficient='1',power=theta));inside={};outside={}
                    for a in range(1,t+1):
                        for d in range(1,a+1):
                            if a%d==0:
                                dest=inside if d<=cut else outside;m=tuple(sorted((a,d)));dest[m]=dest.get(m,F(0))+F(a)**power
                    D=A.scale(A.add(inside,A.scale(outside,-1),L.constant(-1)),F(1,2));Z=A.add(inside,outside,L.constant(-1));contrasts[r,theta,power,t]=D
                    for name,p in [('contrast',D),('prefix_plus',A.add(prefix[t],D)),('prefix_minus',A.add(prefix[t],A.scale(D,-1)))]:sq[name].append(square(p))
                    for name,U in [('one',one),('prefix',prefix[t]),('contrast',D),('normalization',Z)]:
                        for a in range(1,t+1):
                            primitive={(1,):F(1),():F(1)}if a==1 else{(a,):F(a)**power};rel[name][a]=A.add(rel[name].get(a,{}),A.mul(primitive,U))
                squares.extend(sq[k]for k in ('contrast','prefix_plus','prefix_minus'));relations.extend([relation(dict(kind='unit')if a==1 else dict(kind='inverse_row',n=a),p)for a,p in sorted(rel[name].items())]for name in ('one','prefix','contrast','normalization'))
    if(len(squares),len(relations))!=(366,403):raise ValueError('complete fixed native scalar source family counts')
    blocks={}
    for r in ('parent','child'):
        ts=range(X,2*X)if r=='parent'else range(2*X,4*X);blocks['full_'+r]=[[A.serial(one)]+[A.serial(atom(k,t))for k in atoms]+[A.serial(contrasts[r,theta,power,t])for theta in ('1/3','1/2','2/3')for power in (-1,0,1)]for t in ts]
    delta={}
    for b in range(1,H+1):
        for a in range(1,b+1):
            q=F(J(b)*(1 if a==b else 2))
            if q:delta[a,b]=q
    D=32*X*X*_ceilroot(X,6);lhs=A.serial(A.add(L.constant(D),A.scale(delta,-1)))
    return dict(instance=dict(target='mu',horizon=H,lhs=lhs,square_groups=squares,relation_groups=relations),gram_blocks=blocks,storage_blocks=dict(kind='signed_storage_increment',child=blocks['full_child'],parent=blocks['full_parent'],child_multiplier='1',parent_multiplier='-4'),gram_specs=dict(full_child=15,full_parent=15,storage_K=15),math_source_counts=dict(local_operations=A.used,retained_cells=A.retained),math_only_legacy_source=True)
