"""Complete direct rational formal-identity probe; no polynomial construction.

Evaluation in Q x Q is a ring homomorphism. A producer result remains
unverified until the independent whole audit evaluates all source families.
"""
from fractions import Fraction as F
import json
import math
import time

SCHEMA='primitive-state-fresh-identity-probe-v1'
FLAGS=dict(global_bound_proved=False,RH_proved=False,universal_identity_proved=False,candidate_admitted=False,exact_admission=False,infeasibility_proved=False,identity_refuted=False,arithmetic_sign_values_substituted=False,scalar_budget_obligation_verified=False)
PROGRAM=dict(target='mu',q=6,C='32',claim='critical')
LAYOUT=dict(n_variables=1957,squares=366,relations=613,split_start=366,split_end=1592,slack_start=1592,slack_end=1597,gram_offset=1597,gram_order=['full_child','full_parent','storage_K'],gram_dimension=15,gram_pairs='upper triangle row-major')
SPEC=dict(scale_range=[1,9],maximum_horizon=35,prime=65537,assignment='explicit integer list of length4X-1; absolute value<=4096',baseline='all variables zero including u_1',representation='direct paired exact rational ring evaluation; no polynomials',coefficient_source='complete366 squares,613 signed relations,360 original Gram columns',storage='child K minus four parent K',offdiagonal='two times upper entry',target='unchanged critical q6 C32; rhs minus Delta',slacks='all five zero in necessary row',nonzero='unverified until independent complete replay',zero='NOT_REFUTED_BY_THIS_PROBE; never a universal theorem')
SOURCE_CONSTRUCTOR='fresh explicit-assignment paired exact rational fixed grammar; complete domains, factors and integer root cuts; no symbolic polynomial materialization'


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode('utf-8')

class Budget:
    def __init__(self,deadline,max_operations=100000000,max_cells=6000000,max_bits=4096):
        if type(deadline)not in (int,float)or not math.isfinite(deadline):raise ValueError('finite cooperative deadline')
        if type(max_operations)is not int or not 1<=max_operations<=100000000 or type(max_cells)is not int or not 1<=max_cells<=6000000 or type(max_bits)is not int or not 1<=max_bits<=4096:raise ValueError('strict bounded direct arithmetic caps')
        self.deadline=deadline;self.limit=max_operations;self.cell_limit=max_cells;self.bits=max_bits;self.operations=0;self.cells=0;self.maximum_bits=0
    def charge(self,n=1,cells=0):
        if type(n)is not int or n<0 or type(cells)is not int or cells<0:raise ValueError('nonnegative direct work')
        if time.monotonic()>self.deadline:raise TimeoutError('direct evaluation cooperative deadline')
        if n>self.limit-self.operations or cells>self.cell_limit-self.cells:raise OverflowError('direct work/cumulative scalar cell cap')
        self.operations+=n;self.cells+=cells
    def checked(self,q):
        if type(q)is not F:raise ValueError('exact Fraction operand')
        bits=max(abs(q.numerator).bit_length(),q.denominator.bit_length());self.maximum_bits=max(self.maximum_bits,bits)
        if bits>self.bits:raise OverflowError('direct rational operand/result bit cap')
        return q
    def rational(self,s):
        if type(s)is not str or not s or len(s)>2*self.bits+3 or any(c not in '-0123456789/'for c in s):raise ValueError('canonical bounded rational string')
        self.charge(1+len(s)//64,cells=1);parts=s.split('/');digits=1+self.bits*30103//100000
        if len(parts)>2 or any(not t or len(t.lstrip('-'))>digits for t in parts):raise OverflowError('bounded rational integer text preflight')
        try:n=int(parts[0]);d=int(parts[1])if len(parts)==2 else 1
        except ValueError:raise ValueError('valid rational integer')from None
        if d<=0:raise ValueError('positive denominator')
        if max(abs(n).bit_length(),d.bit_length())>self.bits:raise OverflowError('integer bit cap before Fraction allocation')
        q=F(n,d)
        if str(q)!=s:raise ValueError('canonical exact rational')
        return self.checked(q)
    def add(self,a,b):self.checked(a);self.checked(b);self.charge(cells=1);return self.checked(a+b)
    def mul(self,a,b):self.checked(a);self.checked(b);self.charge(cells=1);return self.checked(a*b)
    def counts(self):return dict(operations=self.operations,cumulative_scalar_cells=self.cells,maximum_rational_bits=self.maximum_bits)

class Algebra:
    def __init__(self,budget):self.b=budget;self.one=(F(1),F(1));self.zero=(F(0),F(0))
    def add(self,*ps):
        result=self.zero
        for p in ps:result=(self.b.add(result[0],p[0]),self.b.add(result[1],p[1]))
        return result
    def scale(self,p,q):
        q=F(q);self.b.checked(q);return(self.b.mul(p[0],q),self.b.mul(p[1],q))
    def mul(self,p,q):return(self.b.mul(p[0],q[0]),self.b.mul(p[1],q[1]))
    def total(self,ps):return self.add(*ps)


def factor_witness(n,budget):
    if type(n)is not int or not 1<=n<=35:raise ValueError('bounded factor domain')
    budget.charge();m=n;p=2;out=[]
    while p*p<=m:
        budget.charge(2);e=0
        while m%p==0:budget.charge(3);m//=p;e+=1
        if e:out.append((p,e));budget.charge(cells=2)
        p+=1
    if m>1:out.append((m,1));budget.charge(cells=2)
    return tuple(out)

def floor_power(n,theta,budget):
    a,b=F(theta).numerator,F(theta).denominator
    if type(n)is not int or not 1<=n<=35 or not 1<=a<b<=6:raise ValueError('fixed rational-root cut domain')
    budget.charge(a);target=n**a;lo=0;hi=n+1
    while lo+1<hi:
        mid=(lo+hi)//2;budget.charge(b+2)
        if mid**b<=target:lo=mid
        else:hi=mid
    return lo

def ceil_root(X,q,budget):
    if type(X)is not int or not 1<=X<=9 or type(q)is not int or not 1<=q<=6:raise ValueError('bounded exact ceil-root')
    r=1
    while True:
        budget.charge(q)
        if r**q>=X:return r
        r+=1

FACTOR_ORDER=[('1/2','one'),('1/2','a'),('1/3','one'),('1/2','b'),('2/3','one'),('1/3','a'),('1/3','b'),('1/2','a_minus_b'),('1/4','one'),('2/3','b'),('1/4','a'),('2/3','a'),('1/4','b'),('1/5','one'),('1/3','a_minus_b'),('1/4','a_minus_b'),('1/6','one'),('2/5','one'),('3/4','one'),('1/5','b'),('1/5','a'),('2/3','a_minus_b'),('3/5','one'),('2/5','a'),('3/4','a'),('2/5','b'),('1/6','b'),('3/4','b'),('1/6','a'),('1/5','a_minus_b'),('2/5','a_minus_b'),('3/4','a_minus_b'),('3/5','a'),('3/5','b'),('1/6','a_minus_b'),('4/5','one'),('4/5','a'),('4/5','b'),('3/5','a_minus_b'),('5/6','one'),('4/5','a_minus_b'),('5/6','b'),('5/6','a'),('5/6','a_minus_b')]

def column_pairs(program,X,assignment,budget,checkpoint=None):
    if program!=dict(target='mu',q=6,C='32',claim='critical')or type(X)is not int or not 1<=X<=9 :raise ValueError('fixed bounded critical native source')
    assignment=validate_assignment(X,assignment)
    H=4*X-1;budget.charge(2*(1000*H**3+10000))
    A=Algebra(budget);one=A.one;zero=A.zero;squares=[];relations=[];variables=[zero]+[(F(v),F(0))for v in assignment]
    budget.charge(H,cells=2*H)
    V=lambda n:variables[n]
    factors={n:factor_witness(n,budget)for n in range(1,H+1)}
    sf={n:int(all(e==1 for p,e in factors[n]))for n in factors}
    prime=lambda n:factors.get(n)==((n,1),)
    prefix=[zero]
    for n in range(1,H+1):prefix.append(A.add(prefix[-1],V(n)))
    def K(Y,t):return max(0,2*Y-max(Y,t))
    def J(t):return K(2*X,t)-4*K(X,t)
    def rowmass(i):
        lo=max(2*X,i);return sum(range(lo,4*X))
    def region(r,i):return r=='all'or r=='head'and i<=2*X or r=='tail'and i>2*X or r=='initial'and i<X or r=='parent'and X<=i<2*X or r=='child'and 2*X<=i<4*X
    def square(p,w=1):return A.scale(A.mul(p,p),w)
    def relation(spec,m):return A.mul(primitive(spec),m)
    def weight(w,i):return 1 if w=='one'else X if w=='X'else X*X if w=='X2'else J(i)if w=='defect_kernel'else rowmass(i)
    # Exactly the original52 grouped squares, including empty fixed positions.
    squares.append([square(one,X*X*ceil_root(X,6,budget))])
    for r in ('all','head','tail'):
        budget.charge()
        for w in ('one','X','X2'):squares.append([square(V(i),weight(w,i))for i in range(1,H+1)if region(r,i)])
    for r in ('all','initial','parent','child'):
        budget.charge()
        for w in ('one','X'):squares.append([square(prefix[i],weight(w,i))for i in range(1,H+1)if region(r,i)])
    for domain in ('all','coprime','noncoprime','divides'):
        budget.charge()
        for sign in (1,-1):
            budget.charge()
            for w in ('one','child_kernel','abs_defect_kernel'):
                budget.charge()
                group=[]
                for a in range(1,H+1):
                    budget.charge()
                    for b in range(a+1,H+1):
                        budget.charge()
                        if domain=='coprime'and math.gcd(a,b)!=1 or domain=='noncoprime'and math.gcd(a,b)==1 or domain=='divides'and b%a:continue
                        group.append(square(A.add(V(a),A.scale(V(b),sign)),1 if w=='one'else K(2*X,b)if w=='child_kernel'else abs(J(b))))
                squares.append(group)
    for r in ('all','head','tail'):
        budget.charge()
        for w in ('one','X'):squares.append([square(A.add(*(V(d)for d in range(1,i+1)if i%d==0)),weight(w,i))for i in range(2,H+1)if region(r,i)])
    for domain in ('all','coprime'):
        budget.charge()
        for w in ('one','child_kernel'):squares.append([square(A.mul(V(a),V(b)),1 if w=='one'else K(2*X,b))for a in range(1,H+1)for b in range(a+1,H+1)if domain=='all'or math.gcd(a,b)==1])
    specs={f:[]for f in ('norm','prime_power','squarefree_zero','inverse_row','coprime_product','gcd_product','unit')};specs['unit']=[dict(kind='unit')]
    for n in range(1,H+1):
        budget.charge()
        specs['norm'].append(dict(kind='norm',n=n,factors=factors[n]))
        if len(factors[n])==1:p,e=factors[n][0];specs['prime_power'].append(dict(kind='prime_power',p=p,e=e))
        if not sf[n]:specs['squarefree_zero'].append(dict(kind='squarefree_zero',n=n))
        if n>=2:specs['inverse_row'].append(dict(kind='inverse_row',n=n))
    for a in range(1,H+1):
        budget.charge()
        for b in range(a,H+1):
            budget.charge()
            specs['gcd_product'].append(dict(kind='gcd_product',a=a,b=b,factors_a=factors[a],factors_b=factors[b]))
            if a>=2 and a*b<=H and math.gcd(a,b)==1:specs['coprime_product'].append(dict(kind='coprime_product',a=a,b=b))
    def anchor(s):return s['a']*s['b']if s['kind']=='coprime_product'else s['b']if s['kind']=='gcd_product'else s['p']**s['e']if s['kind']=='prime_power'else s.get('n',1)
    primitive_cache={}
    def primitive(spec):
        key=tuple((k,tuple(tuple(x)for x in v)if type(v)is list else v)for k,v in sorted(spec.items()));budget.charge(1+len(key))
        if key in primitive_cache:return primitive_cache[key]
        kind=spec['kind']
        if kind=='unit':p=A.add(V(1),A.scale(one,-1))
        elif kind=='norm':p=A.add(A.mul(V(spec['n']),V(spec['n'])),A.scale(one,-sf[spec['n']]))
        elif kind=='prime_power':p=A.add(V(spec['p']**spec['e']),one)if spec['e']==1 else V(spec['p']**spec['e'])
        elif kind=='squarefree_zero':p=V(spec['n'])
        elif kind=='inverse_row':
            n=spec['n'];budget.charge(n);p=A.add(*(V(d)for d in range(1,n+1)if n%d==0),A.scale(one,-int(n==1)))
        elif kind=='coprime_product':p=A.add(A.mul(V(spec['a']),V(spec['b'])),A.scale(V(spec['a']*spec['b']),-1))
        elif kind=='gcd_product':
            a,b=spec['a'],spec['b'];g=math.gcd(a,b);fa=dict(factors[a]);fb=dict(factors[b]);budget.charge(4+len(fa)+len(fb));compatible=all(fa[p]==fb[p]for p in fa.keys()&fb.keys());c=sf[g]*int(compatible);p=A.add(A.mul(V(a),V(b)),A.scale(A.mul(V(a//g),V(b//g)),-c))
        else:raise ValueError('unsupported primitive source')
        primitive_cache[key]=p;budget.charge(cells=2);return p
    def base_rel(f,r,w,m):
        group=[]
        for spec in specs[f]:
            budget.charge()
            i=anchor(spec)
            if region(r,i):group.append(relation(spec,A.scale(one if m=='one'else V(i)if m=='anchor'else prefix[H]if m=='global_prefix'else prefix[i],weight(w,i))))
        relations.append(group)
    for f in ('norm','prime_power','squarefree_zero','inverse_row','coprime_product'):
        budget.charge()
        for r in ('all','head','tail'):
            budget.charge()
            for w in ('one','X','defect_kernel','child_rowmass'):
                budget.charge()
                for m in ('one','anchor','prefix'):base_rel(f,r,w,m)
    for r in ('all','head','tail'):
        budget.charge()
        for w in ('one','X','defect_kernel','child_rowmass'):base_rel('gcd_product',r,w,'one')
    for m in ('one','anchor','global_prefix'):base_rel('unit','all','one',m)
    # Exact signed masks and growing-prime sources; no AST archive/compiler hash.
    atoms=('prefix','half','even','mod3one','prime')
    def atom(kind,t):return prefix[t]if kind=='prefix'else prefix[t//2]if kind=='half'else A.total([V(n)for n in range(1,t+1)if n%2==0])if kind=='even'else A.total([V(n)for n in range(1,t+1)if n%3==1])if kind=='mod3one'else A.total([V(n)for n in range(1,t+1)if prime(n)])
    signed=[(r,a,None,1,None)for r in ('parent','child')for a in atoms]
    signed.extend((r,a,b,sign,None)for r in ('parent','child')for i,a in enumerate(atoms)for b in atoms[i+1:]for sign in (1,-1))
    signed.extend((r,None,None,1,k)for r in ('parent','child')for k in (2,3))
    for r,a,b,sign,k in signed:
        budget.charge()
        group=[]
        for t in range(X,2*X)if r=='parent'else range(2*X,4*X):
            budget.charge()
            p=atom(a,t)if k is None and b is None else A.add(atom(a,t),A.scale(atom(b,t),sign))if k is None else A.add(*(V(j)for p in range(2,ceil_root(X,k,budget)+1)if prime(p)for j in range(1,t//p+1)if math.gcd(j,p)==1))
            group.append(square(p))
        squares.append(group)
    for f in ('norm_core','gcd_pair','prime_transport'):
        budget.charge()
        for r in ('all','head','tail'):
            budget.charge()
            for m in ('product','difference'):
                budget.charge()
                for w in ('one','defect_kernel'):
                    budget.charge()
                    group=[]
                    for a in range(1,H+1):
                        budget.charge()
                        for b in range(1 if f=='prime_transport'else a,H+1):
                            budget.charge()
                            i=b
                            if f=='prime_transport':
                                if not prime(a)or a*b>H or math.gcd(a,b)!=1:continue
                                i=a*b;spec=dict(kind='coprime_product',a=a,b=b);p=A.mul(V(a),V(b))if m=='product'else A.mul(V(b),A.add(prefix[i],A.scale(prefix[b],-1)))
                            else:
                                g=math.gcd(a,b);u,v=(a//g,b//g)if f=='norm_core'else(a,b);spec=dict(kind='norm',n=g,factors=factors[g])if f=='norm_core'else dict(kind='gcd_product',a=a,b=b,factors_a=factors[a],factors_b=factors[b]);p=A.mul(V(u),V(v))if m=='product'else A.mul(A.add(V(u),A.scale(V(v),-1)),A.add(V(u),A.scale(V(v),-1)))
                            if region(r,i):group.append(relation(spec,A.scale(p,1 if w=='one'else J(i))))
                    relations.append(group)
    #44 ordered factor blocks; every ordered coprime pair and complement retained.
    for theta,kernel in FACTOR_ORDER:
        budget.charge()
        cut=floor_power(H,theta,budget);normal=F(1,H**(0 if kernel=='one'else 1));parts=[]
        for inside in (True,False):
            budget.charge()
            B=zero;C=zero;terms=[]
            for a in range(1,H+1):
                budget.charge()
                for b in range(1,H//a+1):
                    budget.charge()
                    if math.gcd(a,b)!=1 or(a<=cut)!=inside:continue
                    q=F(1 if kernel=='one'else a if kernel=='a'else b if kernel=='b'else a-b);B=A.add(B,A.scale(A.mul(V(a),V(b)),q));C=A.add(C,A.scale(V(a*b),q));terms.append((dict(kind='coprime_product',a=a,b=b),q))
            B=A.scale(B,normal);C=A.scale(C,normal);T=A.add(B,A.scale(C,-1));plus=A.add(B,C);parts.append((B,C,terms,T,plus))
        squares.extend([[square(part[i])for part in parts]for i in (0,1)])
        for i in (4,3):relations.append([relation(spec,A.scale(part[i],normal*q))for part in parts for spec,q in part[2]])
        contrast=A.add(parts[0][1],A.scale(parts[1][1],-1));squares.extend([[square(A.add(prefix[H],contrast))],[square(A.add(prefix[H],A.scale(contrast,-1)))]] )
    # Complete divisor-localizer sources, with allordered inverse pairs.
    for r in ('parent','child'):
        budget.charge()
        ts=range(X,2*X)if r=='parent'else range(2*X,4*X)
        for power in (-1,0,1):
            budget.charge()
            sq={k:[]for k in ('plain','squarefree_plain','modulated','plus','minus')};norms={};inverse={}
            for t in ts:
                budget.charge()
                weights={a:F(a,t)**power for a in range(1,t+1)}
                for d in range(1,t+1):
                    budget.charge()
                    p=A.total([A.scale(V(a),weights[a])for a in range(d,t+1,d)]);mod=A.mul(V(d),p)
                    for form,poly in [('plain',p),('squarefree_plain',p),('modulated',mod),('plus',A.add(p,mod)),('minus',A.add(p,A.scale(mod,-1)))]:sq[form].append(square(poly,sf[d]if form=='squarefree_plain'else 1))
                    norms[d]=A.add(norms.get(d,zero),A.mul(p,p))
                for a in range(1,t+1):
                    budget.charge()
                    for b in range(1,t+1):
                        budget.charge()
                        g=math.gcd(a,b);inverse[g]=A.add(inverse.get(g,zero),A.scale(A.mul(V(a),V(b)),weights[a]*weights[b]))
            squares.extend(sq[k]for k in ('plain','squarefree_plain','modulated','plus','minus'));relations.append([relation(dict(kind='norm',n=d,factors=factors[d]),p)for d,p in sorted(norms.items())]);relations.append([relation(dict(kind='unit')if g==1 else dict(kind='inverse_row',n=g),p)for g,p in sorted(inverse.items())])
    #18 cells retain exact inclusive floor cut and full complement. State usesD.
    contrasts={}
    for r in ('parent','child'):
        budget.charge()
        ts=range(X,2*X)if r=='parent'else range(2*X,4*X)
        for theta in ('1/3','1/2','2/3'):
            budget.charge()
            for power in (-1,0,1):
                budget.charge()
                sq={k:[]for k in ('contrast','prefix_plus','prefix_minus')};rel={k:{}for k in ('one','prefix','contrast','normalization')}
                for t in ts:
                    budget.charge()
                    cut=floor_power(t,theta,budget);inside=zero;outside=zero
                    for a in range(1,t+1):
                        budget.charge()
                        for d in range(1,a+1):
                            budget.charge()
                            if a%d==0:
                                term=A.scale(A.mul(V(a),V(d)),F(a)**power)
                                if d<=cut:inside=A.add(inside,term)
                                else:outside=A.add(outside,term)
                    D=A.scale(A.add(inside,A.scale(outside,-1),A.scale(one,-1)),F(1,2));Z=A.add(inside,outside,A.scale(one,-1));contrasts[r,theta,power,t]=D
                    for name,p in [('contrast',D),('prefix_plus',A.add(prefix[t],D)),('prefix_minus',A.add(prefix[t],A.scale(D,-1)))]:sq[name].append(square(p))
                    for name,U in [('one',one),('prefix',prefix[t]),('contrast',D),('normalization',Z)]:
                        budget.charge()
                        for a in range(1,t+1):
                            budget.charge()
                            primitive_value=A.add(V(1),one)if a==1 else A.scale(V(a),F(a)**power);rel[name][a]=A.add(rel[name].get(a,zero),A.mul(primitive_value,U))
                squares.extend(sq[k]for k in ('contrast','prefix_plus','prefix_minus'));relations.extend([relation(dict(kind='unit')if a==1 else dict(kind='inverse_row',n=a),p)for a,p in sorted(rel[name].items())]for name in ('one','prefix','contrast','normalization'))
    if(len(squares),len(relations))!=(366,403):raise ValueError('complete fixed native scalar source family counts')
    blocks={}
    for r in ('parent','child'):
        budget.charge()
        ts=range(X,2*X)if r=='parent'else range(2*X,4*X);blocks['full_'+r]=[[one]+[atom(k,t)for k in atoms]+[contrasts[r,theta,power,t]for theta in ('1/3','1/2','2/3')for power in (-1,0,1)]for t in ts]
    # Complete primitive/state suffix contraction, same finite Fubini identity.
    raw_relations=[A.total(group)for group in relations]
    suffix={}
    for r in ('parent','child'):
        budget.charge()
        ts=list(range(X,2*X)if r=='parent'else range(2*X,4*X));running=[zero]*15
        for t,state in reversed(list(zip(ts,blocks['full_'+r]))):
            budget.charge()
            running=[A.add(a,b)for a,b in zip(running,state)];suffix[r,t]=running
    for family in ('unit','norm','prime_power','squarefree_zero','inverse_row','coprime_product','gcd_product'):
        budget.charge()
        for r in ('parent','child'):
            budget.charge()
            ts=list(range(X,2*X)if r=='parent'else range(2*X,4*X))
            for i in range(15):
                budget.charge()
                total=zero
                for spec in specs[family]:
                    budget.charge()
                    budget.charge();a=anchor(spec)
                    if a<=ts[-1]:total=A.add(total,A.mul(primitive(spec),suffix[r,max(ts[0],a)][i]))
                raw_relations.append(total)
    if len(raw_relations)!=613:raise ValueError('complete direct613 relation groups')
    columns=[A.total(group)for group in squares]
    for p in raw_relations:columns.extend([p,A.scale(p,-1)])
    columns.extend([zero]*5)
    for name in ('full_child','full_parent','storage_K'):
        budget.charge()
        regions=[('full_child',1)]if name=='full_child'else[('full_parent',1)]if name=='full_parent'else[('full_child',1),('full_parent',-4)]
        for i in range(15):
            budget.charge()
            for j in range(i,15):
                budget.charge()
                total=zero
                for r,sign in regions:
                    budget.charge()
                    for state in blocks[r]:total=A.add(total,A.scale(A.mul(state[i],state[j]),sign*(1 if i==j else 2)))
                columns.append(total)
    if len(columns)!=1957:raise ValueError('complete original1957 column layout')
    delta=A.add(*(A.mul(prefix[t],prefix[t])for t in range(2*X,4*X)),*(A.scale(A.mul(prefix[t],prefix[t]),-4)for t in range(X,2*X)))
    D=32*X*X*ceil_root(X,6,budget);target=A.add(A.scale(one,D),A.scale(delta,-1))
    return dict(columns=columns,target=target,states=blocks,raw_relations=raw_relations,primitive_cache_entries=len(primitive_cache),factor_witnesses=factors)

DOMAIN_POLICY=dict(per_scalar_pass='1000*H^3+10000 charged before domain construction',paired_passes=2,rational_arithmetic='each add or multiply charged before allocation; cumulative scalar cells',temporary_bits=8193,result_bits=4096,all_domain_reserves_shared_with_arithmetic=True)


def validate_assignment(X,assignment):
    if type(X)is not int or not 1<=X<=9 or type(assignment)is not list or len(assignment)!=4*X-1 or any(type(v)is not int or abs(v)>4096 for v in assignment):raise ValueError('bounded explicit integer formal assignment')
    return list(assignment)


def preflight(candidate_vector,program,*,X,assignment,prime=65537,case_index=0):
    """Metadata only; numerical validation and evaluation share case budget."""
    if program!=PROGRAM or prime!=65537 or type(prime)is not int or type(case_index)is not int or not 0<=case_index<=1:raise ValueError('fixed bounded fresh program/prime/case')
    assignment=validate_assignment(X,assignment)
    if type(candidate_vector)is not list or len(candidate_vector)!=1957:raise ValueError('complete original1957 input')
    return dict(schema='primitive-state-fresh-identity-probe-plan-v1',case_index=case_index,program=program,X=X,H=4*X-1,prime=prime,assignment=assignment,candidate_vector=list(candidate_vector),layout=LAYOUT,spec=SPEC,source_constructor=SOURCE_CONSTRUCTOR,domain_policy=DOMAIN_POLICY,**FLAGS)


def probe(candidate_vector,plan,*,deadline,max_operations=100000000,max_cells=6000000,max_coefficient_bits=4096,max_receipt_bytes=1048576,checkpoint=None):
    budget=Budget(deadline,max_operations,max_cells,max_coefficient_bits)
    out=dict(schema=SCHEMA,status='UNKNOWN',complete=False,program=plan.get('program'),source_constructor=SOURCE_CONSTRUCTOR,case_index=plan.get('case_index'),X=plan.get('X'),H=plan.get('H'),prime=65537,spec=SPEC,domain_policy=DOMAIN_POLICY,limits=dict(max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits,max_receipt_bytes=max_receipt_bytes),**FLAGS)
    try:
        if type(max_receipt_bytes)is not int or not 4096<=max_receipt_bytes<=1048576:raise ValueError('bounded direct receipt')
        if plan!=preflight(candidate_vector,PROGRAM,X=plan['X'],assignment=plan['assignment'],prime=65537,case_index=plan['case_index']):raise ValueError('unchanged complete direct mathematical plan')
        # Trial division is deterministic; no probabilistic primality claim.
        for d in range(2,math.isqrt(65537)+1):
            budget.charge()
            if 65537%d==0:raise ValueError('fixed modulus not prime')
        p=65537;weights=[]
        for s in candidate_vector:
            q=budget.rational(s)
            if q.denominator%p==0:raise ValueError('candidate denominator not invertible; no alternate prime')
            budget.charge(2*p.bit_length());weights.append(q.numerator%p*pow(q.denominator%p,p-2,p)%p)
        X=plan['X'];H=plan['H']
        if checkpoint:checkpoint(dict(phase='direct_columns_started',counts=budget.counts(),**FLAGS))
        data=column_pairs(PROGRAM,X,plan['assignment'],budget,checkpoint);columns=data['columns'];row=[];values=[];baselines=[];body=[0,0];mod_cache={}
        def mod(q):
            budget.checked(q)
            if q.denominator%p==0:raise ValueError('source/row denominator not invertible; no alternate prime')
            key=(q.numerator,q.denominator)
            if key not in mod_cache:budget.charge(2*p.bit_length(),cells=1);mod_cache[key]=q.numerator%p*pow(q.denominator%p,p-2,p)%p
            return mod_cache[key]
        for i,(a,b)in enumerate(columns):
            budget.charge(4,cells=3);row.append(budget.add(a,-b));values.append(str(a));baselines.append(str(b));body[0]=(body[0]+mod(a)*weights[i])%p;body[1]=(body[1]+mod(b)*weights[i])%p
        target=data['target'];rhs=budget.add(target[0],-target[1]);target_mod=[mod(q)for q in target];residual=[(target_mod[i]-body[i])%p for i in range(2)];difference=(residual[0]-residual[1])%p;row_dot=0
        for q,w in zip(row,weights):budget.charge(2);row_dot=(row_dot+mod(q)*w)%p
        if(mod(rhs)-row_dot)%p!=difference:raise ValueError('complete exact row/modular candidate residual mismatch')
        feedback=dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,entries=[dict(index=i,coefficient=str(q))for i,q in enumerate(row)if q],rhs=str(rhs),zero_coordinates=[i for i,q in enumerate(row)if not q],scope='necessary constraint for this universal formal nonconstant identity; not a sufficient identity or cone condition',X=X,assignment=list(plan['assignment']),layout=LAYOUT)
        states={name:[[[str(a),str(b)]for a,b in state]for state in rows]for name,rows in data['states'].items()}
        out.update(status='UNVERIFIED_COUNTEREXAMPLE'if difference else'NOT_REFUTED_BY_THIS_PROBE',complete=True,assignment=list(plan['assignment']),baseline=[0]*H,column_values=values,column_baselines=baselines,target_exact_values=list(map(str,target)),target_values=target_mod,body_values=body,residual_values=residual,nonconstant_difference=difference,feedback_row=feedback,feedback_row_dot_mod_prime=row_dot,feedback_rhs_mod_prime=mod(rhs),regional_states=states,factor_witnesses={str(n):[list(pair)for pair in pairs]for n,pairs in data['factor_witnesses'].items()},coverage=dict(square_groups=366,signed_relation_groups=613,split_relation_coordinates=1226,constant_slacks=5,gram_columns=360,regional_rows=3*X,atoms_per_row=15,primitive_families=['unit','norm','prime_power','squarefree_zero','inverse_row','coprime_product','gcd_product'],factor_blocks=44,complete_domains=True),slack_coordinates_excluded=list(range(1592,1597)),source_denominators_invertible=True,prime_checked=True,complete_direct_source_evaluated=True,source_semantics_independently_verified=False)
        budget.charge(len(encoded(out))//64+1)
        if len(encoded(out))>max_receipt_bytes:raise OverflowError('complete direct receipt byte cap')
        if checkpoint:checkpoint(dict(phase='direct_probe_evaluated',counts=budget.counts(),**FLAGS))
    except (ValueError,OverflowError,TimeoutError,KeyError,TypeError,ZeroDivisionError)as error:
        # No partial vector/row is usable after any gate fails.
        out={k:out[k]for k in ['schema','program','source_constructor','case_index','X','H','prime','spec','domain_policy','limits',*FLAGS]};out.update(status='UNKNOWN',complete=False,reason=str(error),error_type=type(error).__name__,nonconstant_difference=None,feedback_row=None)
    out['counts']=budget.counts()
    if len(encoded(out))>max_receipt_bytes and max_receipt_bytes>=4096:
        out={k:out[k]for k in ['schema','program','source_constructor','case_index','X','H','prime','spec','domain_policy','limits','counts',*FLAGS]};out.update(status='UNKNOWN',complete=False,reason='direct final receipt byte cap',nonconstant_difference=None,feedback_row=None)
    return out
