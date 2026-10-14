"""Independent direct rational finite FORMAL identity endpoint evaluation.

Assignment and all-zero baseline are evaluated in separate scalar passes.
No formal polynomial, source hash, Mobius assignment or numerical solver is used.
"""
from fractions import Fraction as F
import math
import time
import json
from check_primitive_state_uniform_native_source import FACTOR_ORDER
from check_primitive_state_uniform_identity_probe import FLAGS,LAYOUT

PROGRAM=dict(target='mu',q=6,C='32',claim='critical')
FAMILIES=('unit','norm','prime_power','squarefree_zero','inverse_row','coprime_product','gcd_product')

def require(x,message):
    if not x:raise ValueError(message)

class Budget:
    def __init__(self,deadline,max_operations=200000000,max_bits=4096):
        require(type(deadline)in(int,float)and math.isfinite(deadline),'finite direct deadline')
        require(type(max_operations)is int and 0<max_operations<=200000000 and type(max_bits)is int and 0<max_bits<=4096,'strict direct rational caps')
        self.deadline=deadline;self.cap=max_operations;self.bits=max_bits;self.operations=0;self.cells=0;self.maximum_bits=0;self.max_cells=6000000
    def tick(self,n=1,cells=0):
        if n>self.cap-self.operations:raise OverflowError('independent direct aggregate work cap')
        self.operations+=n;self.cells+=cells
        if self.cells>self.max_cells:raise OverflowError('independent direct cumulative cells')
        if time.monotonic()>self.deadline:raise TimeoutError('independent direct deadline')
    def check(self,q):
        q=F(q)
        self.maximum_bits=max(self.maximum_bits,abs(q.numerator).bit_length(),q.denominator.bit_length())
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>self.bits:raise OverflowError('independent direct rational bits')
        return q
    def add(self,a,b):self.tick(cells=1);self.check(a);self.check(b);return self.check(a+b)
    def mul(self,a,b):self.tick(cells=1);self.check(a);self.check(b);return self.check(a*b)
    def sum(self,values):
        out=F(0)
        for q in values:out=self.add(out,q)
        return out
    def parse(self,text):
        require(type(text)is str and 0<len(text)<=2*self.bits+3,'bounded rational text');self.tick(1+len(text)//64)
        require(all(c in '-0123456789/'for c in text),'rational text syntax')
        parts=text.split('/');require(len(parts)<=2 and all(p and p!='-'for p in parts),'rational components')
        digits=1+self.bits*30103//100000
        if any(len(p.lstrip('-'))>digits for p in parts):raise OverflowError('rational decimal preallocation cap')
        ints=[int(p)for p in parts]
        if any(abs(n).bit_length()>self.bits for n in ints):raise OverflowError('rational integer preallocation cap')
        require(len(ints)==1 or ints[1]>0,'positive rational denominator');q=F(*ints);require(str(q)==text,'canonical rational');return self.check(q)

def floor_root(n,power,b):
    p=F(power);b.tick();lo=0;hi=n+1;rhs=n**p.numerator
    while hi-lo>1:
        mid=(lo+hi)//2;b.tick()
        if mid**p.denominator<=rhs:lo=mid
        else:hi=mid
    return lo

def ceil_root(n,k,b):
    lo=0;hi=n+1
    while hi-lo>1:
        mid=(lo+hi)//2;b.tick()
        if mid**k<n:lo=mid
        else:hi=mid
    return hi

def factor(n,b):
    d=2;out={}
    while d*d<=n:
        b.tick();e=0
        while n%d==0:n//=d;e+=1;b.tick()
        if e:out[d]=e
        d+=1
    if n>1:out[n]=1
    return out

def evaluate_pass(X,values,b):
    """Complete scalar recipe declarations, in the licensed original order."""
    H=4*X-1;require(len(values)==H,'all formal coordinates')
    # Aggregate domain/predicate/weight construction reserve, charged once per
    # scalar pass. Includes rejected divisor/mask/coprime indices, bounded
    # small integer powers, and anchor/spec book-keeping; no helper reset.
    b.tick(1000*H**3+10000); u=[F(0)]+[b.check(v)for v in values]
    fac={n:factor(n,b)for n in range(1,H+1)};sf={n:int(all(e==1 for e in f.values()))for n,f in fac.items()};prime=lambda n:fac.get(n)=={n:1}
    pref=[F(0)]
    for n in range(1,H+1):pref.append(b.add(pref[-1],u[n]))
    def K(Y,t):b.tick();return max(0,2*Y-max(Y,t))
    def J(t):return K(2*X,t)-4*K(X,t)
    def region(r,n):b.tick();return r=='all'or r=='head'and n<=2*X or r=='tail'and n>2*X or r=='initial'and n<X or r=='parent'and X<=n<2*X or r=='child'and 2*X<=n<4*X
    def weight(w,n):return F(1 if w=='one'else X if w=='X'else X*X if w=='X2'else J(n)if w=='defect_kernel'else sum(range(max(2*X,n),4*X)))
    def square(q,w=1):return b.mul(F(w),b.mul(q,q))
    def R(spec):
        b.tick();kind=spec[0]
        if kind=='unit':return b.add(u[1],-1)
        if kind=='norm':n=spec[1];return b.add(square(u[n]),-sf[n])
        if kind=='prime_power':p,e=spec[1:];return b.add(u[p**e],int(e==1))
        if kind=='squarefree_zero':return u[spec[1]]
        if kind=='inverse_row':n=spec[1];return b.sum(u[d]for d in range(1,n+1)if n%d==0)
        a,c=spec[1:]
        if kind=='coprime_product':return b.add(b.mul(u[a],u[c]),-u[a*c])
        g=math.gcd(a,c);fa,fc=fac[a],fac[c];shared=set(fa)&set(fc)
        indicator=int(all(fa[p]==fc[p]==1 for p in shared))
        return b.add(b.mul(u[a],u[c]),-b.mul(F(indicator),b.mul(u[a//g],u[c//g])))
    def specs(t):
        out={f:[]for f in FAMILIES};out['unit']=[('unit',)]
        for n in range(1,t+1):
            b.tick();out['norm'].append(('norm',n))
            if len(fac[n])==1:p,e=next(iter(fac[n].items()));out['prime_power'].append(('prime_power',p,e))
            if not sf[n]:out['squarefree_zero'].append(('squarefree_zero',n))
            if n>=2:out['inverse_row'].append(('inverse_row',n))
        for a in range(1,t+1):
            for c in range(a,t+1):
                b.tick();out['gcd_product'].append(('gcd_product',a,c))
                if a>=2 and a*c<=t and math.gcd(a,c)==1:out['coprime_product'].append(('coprime_product',a,c))
        return out
    domain=specs(H)
    def anchor(s):return s[1]*s[2]if s[0]=='coprime_product'else s[2]if s[0]=='gcd_product'else s[1]**s[2]if s[0]=='prime_power'else s[1]if len(s)>1 else 1
    sq=[F(X*X*ceil_root(X,6,b))];rel=[]
    for r in ('all','head','tail'):
        for w in ('one','X','X2'):sq.append(b.sum(square(u[i],weight(w,i))for i in range(1,H+1)if region(r,i)))
    for r in ('all','initial','parent','child'):
        for w in ('one','X'):sq.append(b.sum(square(pref[i],weight(w,i))for i in range(1,H+1)if region(r,i)))
    for dom in ('all','coprime','noncoprime','divides'):
        for sign in (1,-1):
            for w in ('one','child_kernel','abs_defect_kernel'):
                terms=[]
                for a in range(1,H+1):
                    for c in range(a+1,H+1):
                        b.tick()
                        if dom=='coprime'and math.gcd(a,c)!=1 or dom=='noncoprime'and math.gcd(a,c)==1 or dom=='divides'and c%a:continue
                        terms.append(square(b.add(u[a],b.mul(F(sign),u[c])),1 if w=='one'else K(2*X,c)if w=='child_kernel'else abs(J(c))))
                sq.append(b.sum(terms))
    for r in ('all','head','tail'):
        for w in ('one','X'):sq.append(b.sum(square(b.sum(u[d]for d in range(1,i+1)if i%d==0),weight(w,i))for i in range(2,H+1)if region(r,i)))
    for dom in ('all','coprime'):
        for w in ('one','child_kernel'):sq.append(b.sum(square(b.mul(u[a],u[c]),1 if w=='one'else K(2*X,c))for a in range(1,H+1)for c in range(a+1,H+1)if dom=='all'or math.gcd(a,c)==1))
    def base_rel(f,r,w,m):
        return b.sum(b.mul(R(s),b.mul(weight(w,anchor(s)),F(1)if m=='one'else u[anchor(s)]if m=='anchor'else pref[H]if m=='global_prefix'else pref[anchor(s)]))for s in domain[f]if region(r,anchor(s)))
    for f in FAMILIES[1:6]:
        for r in ('all','head','tail'):
            for w in ('one','X','defect_kernel','child_rowmass'):
                for m in ('one','anchor','prefix'):rel.append(base_rel(f,r,w,m))
    for r in ('all','head','tail'):
        for w in ('one','X','defect_kernel','child_rowmass'):rel.append(base_rel('gcd_product',r,w,'one'))
    for m in ('one','anchor','global_prefix'):rel.append(base_rel('unit','all','one',m))
    atoms=('prefix','half','even','mod3one','prime')
    def atom(k,t):return pref[t]if k=='prefix'else pref[t//2]if k=='half'else b.sum(u[n]for n in range(1,t+1)if n%2==0)if k=='even'else b.sum(u[n]for n in range(1,t+1)if n%3==1)if k=='mod3one'else b.sum(u[n]for n in range(1,t+1)if prime(n))
    signed=[(r,a,None,1,None)for r in ('parent','child')for a in atoms]+[(r,a,c,s,None)for r in ('parent','child')for i,a in enumerate(atoms)for c in atoms[i+1:]for s in (1,-1)]+[(r,None,None,1,k)for r in ('parent','child')for k in (2,3)]
    for r,a,c,s,k in signed:
        sq.append(b.sum(square(atom(a,t)if k is None and c is None else b.add(atom(a,t),b.mul(F(s),atom(c,t)))if k is None else b.sum(u[j]for p in range(2,ceil_root(X,k,b)+1)if prime(p)for j in range(1,t//p+1)if math.gcd(j,p)==1))for t in(range(X,2*X)if r=='parent'else range(2*X,4*X))))
    for f in ('norm_core','gcd_pair','prime_transport'):
        for r in ('all','head','tail'):
            for m in ('product','difference'):
                for w in ('one','defect_kernel'):
                    terms=[]
                    for a in range(1,H+1):
                        for c in range(1 if f=='prime_transport'else a,H+1):
                            b.tick();i=c
                            if f=='prime_transport':
                                if not prime(a)or a*c>H or math.gcd(a,c)!=1:continue
                                i=a*c;s=('coprime_product',a,c);q=b.mul(u[a],u[c])if m=='product'else b.mul(u[c],b.add(pref[i],-pref[c]))
                            else:
                                g=math.gcd(a,c);v,z=(a//g,c//g)if f=='norm_core'else(a,c);s=('norm',g)if f=='norm_core'else('gcd_product',a,c);q=b.mul(u[v],u[z])if m=='product'else square(b.add(u[v],-u[z]))
                            if region(r,i):terms.append(b.mul(R(s),b.mul(q,F(1 if w=='one'else J(i)))))
                    rel.append(b.sum(terms))
    for theta,kernel in FACTOR_ORDER:
        cut=floor_root(H,theta,b);normal=F(1,H**int(kernel!='one'));parts=[]
        for inside in (True,False):
            bs=F(0);cs=F(0);rs=F(0)
            for a in range(1,H+1):
                for c in range(1,H//a+1):
                    b.tick()
                    if math.gcd(a,c)!=1 or(a<=cut)!=inside:continue
                    q=F(1 if kernel=='one'else a if kernel=='a'else c if kernel=='b'else a-c);bs=b.add(bs,b.mul(q,b.mul(u[a],u[c])));cs=b.add(cs,b.mul(q,u[a*c]));rs=b.add(rs,b.mul(q,R(('coprime_product',a,c))))
            bs=b.mul(bs,normal);cs=b.mul(cs,normal);parts.append((bs,cs,b.mul(rs,normal)))
        sq.extend([b.sum(square(p[i])for p in parts)for i in (0,1)])
        rel.extend(b.sum(b.mul(p[2],b.add(p[0],p[1]if sign==1 else-p[1]))for p in parts)for sign in (1,-1))
        contrast=b.add(parts[0][1],-parts[1][1]);sq.extend([square(b.add(pref[H],contrast)),square(b.add(pref[H],-contrast))])
    for r in ('parent','child'):
        for power in (-1,0,1):
            groups=[F(0)]*5;norm=F(0);inv=F(0)
            for t in(range(X,2*X)if r=='parent'else range(2*X,4*X)):
                weights={a:F(a,t)**power for a in range(1,t+1)}
                for d in range(1,t+1):
                    q=b.sum(b.mul(weights[a],u[a])for a in range(d,t+1,d));mod=b.mul(u[d],q)
                    for i,z in enumerate((q,q,mod,b.add(q,mod),b.add(q,-mod))):groups[i]=b.add(groups[i],square(z,sf[d]if i==1 else 1))
                    norm=b.add(norm,b.mul(R(('norm',d)),square(q)))
                for a in range(1,t+1):
                    for c in range(1,t+1):
                        b.tick();g=math.gcd(a,c);inv=b.add(inv,b.mul(R(('unit',)if g==1 else('inverse_row',g)),b.mul(b.mul(weights[a],weights[c]),b.mul(u[a],u[c]))))
            sq.extend(groups);rel.extend((norm,inv))
    contrasts={}
    for r in ('parent','child'):
        for theta in ('1/3','1/2','2/3'):
            for power in (-1,0,1):
                groups=[F(0)]*3;rels=[F(0)]*4
                for t in(range(X,2*X)if r=='parent'else range(2*X,4*X)):
                    cut=floor_root(t,theta,b);inside=F(0);outside=F(0)
                    for a in range(1,t+1):
                        for d in range(1,a+1):
                            b.tick()
                            if a%d==0:
                                q=b.mul(F(a)**power,b.mul(u[a],u[d]))
                                if d<=cut:inside=b.add(inside,q)
                                else:outside=b.add(outside,q)
                    D=b.mul(F(1,2),b.add(b.add(inside,-outside),-1));Z=b.add(b.add(inside,outside),-1);contrasts[r,theta,power,t]=D
                    for i,z in enumerate((D,b.add(pref[t],D),b.add(pref[t],-D))):groups[i]=b.add(groups[i],square(z))
                    primitive=b.sum(b.mul(R(('unit',)if a==1 else('inverse_row',a)),b.add(u[1],1)if a==1 else b.mul(F(a)**power,u[a]))for a in range(1,t+1))
                    for i,z in enumerate((F(1),pref[t],D,Z)):rels[i]=b.add(rels[i],b.mul(primitive,z))
                sq.extend(groups);rel.extend(rels)
    require((len(sq),len(rel))==(366,403),'complete base scalar family count')
    states={r:[[F(1)]+[atom(k,t)for k in atoms]+[contrasts[r,theta,power,t]for theta in ('1/3','1/2','2/3')for power in(-1,0,1)]for t in(range(X,2*X)if r=='parent'else range(2*X,4*X))]for r in('parent','child')}
    # Complete per-t domains and primitive sums reused across all15 atoms.
    # Forward scalar evaluation remains independent of producer suffix counts.
    relation_sums={t:{f:b.sum(R(s)for s in group)for f,group in specs(t).items()}for t in range(X,H+1)}
    for f in FAMILIES:
        for r in ('parent','child'):
            ts=range(X,2*X)if r=='parent'else range(2*X,4*X)
            for i in range(15):rel.append(b.sum(b.mul(row[i],relation_sums[t][f])for t,row in zip(ts,states[r])))
    require(len(rel)==613,'complete613 signed primitive groups')
    grams=[]
    for r in ('child','parent'):
        grams.append([b.sum(b.mul(row[i],row[j])for row in states[r])for i in range(15)for j in range(i,15)])
    grams.append([b.add(c,-b.mul(F(4),p))for c,p in zip(*grams)])
    delta=b.add(b.sum(square(pref[t])for t in range(2*X,4*X)),-b.mul(F(4),b.sum(square(pref[t])for t in range(X,2*X))))
    return dict(squares=sq,relations=rel,grams=grams,delta=delta,states=states,factors=fac)


def exact_row(X,b):
    require(type(X)is int and 1<=X<=7,'bounded fixed probe scale')
    assignment=evaluate_pass(X,[2*n+1 for n in range(1,4*X)],b);baseline=evaluate_pass(X,[0]*(4*X-1),b)
    squares=[b.add(a,-z)for a,z in zip(assignment['squares'],baseline['squares'])];relations=[b.add(a,-z)for a,z in zip(assignment['relations'],baseline['relations'])]
    grams=[[b.add(a,-z)for a,z in zip(g,h)]for g,h in zip(assignment['grams'],baseline['grams'])]
    row=list(squares)
    for q in relations:row.extend((q,-q))
    row.extend([F(0)]*5)
    for g in grams:
        k=0
        for i in range(15):
            for j in range(i,15):row.append(b.mul(g[k],F(1 if i==j else 2)));k+=1
    require(len(row)==1957,'all original coordinates')
    return row,-b.add(assignment['delta'],-baseline['delta']),assignment,baseline

def original_columns(result,b):
    values=list(result['squares'])
    for q in result['relations']:values.extend((q,-q))
    values.extend([F(0)]*5)
    for gram in result['grams']:
        k=0
        for i in range(15):
            for j in range(i,15):values.append(b.mul(gram[k],F(1 if i==j else 2)));k+=1
    return values


def modular(q,b):
    b.check(q);require(q.denominator%65537!=0,'fixed prime denominator must be invertible; no retry');b.tick(34)
    return q.numerator%65537*pow(q.denominator%65537,65535,65537)%65537


def feedback_row(row,rhs,X):
    return dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,entries=[dict(index=i,coefficient=str(q))for i,q in enumerate(row)if q],rhs=str(rhs),zero_coordinates=[i for i,q in enumerate(row)if not q],scope='necessary constraint for this universal formal nonconstant identity; not a sufficient identity or cone condition',X=X,assignment=[2*n+1 for n in range(1,4*X)],layout=LAYOUT)

SCHEMA='primitive-state-direct-identity-probe-v1'
SPEC=dict(scale=7,horizon=27,prime=65537,assignment='u_n=2*n+1 for every formal variable',baseline='all variables zero including u_1',representation='direct paired exact rational ring evaluation; no polynomials',coefficient_source='complete366 squares,613 signed relations,360 original Gram columns',storage='child K minus four parent K',offdiagonal='two times upper entry',target='unchanged critical q6 C32; rhs minus Delta',slacks='all five zero in necessary row',nonzero='unverified until independent complete replay',zero='NOT_REFUTED_BY_THIS_PROBE; never a universal theorem')
SOURCE_CONSTRUCTOR='direct paired exact rational fixed grammar; complete domains, factors and integer root cuts; no symbolic polynomial materialization'
DOMAIN_POLICY=dict(per_scalar_pass='1000*H^3+10000 charged before domain construction',paired_passes=2,rational_arithmetic='each add or multiply charged before allocation; cumulative scalar cells',temporary_bits=8193,result_bits=4096,all_domain_reserves_shared_with_arithmetic=True)

def expected_plan(vector,X):
    return dict(schema='primitive-state-direct-identity-probe-plan-v1',program=PROGRAM,X=X,H=4*X-1,prime=65537,candidate_vector=vector,layout=LAYOUT,spec=SPEC,source_constructor=SOURCE_CONSTRUCTOR,domain_policy=DOMAIN_POLICY,**FLAGS)

def verify_probe(vector,plan,receipt,*,deadline=None,max_operations=200000000,max_cells=6000000,max_coefficient_bits=4096,max_receipt_bytes=1048576):
    require(type(max_cells)is int and 0<max_cells<=6000000 and type(max_receipt_bytes)is int and 0<max_receipt_bytes<=1048576,'strict direct output/cell caps')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_coefficient_bits);b.max_cells=max_cells
    require(type(vector)is list and len(vector)==1957 and type(plan)is dict and type(plan.get('X'))is int and 1<=plan['X']<=7,'all candidate coordinates and finite scale')
    X=plan['X'];require(plan==expected_plan(vector,X),'unchanged actual direct mathematical plan')
    raw=json.dumps(receipt,sort_keys=True,separators=(',',':'),allow_nan=False).encode();require(len(raw)<=max_receipt_bytes,'bounded direct receipt')
    b.tick(len(raw)//64+1,cells=len(raw)//64+1)
    for k,v in dict(schema=SCHEMA,program=PROGRAM,source_constructor=SOURCE_CONSTRUCTOR,X=X,H=4*X-1,prime=65537,spec=SPEC,domain_policy=DOMAIN_POLICY).items():require(receipt.get(k)==v,'fixed direct receipt '+k)
    for k in FLAGS:require(receipt.get(k)is False,'no formal/global promotion '+k)
    require(receipt.get('complete')is True,'complete direct receipt required')
    limits=receipt.get('limits');require(type(limits)is dict and set(limits)=={'max_operations','max_cells','max_coefficient_bits','max_receipt_bytes'},'explicit producer caps')
    for k,cap in dict(max_operations=200000000,max_cells=6000000,max_coefficient_bits=4096,max_receipt_bytes=1048576).items():require(type(limits[k])is int and 0<limits[k]<=cap,'bounded producer limit '+k)
    counts=receipt.get('counts');require(type(counts)is dict and set(counts)=={'operations','cumulative_scalar_cells','maximum_rational_bits'},'producer diagnostic counters')
    for k,cap in [('operations',limits['max_operations']),('cumulative_scalar_cells',limits['max_cells']),('maximum_rational_bits',limits['max_coefficient_bits'])]:require(type(counts[k])is int and 0<=counts[k]<=cap,'producer count bounded '+k)
    for d in range(2,math.isqrt(65537)+1):b.tick();require(65537%d,'fixed prime')
    weights=[modular(b.parse(q),b)for q in vector]
    row,rhs,point,zero=exact_row(X,b);values=original_columns(point,b);baselines=original_columns(zero,b)
    require(receipt.get('column_values')==list(map(str,values))and receipt.get('column_baselines')==list(map(str,baselines)),'all1957 exact full-source columns')
    require(receipt.get('feedback_row')==feedback_row(row,rhs,X),'every exact coefficient/sign/slack/storage/rhs')
    root=ceil_root(X,6,b);constant=F(32*X*X*root);target=[b.add(constant,-point['delta']),b.add(constant,-zero['delta'])]
    body=[0,0];dot=0
    for i,(a,z,q)in enumerate(zip(values,baselines,row)):
        b.tick(6);body[0]=(body[0]+modular(a,b)*weights[i])%65537;body[1]=(body[1]+modular(z,b)*weights[i])%65537;dot=(dot+modular(q,b)*weights[i])%65537
    tm=[modular(q,b)for q in target];residual=[(a-z)%65537 for a,z in zip(tm,body)];difference=(residual[0]-residual[1])%65537
    expected=dict(assignment=[2*n+1 for n in range(1,4*X)],baseline=[0]*(4*X-1),target_exact_values=list(map(str,target)),target_values=tm,body_values=body,residual_values=residual,nonconstant_difference=difference,feedback_row_dot_mod_prime=dot,feedback_rhs_mod_prime=modular(rhs,b),slack_coordinates_excluded=list(range(1592,1597)),source_denominators_invertible=True,prime_checked=True,complete_direct_source_evaluated=True,source_semantics_independently_verified=False,coverage=dict(square_groups=366,signed_relation_groups=613,split_relation_coordinates=1226,constant_slacks=5,gram_columns=360,regional_rows=3*X,atoms_per_row=15,primitive_families=list(FAMILIES),factor_blocks=44,complete_domains=True))
    expected['regional_states']={'full_'+r:[[[str(a),str(z)]for a,z in zip(pa,za)]for pa,za in zip(point['states'][r],zero['states'][r])]for r in('parent','child')}
    expected['factor_witnesses']={str(n):[[p,e]for p,e in sorted(f.items())]for n,f in point['factors'].items()}
    for k,v in expected.items():require(receipt.get(k)==v,'independent direct value/coverage '+k)
    require((modular(rhs,b)-dot)%65537==difference,'complete row and target residual agree');require(receipt.get('status')==('UNVERIFIED_COUNTEREXAMPLE'if difference else'NOT_REFUTED_BY_THIS_PROBE'),'scope-correct producer disposition')
    return dict(schema='primitive-state-direct-identity-probe-independent-check-v1',verified=True,complete=True,status='REFUTED'if difference else'NOT_REFUTED_BY_THIS_PROBE',nonconstant_formal_identity_refuted=bool(difference),complete_grammar_independently_evaluated=True,complete_coefficient_row_verified=True,symbolic_source_constructed=False,necessary_formal_identity_constraint=feedback_row(row,rhs,X),modular_prime=65537,nonconstant_difference=difference,scalar_passes=2,domain_control_work_reserve=2*(1000*(4*X-1)**3+10000),audit_operations=b.operations,audit_cells=b.cells,maximum_rational_bits=b.maximum_bits,**FLAGS)
