"""Independent direct rational finite FORMAL identity endpoint evaluation.

Each explicit integer assignment and all-zero baseline are evaluated in separate scalar passes.
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
        self.deadline=deadline;self.cap=max_operations;self.bits=max_bits;self.operations=0;self.cells=0;self.maximum_bits=0;self.max_cells=12000000;self.phase="initialization";self.case_index=None
    def tick(self,n=1,cells=0):
        require(type(n)is int and n>=0 and type(cells)is int and cells>=0,'nonnegative shared audit proxies')
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
    validate_assignment(X,values);H=4*X-1
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


def validate_assignment(X,values):
    require(type(X)is int and 1<=X<=9 and type(values)is list and len(values)==4*X-1 and all(type(v)is int and abs(v)<=4096 for v in values),'complete bounded integer assignment including u_1')


def exact_row(X,values,b):
    require(type(X)is int and 1<=X<=9,'bounded fresh probe scale')
    b.phase='case-%s assignment scalar pass'%b.case_index;assignment=evaluate_pass(X,values,b);b.phase='case-%s baseline scalar pass'%b.case_index;baseline=evaluate_pass(X,[0]*(4*X-1),b)
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


def feedback_row(row,rhs,X,values):
    return dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,entries=[dict(index=i,coefficient=str(q))for i,q in enumerate(row)if q],rhs=str(rhs),zero_coordinates=[i for i,q in enumerate(row)if not q],scope='necessary constraint for this universal formal nonconstant identity; not a sufficient identity or cone condition',X=X,assignment=values,layout=LAYOUT)

SCHEMA='primitive-state-fresh-identity-probe-v1'
SPEC=dict(scale_range=[1,9],maximum_horizon=35,prime=65537,assignment='explicit integer list of length4X-1; absolute value<=4096',baseline='all variables zero including u_1',representation='direct paired exact rational ring evaluation; no polynomials',coefficient_source='complete366 squares,613 signed relations,360 original Gram columns',storage='child K minus four parent K',offdiagonal='two times upper entry',target='unchanged critical q6 C32; rhs minus Delta',slacks='all five zero in necessary row',nonzero='unverified until independent complete replay',zero='NOT_REFUTED_BY_THIS_PROBE; never a universal theorem')
SOURCE_CONSTRUCTOR='fresh explicit-assignment paired exact rational fixed grammar; complete domains, factors and integer root cuts; no symbolic polynomial materialization'
DOMAIN_POLICY=dict(per_scalar_pass='1000*H^3+10000 charged before domain construction',paired_passes=2,rational_arithmetic='each add or multiply charged before allocation; cumulative scalar cells',temporary_bits=8193,result_bits=4096,all_domain_reserves_shared_with_arithmetic=True)

def expected_plan(vector,X,values,index):
    return dict(schema='primitive-state-fresh-identity-probe-plan-v1',case_index=index,assignment=values,program=PROGRAM,X=X,H=4*X-1,prime=65537,candidate_vector=vector,layout=LAYOUT,spec=SPEC,source_constructor=SOURCE_CONSTRUCTOR,domain_policy=DOMAIN_POLICY,**FLAGS)

def verify_probe(vector,plan,receipt,b,*,max_receipt_bytes=1048576):
    require(type(max_receipt_bytes)is int and 0<max_receipt_bytes<=1048576,'bounded fresh receipt')
    require(type(vector)is list and len(vector)==1957 and type(plan)is dict and type(plan.get('X'))is int and 1<=plan['X']<=9,'all original candidate coordinates and bounded scale')
    b.case_index=plan.get('case_index');b.phase='case-%s receipt and weights'%b.case_index
    X=plan['X'];values=plan.get('assignment');index=plan.get('case_index');validate_assignment(X,values);require(type(index)is int and 0<=index<2 and plan==expected_plan(vector,X,values,index),'actual exact mathematical fresh plan')
    raw=json.dumps(receipt,sort_keys=True,separators=(',',':'),allow_nan=False).encode();require(len(raw)<=max_receipt_bytes,'bounded direct receipt')
    b.tick(len(raw)//64+1,cells=len(raw)//64+1)
    for k,v in dict(schema=SCHEMA,program=PROGRAM,source_constructor=SOURCE_CONSTRUCTOR,case_index=index,X=X,H=4*X-1,prime=65537,spec=SPEC,domain_policy=DOMAIN_POLICY).items():require(receipt.get(k)==v,'fixed direct receipt '+k)
    for k in FLAGS:require(receipt.get(k)is False,'no formal/global promotion '+k)
    require(receipt.get('complete')is True,'complete direct receipt required')
    limits=receipt.get('limits');require(type(limits)is dict and set(limits)=={'max_operations','max_cells','max_coefficient_bits','max_receipt_bytes'},'explicit producer caps')
    for k,cap in dict(max_operations=100000000,max_cells=6000000,max_coefficient_bits=4096,max_receipt_bytes=1048576).items():require(type(limits[k])is int and 0<limits[k]<=cap,'bounded producer limit '+k)
    counts=receipt.get('counts');require(type(counts)is dict and set(counts)=={'operations','cumulative_scalar_cells','maximum_rational_bits'},'producer diagnostic counters')
    for k,cap in [('operations',limits['max_operations']),('cumulative_scalar_cells',limits['max_cells']),('maximum_rational_bits',limits['max_coefficient_bits'])]:require(type(counts[k])is int and 0<=counts[k]<=cap,'producer count bounded '+k)
    for d in range(2,math.isqrt(65537)+1):b.tick();require(65537%d,'fixed prime')
    weights=[modular(b.parse(q),b)for q in vector]
    row,rhs,point,zero=exact_row(X,values,b);column_values=original_columns(point,b);baselines=original_columns(zero,b)
    require(receipt.get('column_values')==list(map(str,column_values))and receipt.get('column_baselines')==list(map(str,baselines)),'all1957 exact full-source columns')
    require(receipt.get('feedback_row')==feedback_row(row,rhs,X,values),'every exact coefficient/sign/slack/storage/rhs')
    root=ceil_root(X,6,b);constant=F(32*X*X*root);target=[b.add(constant,-point['delta']),b.add(constant,-zero['delta'])]
    body=[0,0];dot=0
    for i,(a,z,q)in enumerate(zip(column_values,baselines,row)):
        b.tick(6);body[0]=(body[0]+modular(a,b)*weights[i])%65537;body[1]=(body[1]+modular(z,b)*weights[i])%65537;dot=(dot+modular(q,b)*weights[i])%65537
    tm=[modular(q,b)for q in target];residual=[(a-z)%65537 for a,z in zip(tm,body)];difference=(residual[0]-residual[1])%65537
    expected=dict(assignment=values,baseline=[0]*(4*X-1),target_exact_values=list(map(str,target)),target_values=tm,body_values=body,residual_values=residual,nonconstant_difference=difference,feedback_row_dot_mod_prime=dot,feedback_rhs_mod_prime=modular(rhs,b),slack_coordinates_excluded=list(range(1592,1597)),source_denominators_invertible=True,prime_checked=True,complete_direct_source_evaluated=True,source_semantics_independently_verified=False,coverage=dict(square_groups=366,signed_relation_groups=613,split_relation_coordinates=1226,constant_slacks=5,gram_columns=360,regional_rows=3*X,atoms_per_row=15,primitive_families=list(FAMILIES),factor_blocks=44,complete_domains=True))
    expected['regional_states']={'full_'+r:[[[str(a),str(z)]for a,z in zip(pa,za)]for pa,za in zip(point['states'][r],zero['states'][r])]for r in('parent','child')}
    expected['factor_witnesses']={str(n):[[p,e]for p,e in sorted(f.items())]for n,f in point['factors'].items()}
    for k,v in expected.items():require(receipt.get(k)==v,'independent direct value/coverage '+k)
    require((modular(rhs,b)-dot)%65537==difference,'complete row and target residual agree');require(receipt.get('status')==('UNVERIFIED_COUNTEREXAMPLE'if difference else'NOT_REFUTED_BY_THIS_PROBE'),'scope-correct producer disposition')
    return dict(schema='primitive-state-fresh-identity-probe-independent-check-v1',case_index=index,verified=True,complete=True,status='REFUTED'if difference else'NOT_REFUTED_BY_THIS_PROBE',nonconstant_formal_identity_refuted=bool(difference),complete_grammar_independently_evaluated=True,complete_coefficient_row_verified=True,symbolic_source_constructed=False,necessary_formal_identity_constraint=feedback_row(row,rhs,X,values),modular_prime=65537,nonconstant_difference=difference,scalar_passes=2,domain_control_work_reserve=2*(1000*(4*X-1)**3+10000),audit_operations=b.operations,audit_cells=b.cells,maximum_rational_bits=b.maximum_bits,**FLAGS)


def projection_layout():
    retained=[*range(366),*[366+2*i for i in range(613)],*range(1592,1837)]
    recipes={367+2*i:{366+2*i:F(-1)}for i in range(613)}
    recipes.update({1837+i:{1597+i:F(1),1717+i:F(-4)}for i in range(120)})
    require(len(retained)==1224 and len(recipes)==733,'complete unchanged original projection')
    return retained,recipes


def parse_chart(chart,review,report,b):
    """The wrapper supplies the designated published024 full-span premise."""
    require(report.get('schema')==24 and report.get('chart_verified')is True and report.get('candidate_equations_verified')is True and report.get('independent_audit_complete')is True and report.get('classification')=='independent'and report.get('coefficient_rank')==780 and report.get('augmented_rank')==780 and report.get('free_count')==444,'published024 complete consistent chart premise')
    check=review.get('independent_affine_check');require(review.get('schema')=='primitive-state-feedback-affine-independent-review-v1'and review.get('all_passed')is True and review.get('status')=='AFFINE_UPDATED'and review.get('chart_verified')is True and type(check)is dict and check.get('verified')is True and check.get('complete')is True and check.get('all_original_rows_replayed')is True and check.get('normalized_chart_verified')is True and check.get('new_rank')==780 and check.get('new_free_count')==444,'designated prior all-row span proof; no new old-tape replay')
    require(chart.get('schema')=='primitive-state-feedback-affine-chart-v1'and chart.get('width')==1224 and chart.get('original_width')==1957 and chart.get('old_rank')==779 and chart.get('new_rank')==780 and chart.get('classification')=='independent','actual complete780-pivot chart')
    retained,_=projection_layout();require(chart.get('retained_indices')==retained,'same1957-coordinate quotient')
    records=chart.get('normalized_rows');appended=chart.get('appended_row');require(type(records)is list and len(records)==779 and type(appended)is dict and appended.get('pivot')==148 and appended.get('source_row')=='feedback','all779 old rows and learned148 row retained')
    require(chart.get('old_pivots')==[r['pivot']for r in records]and chart['old_pivots']==sorted(set(chart['old_pivots']))and 148 not in chart['old_pivots'],'ordered779 old pivots')
    source_rows=set();basis={};cells=0
    for record in [*records,appended]:
        p=record.get('pivot');require(type(p)is int and 0<=p<1224 and p not in basis,'unique variable pivot')
        if record is not appended:require(type(record.get('source_row'))is int and 0<=record['source_row']<5641 and record['source_row']not in source_rows,'unique old source row');source_rows.add(record['source_row'])
        terms=record.get('terms');require(type(terms)is list and terms,'explicit normalized chart row');row={};last=-1;b.tick(len(terms),cells=len(terms));cells+=len(terms)
        for j,text in terms:
            require(type(j)is int and last<j<=1224,'ordered sparse augmented row');last=j;q=b.parse(text);require(q!=0,'nonzero chart coefficient');row[j]=q
        require(row.get(p)==1 and min(row)==p,'normalized upper-triangular cached row');basis[p]=row
    pivots=sorted(basis);free=[j for j in range(1224)if j not in basis]
    require(len(pivots)==780 and len(free)==444 and chart.get('pivot_columns')==pivots and chart.get('free_indices')==free and chart.get('old_free_indices')==[j for j in range(1224)if j not in chart['old_pivots']],'complete780/444 chart partition')
    return basis,retained


def project_constraint(constraint,b):
    retained,recipes=projection_layout();require(constraint.get('schema')=='primitive-state-formal-identity-necessary-row-v1'and constraint.get('width')==1957 and constraint.get('layout')==LAYOUT,'complete exact original-coordinate formal row')
    X=constraint.get('X');validate_assignment(X,constraint.get('assignment'));full=[F(0)]*1957;last=-1
    for item in constraint['entries']:
        j=item['index'];require(type(j)is int and last<j<1957,'ordered sparse exact original row');last=j;q=b.parse(item['coefficient']);require(q!=0,'nonzero exact row coefficient');full[j]=q
    require(constraint.get('zero_coordinates')==[j for j,q in enumerate(full)if not q]and all(full[j]==0 for j in range(1592,1597)),'complete zero complement and constant slacks absent')
    for omitted,recipe in recipes.items():
        value=F(0)
        for j,q in recipe.items():value=b.add(value,b.mul(q,full[j]))
        require(full[omitted]==value,'all613 signed and120 storage coefficient dependencies')
    return {i:full[j]for i,j in enumerate(retained)if full[j]},b.parse(constraint['rhs'])


def reduce_row(row,rhs,basis,index,b):
    residual=dict(row)
    if rhs:residual[1224]=rhs
    multipliers=[];b.tick(len(residual),cells=len(residual));b.tick(len(basis)*max(1,len(basis).bit_length()))
    for pivot in sorted(basis):
        if pivot not in residual:continue
        multiplier=residual[pivot];multipliers.append([pivot,str(multiplier)])
        for j,q in basis[pivot].items():
            value=b.add(residual.get(j,F(0)),-b.mul(multiplier,q))
            if value:residual[j]=value
            else:residual.pop(j,None)
    require(not(set(residual)&set(basis)),'all existing augmented pivots eliminated, even beyond leading free')
    coefficient_pivots=[j for j in residual if j<1224];classification='independent'if coefficient_pivots else'inconsistent'if residual.get(1224)else'redundant'
    pivot=min(coefficient_pivots)if coefficient_pivots else 1224 if classification=='inconsistent'else None
    normalization=residual[pivot]if pivot is not None else None;normalized=None
    if pivot is not None:
        normalized={}
        for j,q in sorted(residual.items()):
            b.tick(cells=1);b.check(q);b.check(normalization);normalized[j]=b.check(q/normalization)
        basis[pivot]=normalized
    rank=sum(p<1224 for p in basis);augmented=len(basis);contradictory=1224 in basis
    record=dict(index=index,classification=classification,multipliers=multipliers,residual_terms=[[j,str(q)]for j,q in sorted(residual.items())],chosen_pivot=pivot if classification=='independent'else None,normalization=str(normalization)if normalization is not None else None,normalized_row=dict(pivot=pivot,terms=[[j,str(q)]for j,q in sorted(normalized.items())])if normalized is not None else None,coefficient_rank=rank,augmented_rank=augmented,free_count=None if contradictory else 1224-rank)
    return record


def extend_chart(chart,review,report,constraints,b,*,chart_path=None):
    b.phase='cached024 chart parsing';basis,_=parse_chart(chart,review,report,b);require(type(constraints)is list and len(constraints)==2,'two mandatory sequential exact rows')
    reductions=[];appended=[];contradiction=None
    for index,constraint in enumerate(constraints):
        b.phase='case-%02d exact projection and sequential reduction'%index;row,rhs=project_constraint(constraint,b);record=reduce_row(row,rhs,basis,index,b);reductions.append(record)
        if record['classification']=='independent':appended.append(dict(source_case=index,**record['normalized_row']))
        elif record['classification']=='inconsistent':contradiction=dict(source_case=index,**record['normalized_row'])
    rank=sum(p<1224 for p in basis)
    return dict(complete=True,prior_chart_path=chart_path,prior_chart_schema='primitive-state-feedback-affine-chart-v1',prior_span_premise='designated published024 independently checked complete finite row span',old_rank=780,coefficient_rank=rank,augmented_rank=len(basis),free_count=None if 1224 in basis else 1224-rank,reductions=reductions,appended_rows=appended,contradiction_row=contradiction,old_tape_replayed=False,formal_family_only=True,**FLAGS)


def verify_cases(vector,plans,receipts,chart,review024,report024,*,deadline=None,max_operations=200000000,max_cells=12000000,max_coefficient_bits=4096,chart_path=None):
    require(type(max_cells)is int and 0<max_cells<=12000000,'shared twelve-million cumulative scalar-cell cap')
    require(type(plans)is list and type(receipts)is list and len(plans)==len(receipts)==2,'complete pair of fresh cases')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_coefficient_bits);b.max_cells=max_cells;checks=[];constraints=[]
    try:
        for index,(plan,receipt)in enumerate(zip(plans,receipts)):
            require(plan.get('case_index')==receipt.get('case_index')==index,'fixedcase order and labels')
            check=verify_probe(vector,plan,receipt,b);checks.append(dict(index=index,independent_probe_check=check));constraints.append(check['necessary_formal_identity_constraint'])
        extension=extend_chart(chart,review024,report024,constraints,b,chart_path=chart_path)
        result=dict(verified=True,complete=True,case_checks=checks,necessary_formal_identity_constraints=constraints,affine_extension=extension,nonconstant_formal_identity_refuted=any(c['independent_probe_check']['nonconstant_formal_identity_refuted']for c in checks),scalar_passes=4,audit_operations=b.operations,audit_cells=b.cells,maximum_rational_bits=b.maximum_bits,shared_budget=True,**FLAGS)
        b.phase='complete mathematical result serialization';payload=json.dumps(result,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
        if len(payload)>8388608:raise OverflowError('complete independent mathematical result byte cap')
        b.tick(2*(len(payload)//64+1),cells=len(payload)//64+1);result.update(audit_operations=b.operations,audit_cells=b.cells)
        return result
    except(OverflowError,TimeoutError,MemoryError)as error:
        error.independent_audit_counts=dict(operations=b.operations,cumulative_scalar_cells=b.cells,maximum_rational_bits=b.maximum_bits)
        error.independent_phase=b.phase
        raise
