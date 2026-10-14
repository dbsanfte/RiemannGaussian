"""Independent exact necessary-row and finite-field formal counterexample checks.

No arithmetic substitution or numerical samples establish an identity here. A
nonzero residue refutes only the fixed nonconstant formal identity, after a
complete independently reconstructed finite native source is bound.
"""
import json
import copy
import math
from fractions import Fraction as F
import sys
import time
import check_cancellation_primitive_state_localizers as LOCAL
import check_primitive_state_uniform_native_source as MATH_SOURCE

SCHEMA='primitive-state-uniform-identity-probe-v1'
NATIVE_CONSTRUCTOR='math-only fixed366/403/full15 source + complete primitive suffix multipliers; no metadata hashes or optional expanded verification'
FLAGS=dict(global_bound_proved=False,RH_proved=False,universal_identity_proved=False,candidate_admitted=False,exact_admission=False,infeasibility_proved=False,identity_refuted=False,arithmetic_sign_values_substituted=False,scalar_budget_obligation_verified=False)
SPEC=dict(scale=7,prime=65537,assignment='u_n=2*n+1 for every 1<=n<=4*X-1',baseline='all formal variables zero, including u_1',expression='(L_X-B_X)(u)-(L_X-B_X)(0)',field='fixed prime modular rational reduction; integer predicates/cuts before reduction',target='unchanged q6 C32 critical mu target',slacks='all five per-instance constants excluded; baseline subtraction cancels them',storage='Gc child + Gp parent + K(child - 4 parent)',offdiagonal='two times upper-triangle entry',conclusion_nonzero='unverified_counterexample until independent complete source replay',conclusion_zero='NOT_REFUTED_BY_THIS_PROBE; no universal theorem')
LAYOUT=dict(n_variables=1957,squares=366,relations=613,split_start=366,split_end=1592,slack_start=1592,slack_end=1597,gram_offset=1597,gram_order=['full_child','full_parent','storage_K'],gram_dimension=15,gram_pairs='upper triangle row-major')
_TOKEN=object()

class _SourceAbort(BaseException):
    pass

def require(condition,message):
    if not condition:raise ValueError(message)

def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()

class Budget:
    def __init__(self,deadline=None,max_operations=50000000,max_cells=60000000,max_bits=4096):
        require(type(max_operations)is int and 0<max_operations<=450000000 and type(max_cells)is int and 0<max_cells<=60000000 and type(max_bits)is int and 0<max_bits<=4096,'strict finite independent caps')
        require(deadline is None or type(deadline)in (int,float)and math.isfinite(deadline),'finite independent deadline')
        self.deadline=deadline;self.max_operations=max_operations;self.max_cells=max_cells;self.max_bits=max_bits;self.operations=0;self.cells=0
    def charge(self,n=1,cells=0):
        require(type(n)is int and n>=0 and type(cells)is int and cells>=0,'nonnegative independent work/cells')
        if self.deadline is not None and time.monotonic()>self.deadline:raise TimeoutError('independent probe deadline')
        if n>self.max_operations-self.operations or cells>self.max_cells-self.cells:raise OverflowError('independent probe work/cell cap')
        self.operations+=n;self.cells+=cells
    def checked(self,q):
        require(type(q)is F,'exact rational operand')
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>self.max_bits:raise OverflowError('independent exact rational bit cap')
        return q
    def rational(self,s):
        require(type(s)is str and 0<len(s)<=2*self.max_bits+3 and all(c in '-0123456789/'for c in s),'canonical bounded rational text')
        self.charge(1+len(s)//64)
        parts=s.split('/');require(len(parts)<=2 and all(part not in ('','-')for part in parts),'rational components')
        if any(abs(int(part)).bit_length()>self.max_bits for part in parts):raise OverflowError('rational parse before Fraction allocation')
        q=F(s);require(str(q)==s,'canonical exact rational');return self.checked(q)
    def add(self,a,b):self.checked(a);self.checked(b);self.charge();return self.checked(a+b)
    def mul(self,a,b):self.checked(a);self.checked(b);self.charge();return self.checked(a*b)


def verify_plan(plan,vector,budget):
    require(type(plan)is dict and plan.get('schema')=='primitive-state-uniform-identity-probe-plan-v1','known exact fixed-probe plan')
    for k in FLAGS:require(plan.get(k)is False,'plan cannot admit a theorem')
    require(plan.get('program')==dict(target='mu',q=6,C='32',claim='critical') and type(plan.get('X'))is int and 1<=plan['X']<=7,'unchanged exact critical program and finite bounded scale')
    X=plan['X'];H=4*X-1;p=plan.get('prime')
    require(type(p)is int and p==65537 and plan.get('H')==H,'one fixed prime and exact source horizon')
    for d in range(2,math.isqrt(p)+1):budget.charge();require(p%d!=0,'prime checked independently')
    require(plan.get('assignment')==[2*n+1 for n in range(1,H+1)] and plan.get('baseline')==[0]*H and plan.get('spec')==SPEC and plan.get('layout')==LAYOUT,'fixed full formal assignment including free u1, layout and source scope')
    require(type(vector)is list and len(vector)==1957,'every original candidate coordinate explicit')
    coeff=[]
    for s in vector:
        q=budget.rational(s);require(q.denominator%p!=0,'candidate denominator invertible at fixed prime');coeff.append(q)
    require(plan.get('candidate_vector')==vector and plan.get('source_constructor')==NATIVE_CONSTRUCTOR,'actual fixed candidate vector and declared native construction')
    return coeff

class _SourceLicense:
    def __init__(self,token,native,plan,vector,counts):
        require(token is _TOKEN,'source license issued only by independent complete reconstruction')
        self.native=native;self.plan=copy.deepcopy(plan);self.vector=tuple(vector);self.counts=counts


def _construct_source(program,X):
    """Independent finite forward aggregation, without optional degree4 products.

    All seven complete primitive families, both regions, and15 atoms are retained.
    Only optional expanded polynomial hashes and nonsemantic counters are omitted.
    """
    limits=dict(max_horizon=27,max_operations=200000000,max_terms=100000,max_coefficient_bits=4096)
    out=MATH_SOURCE.build_affine(program,X,**limits);blocks=out['gram_blocks'];H=4*X-1
    require(set(blocks)=={'full_child','full_parent'} and len(blocks['full_child'])==2*X and len(blocks['full_parent'])==X,'complete original15-state regional source')
    domains={t:LOCAL.primitive_specs(t)for t in range(X,H+1)};groups=[];retained=out['math_source_counts']['retained_cells']
    for family,region,atom in ((family,region,atom)for family in LOCAL.SPEC['primitive_families']for region in LOCAL.SPEC['regions']for atom in range(15)):
        ts=range(X,2*X)if region=='parent'else range(2*X,4*X)
        accumulated={}
        for t,state in zip(ts,blocks['full_'+region]):
            require(len(state)==15,'all15 independent state atoms');poly=LOCAL.P.parse(state[atom],H)
            for spec in domains[t][family]:
                key=encoded(spec)
                if key not in accumulated:accumulated[key]={}
                row=accumulated[key]
                for m,q in poly.items():
                    value=row.get(m,F(0))+q
                    if max(abs(value.numerator).bit_length(),value.denominator.bit_length())>4096:raise OverflowError('independent primitive coefficient cap')
                    if value:row[m]=value
                    else:row.pop(m,None)
                if len(row)>100000:raise OverflowError('independent primitive term cap')
        terminal=domains[max(ts)][family]
        retained+=sum(len(accumulated[encoded(spec)])for spec in terminal)
        if retained>4000000:raise OverflowError('complete independent retained source cells')
        groups.append([dict(spec=spec,multiplier=LOCAL.P.canonical(accumulated[encoded(spec)]))for spec in terminal])
    require(len(groups)==210,'all210 independently added primitive-state groups')
    out['instance']['relation_groups'].extend(groups);out.update(gram_program=LOCAL.SPEC,primitive_state_spec=LOCAL.SPEC)
    return out


def rebuild_source(plan,vector,*,deadline=None,max_source_line_events=150000000,max_operations=50000000,max_cells=60000000):
    """One complete rebuild, metered across nested source/Fraction call frames.

    LINE_EVENTS are runtime proxies, not exact arithmetic-operation counts. A
    finite event cap enforces stopping even where frozen nested budgets reset.
    The whole-stage protocol must separately reserve serialization/evaluation.
    """
    require(type(max_source_line_events)is int and 0<max_source_line_events<=150000000,'finite aggregate source line-event cap')
    budget=Budget(deadline,max_operations,max_cells);verify_plan(plan,vector,budget);old=sys.gettrace();require(old is None,'do not replace an existing trace instrumentation')
    events=0;guard_reason=None
    def trace(frame,event,arg):
        nonlocal events,guard_reason
        if event=='line':
            events+=1
            if events>max_source_line_events:
                guard_reason='aggregate independent native source LINE_EVENTS cap';raise _SourceAbort(guard_reason)
            if events%1024==0 and deadline is not None and time.monotonic()>deadline:
                guard_reason='independent native source deadline';raise _SourceAbort(guard_reason)
        return trace
    try:
        sys.settrace(trace);native=_construct_source(plan['program'],plan['X'])
        if guard_reason is not None:raise _SourceAbort(guard_reason)
        if sys.gettrace()is not trace:raise _SourceAbort('native source trace instrumentation disabled')
    except _SourceAbort as error:
        raise OverflowError(str(error)) from None
    finally:
        sys.settrace(old)
        require(sys.gettrace()is old,'native trace instrumentation restored')
    return _SourceLicense(_TOKEN,native,plan,vector,dict(native_line_events=events,audit_operations=budget.operations,audit_cells=budget.cells))


class Evaluator:
    def __init__(self,plan,budget):self.H=plan['H'];self.p=plan['prime'];self.values=plan['assignment'];self.b=budget;self.relations={};self.source_terms=0
    def mod(self,q):
        self.b.checked(q);require(q.denominator%self.p!=0,'all exact source/row denominators invertible; no prime retry');self.b.charge(2*self.p.bit_length());return q.numerator%self.p*pow(q.denominator%self.p,self.p-2,self.p)%self.p
    def pair(self,poly):
        require(type(poly)is list and len(poly)<=100000,'complete bounded polynomial factors');self.b.charge(len(poly),cells=len(poly));self.source_terms+=len(poly);previous=None;total=F(0);constant=F(0)
        for term in poly:
            require(type(term)is dict and set(term)=={'m','c'} and type(term['m'])is list,'canonical native polynomial term')
            m=term['m'];require(len(m)<=4 and all(type(i)is int and 1<=i<=self.H for i in m) and m==sorted(m) and (previous is None or previous<m),'strict complete monomial order/domain');previous=m
            q=self.b.rational(term['c']);require(q!=0 and q.denominator%self.p!=0,'nonzero coefficient with invertible denominator')
            if not m:constant=q
            for i in m:q=self.b.mul(q,F(self.values[i-1]))
            total=self.b.add(total,q)
        return total,constant
    def relation(self,spec):
        key=encoded(spec);self.b.charge(1+len(encoded(spec))//64)
        if key not in self.relations:
            # Frozen independent factor/root domains are bounded by H<=27.
            self.b.charge(16*self.H*self.H+16*self.H+256)
            polynomial=LOCAL.G.relation(spec,'mu',self.H);self.relations[key]=self.pair(LOCAL.P.canonical(polynomial));self.b.charge(cells=1)
        return self.relations[key]


def exact_row(native,plan,vector,budget):
    instance=native['instance'];H=plan['H'];X=plan['X'];p=plan['prime'];require(instance['target']=='mu' and instance['horizon']==H and len(instance['square_groups'])==366 and len(instance['relation_groups'])==613,'complete366/613 native source')
    blocks=native['gram_blocks'];require(native['gram_specs']=={'full_child':15,'full_parent':15,'storage_K':15} and set(blocks)=={'full_child','full_parent'} and len(blocks['full_child'])==2*X and len(blocks['full_parent'])==X,'complete original3Gram regions')
    require(native['storage_blocks']==dict(kind='signed_storage_increment',child=blocks['full_child'],parent=blocks['full_parent'],child_multiplier='1',parent_multiplier='-4'),'signed child-minus4parent storage source')
    E=Evaluator(plan,budget);weights=[E.mod(q)for q in vector];row=[F(0)]*1957;body=[0,0];square_values=[];relation_values=[];totals={}
    for kind,count,groups in [('square',366,instance['square_groups']),('relation',613,instance['relation_groups'])]:
        weighted_sum=[0,0]
        for i,group in enumerate(groups):
            require(type(group)is list,'complete group factor list');pair=[F(0),F(0)]
            for term in group:
                if kind=='square':
                    require(type(term)is dict and set(term)=={'poly','weight'},'complete square factor/weight');a,b=E.pair(term['poly']);w=budget.rational(term['weight']);require(w>=0,'native internal square coefficient nonnegative');E.mod(w);pair=[budget.add(pair[0],budget.mul(w,budget.mul(a,a))),budget.add(pair[1],budget.mul(w,budget.mul(b,b)))]
                else:
                    require(type(term)is dict and set(term)=={'spec','multiplier'},'complete signed relation factor');a,b=E.relation(term['spec']);c,d=E.pair(term['multiplier']);pair=[budget.add(pair[0],budget.mul(a,c)),budget.add(pair[1],budget.mul(b,d))]
            delta=budget.add(pair[0],-pair[1])
            if kind=='square':row[i]=delta;w=weights[i]
            else:row[366+2*i]=delta;row[367+2*i]=-delta;w=(weights[366+2*i]-weights[367+2*i])%p
            weighted=[E.mod(q)*w%p for q in pair];weighted_sum=[(a+b)%p for a,b in zip(weighted_sum,weighted)];entry=dict(index=i,value=weighted[0],baseline=weighted[1],exact_value=str(pair[0]),exact_baseline=str(pair[1]));(square_values if kind=='square'else relation_values).append(entry)
        totals[kind]=weighted_sum;body=[(a+b)%p for a,b in zip(body,weighted_sum)]
    states={}
    for name,region in blocks.items():
        states[name]=[]
        for state in region:
            require(type(state)is list and len(state)==15,'every formal15-state row explicit');pairs=[E.pair(poly)for poly in state];states[name].append(([a for a,b in pairs],[b for a,b in pairs]))
    gram_values=[];gram_total=[0,0]
    for z,name in enumerate(LAYOUT['gram_order']):
        regions=[('full_child',1)]if z==0 else [('full_parent',1)]if z==1 else [('full_child',1),('full_parent',-4)];values=[0,0];columns=[];position=0
        for i in range(15):
            for j in range(i,15):
                pair=[F(0),F(0)]
                for region,sign in regions:
                    for a,b in states[region]:
                        factor=F(sign*(1 if i==j else 2));pair=[budget.add(pair[0],budget.mul(factor,budget.mul(a[i],a[j]))),budget.add(pair[1],budget.mul(factor,budget.mul(b[i],b[j])))]
                k=1597+120*z+position;row[k]=budget.add(pair[0],-pair[1]);values=[(old+E.mod(q)*weights[k])%p for old,q in zip(values,pair)];columns.append(dict(value=str(pair[0]),baseline=str(pair[1])));position+=1
        gram_values.append(dict(name=name,value=values[0],baseline=values[1],exact_columns=columns));gram_total=[(a+b)%p for a,b in zip(gram_total,values)]
    prefix=[0]
    for value in plan['assignment']:prefix.append(prefix[-1]+value);budget.charge()
    delta=sum(prefix[t]**2 for t in range(2*X,4*X))-4*sum(prefix[t]**2 for t in range(X,2*X));budget.charge(8*X)
    root=1
    while root**6<X:root+=1;budget.charge(6)
    D=32*X*X*root;target_pair=(F(D-delta),F(D));require(E.pair(instance['lhs'])==target_pair,'direct prefix-square target agrees with complete native target')
    target=[E.mod(q)for q in target_pair];body=[(body[i]+gram_total[i])%p for i in range(2)];residual=[(target[i]-body[i])%p for i in range(2)];difference=(residual[0]-residual[1])%p;rhs=F(-delta)
    return dict(row=row,rhs=rhs,square_values=square_values,relation_values=relation_values,gram_values=gram_values,target_values=target,target_exact_values=list(map(str,target_pair)),square_total=totals['square'],relation_total=totals['relation'],gram_total=gram_total,body_values=body,residual_values=residual,nonconstant_difference=difference,relation_spec_count=len(E.relations),source_terms=E.source_terms,feedback_row_dot_mod_prime=sum(E.mod(q)*w for q,w in zip(row,weights))%p,feedback_rhs_mod_prime=E.mod(rhs))


def verify_probe(source_license,vector,plan,receipt,*,deadline=None,max_operations=50000000,max_cells=60000000,max_coefficient_bits=4096,max_receipt_bytes=1048576):
    require(type(source_license)is _SourceLicense,'complete independently rebuilt source license required; raw native data cannot reject an identity')
    budget=Budget(deadline,max_operations,max_cells,max_coefficient_bits);weights=verify_plan(plan,vector,budget)
    require(source_license.plan==plan and source_license.vector==tuple(vector),'independent source and exact candidate belong to this actual mathematical plan')
    require(type(receipt)is dict and len(encoded(receipt))<=max_receipt_bytes<=1048576,'bounded complete probe receipt')
    for k in FLAGS:require(receipt.get(k)is False,'producer never admits a formal/scalar/arithmetic theorem')
    require(receipt.get('schema')==SCHEMA and receipt.get('X')==plan['X'] and receipt.get('H')==plan['H'] and receipt.get('prime')==65537 and receipt.get('spec')==SPEC,'fixed counterexample envelope')
    require(receipt.get('complete')is True and receipt.get('assignment')==plan['assignment'] and receipt.get('baseline')==plan['baseline'],'complete native evaluation at the actual fixed assignment')
    values=exact_row(source_license.native,plan,weights,budget)
    for k in ('square_values','relation_values','gram_values','target_values','target_exact_values','square_total','relation_total','gram_total','body_values','residual_values','nonconstant_difference','relation_spec_count','feedback_row_dot_mod_prime','feedback_rhs_mod_prime'):require(receipt.get(k)==values[k],'independently recomputed complete exact/modular evaluation '+k)
    expected_status='UNVERIFIED_COUNTEREXAMPLE'if values['nonconstant_difference']else'NOT_REFUTED_BY_THIS_PROBE';require(receipt.get('status')==expected_status,'nonzero/zero producer outcome only')
    feedback=dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,entries=[dict(index=i,coefficient=str(q))for i,q in enumerate(values['row'])if q],rhs=str(values['rhs']),zero_coordinates=[i for i,q in enumerate(values['row'])if not q],scope='necessary constraint for this universal formal nonconstant identity; not a sufficient identity or cone condition',X=plan['X'],assignment=plan['assignment'],layout=LAYOUT)
    require(receipt.get('feedback_row')==feedback and (values['feedback_rhs_mod_prime']-values['feedback_row_dot_mod_prime'])%65537==values['nonconstant_difference'],'all1957 original necessary-row coefficients and modular witness verified')
    require(receipt.get('program')==plan['program'] and receipt.get('source_constructor')==plan['source_constructor'],'actual receipt program/construction')
    require(receipt.get('slack_coordinates_excluded')==list(range(1592,1597)) and receipt.get('complete_native_source_evaluated')is True and receipt.get('source_semantics_independently_verified')is False and receipt.get('source_denominators_invertible')is True and receipt.get('prime_checked')is True,'producer scope and complete denominator/domain coverage')
    nonzero=values['nonconstant_difference']!=0
    return dict(schema='primitive-state-uniform-identity-probe-independent-check-v1',verified=True,complete=True,status='REFUTED'if nonzero else'NOT_REFUTED_BY_THIS_PROBE',nonconstant_formal_identity_refuted=nonzero,source_semantics_independently_verified=True,necessary_formal_identity_constraint=feedback,nonconstant_difference=values['nonconstant_difference'],modular_prime=65537,formal_assignment_complete=True,original_variables=1957,source_rebuilds=1,source_degree_bound_verified=False,arithmetic_or_scalar_identity_refuted=False,audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(encoded(receipt))+1,**FLAGS)
