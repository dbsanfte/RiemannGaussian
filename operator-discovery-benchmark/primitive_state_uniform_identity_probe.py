"""Bounded modular counterexample proposals for a complete native formal operator.

A nonzero producer value is unverified until independent source reconstruction.
Zero never proves a universal identity. No arithmetic sign samples are used.
"""
from fractions import Fraction as F
import json
import math
import time
import cancellation_primitive_state_localizers as NATIVE
import grouped_arithmetic_language as LANGUAGE
import primitive_state_uniform_native_source as MATH_NATIVE

SCHEMA='primitive-state-uniform-identity-probe-v1'
SEMANTIC_KEYS=['instance','gram_blocks','storage_blocks','gram_specs','gram_program','primitive_state_spec']
FLAGS=dict(global_bound_proved=False,RH_proved=False,universal_identity_proved=False,candidate_admitted=False,exact_admission=False,infeasibility_proved=False,identity_refuted=False,arithmetic_sign_values_substituted=False,scalar_budget_obligation_verified=False)
SPEC=dict(scale=7,prime=65537,assignment='u_n=2*n+1 for every 1<=n<=4*X-1',baseline='all formal variables zero, including u_1',expression='(L_X-B_X)(u)-(L_X-B_X)(0)',field='fixed prime modular rational reduction; integer predicates/cuts before reduction',target='unchanged q6 C32 critical mu target',slacks='all five per-instance constants excluded; baseline subtraction cancels them',storage='Gc child + Gp parent + K(child - 4 parent)',offdiagonal='two times upper-triangle entry',conclusion_nonzero='unverified_counterexample until independent complete source replay',conclusion_zero='NOT_REFUTED_BY_THIS_PROBE; no universal theorem')
LAYOUT=dict(n_variables=1957,squares=366,relations=613,split_start=366,split_end=1592,slack_start=1592,slack_end=1597,gram_offset=1597,gram_order=['full_child','full_parent','storage_K'],gram_dimension=15,gram_pairs='upper triangle row-major')
# Source-stage allocation is supplied by the runner's independently reviewed
# aggregate native-call bound, not inferred from a nested helper's local cap.
DEFAULT_LIMITS=dict(max_operations=50000000,max_coefficient_bits=4096,max_source_cells=4000000,max_polynomial_terms=100000,max_receipt_bytes=1048576,max_live_cells=6000000)

def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode('utf-8')
def canonical_key(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False)

class Budget:
    def __init__(self,*,deadline,max_operations=50000000,max_coefficient_bits=4096,max_source_cells=4000000,max_polynomial_terms=100000,max_receipt_bytes=1048576,max_live_cells=6000000):
        if type(deadline)not in (int,float)or not math.isfinite(deadline):raise ValueError('finite cooperative deadline')
        for x in [max_operations,max_coefficient_bits,max_source_cells,max_polynomial_terms,max_receipt_bytes,max_live_cells]:
            if type(x)is not int or x<1:raise ValueError('strict positive probe caps')
        if max_operations>450000000 or max_coefficient_bits>4096 or max_source_cells>60000000 or max_live_cells>60000000:raise ValueError('probe hard resource caps')
        self.deadline=deadline;self.limits=dict(max_operations=max_operations,max_coefficient_bits=max_coefficient_bits,max_source_cells=max_source_cells,max_polynomial_terms=max_polynomial_terms,max_receipt_bytes=max_receipt_bytes,max_live_cells=max_live_cells);self.operations=0;self.source_cells=0;self.polynomial_terms=0;self.peak_live_cells=0
    def charge(self,n=1):
        if type(n)is not int or n<0:raise ValueError('nonnegative work')
        if time.monotonic()>self.deadline:raise TimeoutError('probe cooperative deadline')
        if n>self.limits['max_operations']-self.operations:raise OverflowError('probe work cap')
        self.operations+=n
    def cells(self,n):
        if n>self.limits['max_live_cells']:raise OverflowError('probe live cell cap')
        self.peak_live_cells=max(self.peak_live_cells,n);self.charge()
    def rational(self,s):
        self.charge(1+len(s)//64 if type(s)is str else 1)
        if type(s)is not str or not s or len(s)>2*self.limits['max_coefficient_bits']+3 or any(c not in '-0123456789/'for c in s):raise ValueError('canonical bounded rational string')
        parts=s.split('/')
        if len(parts)>2 or any(not t or t in ('-','+')for t in parts):raise ValueError('valid rational syntax')
        digits=1+self.limits['max_coefficient_bits']*30103//100000
        if any(len(t.lstrip('-'))>digits for t in parts):raise OverflowError('rational integer text bit preflight')
        try:n=int(parts[0]);d=int(parts[1])if len(parts)==2 else 1
        except ValueError:raise ValueError('valid rational integer')from None
        if d<=0:raise ValueError('positive rational denominator')
        if max(abs(n).bit_length(),d.bit_length())>self.limits['max_coefficient_bits']:raise OverflowError('probe coefficient bit cap before Fraction allocation')
        q=F(n,d)
        if str(q)!=s:raise ValueError('canonical rational string')
        return q
    def counts(self):return dict(operations=self.operations,source_cells=self.source_cells,polynomial_terms=self.polynomial_terms,peak_live_cells=self.peak_live_cells)

def is_prime(p,budget):
    if type(p)is not int or p<2 or p>65537:raise ValueError('bounded fixed prime')
    for d in range(2,math.isqrt(p)+1):
        budget.charge()
        if p%d==0:return False
    return True

def preflight(candidate_vector,program,*,X=7,prime=65537,deadline=None,limits=None):
    """Pure plan; never constructs or evaluates the arithmetic operator."""
    budget=Budget(deadline=time.monotonic()+60 if deadline is None else deadline,**dict(DEFAULT_LIMITS,**(limits or {})))
    if type(X)is not int or not 1<=X<=7:raise ValueError('declared bounded scale')
    if type(program)is not dict or program!=dict(target='mu',q=6,C='32',claim='critical'):raise ValueError('unchanged critical program')
    if not is_prime(prime,budget):raise ValueError('prime independently checked by trial division')
    if type(candidate_vector)is not list or len(candidate_vector)!=1957:raise ValueError('complete original coordinate vector')
    for s in candidate_vector:
        q=budget.rational(s)
        if q.denominator%prime==0:raise ValueError('candidate denominator not invertible; no adaptive prime')
    return dict(schema='primitive-state-uniform-identity-probe-plan-v1',program=program,X=X,H=4*X-1,prime=prime,assignment=[2*n+1 for n in range(1,4*X)],baseline=[0]*(4*X-1),candidate_vector=list(candidate_vector),layout=LAYOUT,source_constructor=NATIVE_CONSTRUCTOR,spec=SPEC,limits=budget.limits,preflight_counts=budget.counts(),**FLAGS)

class ExactEvaluator:
    def __init__(self,p,H,budget):self.p=p;self.H=H;self.b=budget;self.coefficients={};self.relations={}
    def checked(self,q):
        if type(q)is not F:raise ValueError('exact Fraction operand')
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>self.b.limits['max_coefficient_bits']:raise OverflowError('exact evaluation result bit cap')
        return q
    def add(self,a,b):
        # Check bounded operands before rational allocation: at most8193bits
        # temporarily, then the declared4096bit result cap applies immediately.
        self.checked(a);self.checked(b);self.b.charge();return self.checked(a+b)
    def mul(self,a,b):
        self.checked(a);self.checked(b);self.b.charge();return self.checked(a*b)
    def coefficient(self,s):
        q=self.b.rational(s)
        if q.denominator%self.p==0:raise ValueError('source denominator not invertible; no adaptive prime')
        if s not in self.coefficients:
            self.b.charge(2*self.p.bit_length());self.coefficients[s]=q.numerator%self.p*pow(q.denominator%self.p,self.p-2,self.p)%self.p;self.b.cells(len(self.coefficients)+len(self.relations))
        return self.coefficients[s]
    def pair(self,serial,values):
        if type(serial)is not list or len(serial)>self.b.limits['max_polynomial_terms']:raise ValueError('complete bounded canonical polynomial list')
        if len(serial)>self.b.limits['max_source_cells']-self.b.source_cells:raise OverflowError('source term cell cap')
        self.b.source_cells+=len(serial);self.b.polynomial_terms+=len(serial);previous=None;total=F(0);zero=F(0)
        for row in serial:
            self.b.charge()
            if type(row)is not dict or set(row)!={'m','c'}or type(row['m'])is not list:raise ValueError('native polynomial term schema')
            m=row['m']
            if len(m)>4 or any(type(n)is not int or not 1<=n<=self.H for n in m)or m!=sorted(m):raise ValueError('native bounded monomial')
            if previous is not None and m<=previous:raise ValueError('canonical strict polynomial term order')
            previous=m;c=self.b.rational(row['c'])
            if not c:raise ValueError('nonzero polynomial coefficient')
            if c.denominator%self.p==0:raise ValueError('source denominator not invertible; no adaptive prime')
            if not m:zero=c
            for n in m:c=self.mul(c,F(values[n-1]))
            total=self.add(total,c)
        return total,zero
    def relation_pair(self,spec,values):
        key=canonical_key(spec);self.b.charge(1+len(encoded(spec))//64)
        if key not in self.relations:
            cap=16*self.H*self.H+16*self.H+256;self.b.charge(cap)
            poly=LANGUAGE.relation(spec,'mu',self.H,max_operations=cap,max_horizon=self.H)
            self.relations[key]=self.pair(LANGUAGE.dump_poly(poly),values);self.b.cells(len(self.relations)+len(self.coefficients))
        return self.relations[key]

def target_pair(X,program,values,p,budget):
    r=1
    while r**program['q']<X:budget.charge(program['q']);r+=1
    D=int(program['C'])*X*X*r;prefix=[0];running=0
    for v in values:budget.charge(2);running=running+v;prefix.append(running)
    delta=0
    for t in range(2*X,4*X):budget.charge(3);delta=delta+prefix[t]*prefix[t]
    for t in range(X,2*X):budget.charge(4);delta=delta-4*prefix[t]*prefix[t]
    return (F(D-delta),F(D))

def probe_native(native,candidate_vector,plan,*,deadline,limits=None,checkpoint=None):
    """Evaluate a complete native instance once. No source admission is issued."""
    budget=Budget(deadline=deadline,**dict(DEFAULT_LIMITS,**(limits or {})));out=dict(schema=SCHEMA,status='UNKNOWN',complete=False,program=plan.get('program'),source_constructor=NATIVE_CONSTRUCTOR,X=plan.get('X'),H=plan.get('H'),prime=plan.get('prime'),spec=SPEC,limits=budget.limits,**FLAGS)
    try:
        budget.charge(plan['preflight_counts']['operations'])
        if candidate_vector!=plan.get('candidate_vector')or plan.get('program')!=dict(target='mu',q=6,C='32',claim='critical')or plan.get('layout')!=LAYOUT or plan.get('source_constructor')!=NATIVE_CONSTRUCTOR:raise ValueError('fixed complete mathematical plan/candidate')
        if plan.get('assignment')!=[2*n+1 for n in range(1,plan['H']+1)]or plan.get('baseline')!=[0]*plan['H']:raise ValueError('complete fixed formal assignments')
        instance=native['instance'];X=plan['X'];H=plan['H'];p=plan['prime'];values=plan['assignment']
        if instance['target']!='mu'or instance['horizon']!=H or len(instance['square_groups'])!=366 or len(instance['relation_groups'])!=613:raise ValueError('complete native scalar source layout')
        if native['gram_specs']!={'full_child':15,'full_parent':15,'storage_K':15}:raise ValueError('complete original three Gram specification; K supplied by signed storage transport')
        blocks=native['gram_blocks'];storage=native['storage_blocks']
        if set(blocks)!={'full_child','full_parent'}or len(blocks['full_child'])!=2*X or len(blocks['full_parent'])!=X or any(len(row)!=15 for rows in blocks.values()for row in rows):raise ValueError('complete native regional state coverage')
        if storage!=dict(kind='signed_storage_increment',child=blocks['full_child'],parent=blocks['full_parent'],child_multiplier='1',parent_multiplier='-4'):raise ValueError('signed parent storage source')
        E=ExactEvaluator(p,H,budget);w=[E.coefficient(s)for s in candidate_vector];out['assignment']=values;out['baseline']=plan['baseline'];out['square_values']=[];out['relation_values']=[];row=[F(0)]*1957
        def report(phase):
            if checkpoint:checkpoint(dict(phase=phase,counts=budget.counts(),**FLAGS))
        square=[0,0];relation=[0,0]
        for i,group in enumerate(instance['square_groups']):
            v=[F(0),F(0)]
            if type(group)is not list:raise ValueError('native square group list')
            for term in group:
                if type(term)is not dict or set(term)!={'weight','poly'}:raise ValueError('native square term schema')
                q=budget.rational(term['weight']);a,b=E.pair(term['poly'],values);E.coefficient(term['weight']);v[0]=E.add(v[0],E.mul(q,E.mul(a,a)));v[1]=E.add(v[1],E.mul(q,E.mul(b,b)))
            row[i]=E.add(v[0],-v[1]);raw=list(map(str,v));budget.charge(4);v=[E.coefficient(str(n))*w[i]%p for n in v];square=[(a+b)%p for a,b in zip(square,v)];out['square_values'].append(dict(index=i,value=v[0],baseline=v[1],exact_value=raw[0],exact_baseline=raw[1]))
        report('squares_evaluated')
        for i,group in enumerate(instance['relation_groups']):
            v=[F(0),F(0)]
            if type(group)is not list:raise ValueError('native relation group list')
            for term in group:
                if type(term)is not dict or set(term)!={'spec','multiplier'}:raise ValueError('native relation term schema')
                a,b=E.relation_pair(term['spec'],values);c,d=E.pair(term['multiplier'],values);v[0]=E.add(v[0],E.mul(a,c));v[1]=E.add(v[1],E.mul(b,d))
            row[366+2*i]=E.add(v[0],-v[1]);row[367+2*i]=-row[366+2*i];raw=list(map(str,v));beta=(w[366+2*i]-w[367+2*i])%p;budget.charge(5);v=[E.coefficient(str(a))*beta%p for a in v];relation=[(a+b)%p for a,b in zip(relation,v)];out['relation_values'].append(dict(index=i,value=v[0],baseline=v[1],exact_value=raw[0],exact_baseline=raw[1]))
        report('relations_evaluated')
        states={k:[list(zip(*(E.pair(poly,values)for poly in state)))for state in rows]for k,rows in blocks.items()};gram=[];gram_total=[0,0];pairs=[(i,j)for i in range(15)for j in range(i,15)]
        for z,name in enumerate(LAYOUT['gram_order']):
            v=[0,0];exact_columns=[]
            regions=[('full_child',1)]if name=='full_child'else[('full_parent',1)]if name=='full_parent'else[('full_child',1),('full_parent',-4)]
            for t,(i,j)in enumerate(pairs):
                column=[F(0),F(0)];factor_pair=1 if i==j else 2
                for region,factor in regions:
                    for a,b in states[region]:
                        factor_q=F(factor_pair*factor);column[0]=E.add(column[0],E.mul(factor_q,E.mul(a[i],a[j])));column[1]=E.add(column[1],E.mul(factor_q,E.mul(b[i],b[j])))
                index=1597+120*z+t;row[index]=E.add(column[0],-column[1]);budget.charge(4);v[0]=(v[0]+E.coefficient(str(column[0]))*w[index])%p;v[1]=(v[1]+E.coefficient(str(column[1]))*w[index])%p;exact_columns.append(dict(value=str(column[0]),baseline=str(column[1])))
            gram_total=[(a+b)%p for a,b in zip(gram_total,v)];gram.append(dict(name=name,value=v[0],baseline=v[1],exact_columns=exact_columns))
        target_exact=target_pair(X,plan['program'],values,p,budget);native_target=E.pair(instance['lhs'],values)
        if target_exact!=native_target:raise ValueError('prefix target/native target disagreement')
        target=[E.coefficient(str(x))for x in target_exact];body=[(square[i]+relation[i]+gram_total[i])%p for i in range(2)];residual=[(target[i]-body[i])%p for i in range(2)];difference=(residual[0]-residual[1])%p;budget.charge(12)
        rhs=E.add(target_exact[0],-target_exact[1]);feedback=dict(schema='primitive-state-formal-identity-necessary-row-v1',width=1957,entries=[dict(index=i,coefficient=str(q))for i,q in enumerate(row)if q],rhs=str(rhs),zero_coordinates=[i for i,q in enumerate(row)if not q],scope='necessary constraint for this universal formal nonconstant identity; not a sufficient identity or cone condition',X=X,assignment=values,layout=LAYOUT)
        budget.charge(1+len(encoded(feedback))//64)
        row_dot=0
        for i,q in enumerate(row):budget.charge(2);row_dot=(row_dot+E.coefficient(str(q))*w[i])%p
        if (E.coefficient(str(rhs))-row_dot)%p!=difference:raise ValueError('exact feedback row/modular residual mismatch')
        out.update(complete=True,status='UNVERIFIED_COUNTEREXAMPLE'if difference else'NOT_REFUTED_BY_THIS_PROBE',gram_values=gram,target_values=target,target_exact_values=list(map(str,target_exact)),square_total=square,relation_total=relation,gram_total=gram_total,body_values=body,residual_values=residual,nonconstant_difference=difference,feedback_row=feedback,feedback_row_dot_mod_prime=row_dot,feedback_rhs_mod_prime=E.coefficient(str(rhs)),complete_native_source_evaluated=True,source_semantics_independently_verified=False,source_degree_bound_verified=False,slack_coordinates_excluded=list(range(1592,1597)),relation_spec_count=len(E.relations),source_denominators_invertible=True,prime_checked=True)
        report('probe_evaluated')
    except (ValueError,OverflowError,TimeoutError,KeyError,TypeError)as error:
        out.update(status='UNKNOWN',complete=False,reason=str(error),error_type=type(error).__name__,nonconstant_difference=None,complete_native_source_evaluated=False)
    out['counts']=budget.counts()
    if len(encoded(out))>budget.limits['max_receipt_bytes']:
        out={k:out[k]for k in ['schema','program','source_constructor','X','H','prime','spec','limits','counts',*FLAGS]};out.update(status='UNKNOWN',complete=False,reason='probe receipt byte cap',nonconstant_difference=None)
    return out

NATIVE_CONSTRUCTOR='math-only fixed366/403/full15 source + complete primitive suffix multipliers; no metadata hashes or optional expanded verification'

def build_native(program,X,*,deadline,max_operations=100000000,max_source_cells=4000000,max_coefficient_bits=4096,max_horizon=27,max_terms=100000,checkpoint=None):
    """Complete math-only source and primitive suffixes; no archive digests."""
    if type(X)is not int or X<1 or 4*X-1>max_horizon:raise ValueError('bounded exact native horizon')
    b=Budget(deadline=deadline,max_operations=max_operations,max_source_cells=max_source_cells,max_coefficient_bits=max_coefficient_bits,max_polynomial_terms=max_terms)
    out=MATH_NATIVE.build_affine(program,X,max_horizon=max_horizon,max_operations=max_operations,max_terms=max_terms,max_coefficient_bits=max_coefficient_bits,max_retained_cells=max_source_cells)
    b.charge();H=4*X-1;E=ExactEvaluator(65537,H,b);blocks=out['gram_blocks']
    if set(blocks)!={'full_child','full_parent'}or len(blocks['full_child'])!=2*X or len(blocks['full_parent'])!=X:raise ValueError('complete affine base states')
    factors={}
    for n in range(1,H+1):
        # H trial factors, at most H divisions and bounded exponents.
        b.charge(4*H+16);factors[n]=LANGUAGE.factor_witness(n,max_n=H,max_operations=4*H+16)
    specs={f:[]for f in NATIVE.SPEC['primitive_families']};specs['unit']=[dict(kind='unit')]
    for n in range(1,H+1):
        b.charge(8);specs['norm'].append(dict(kind='norm',n=n,factors=factors[n]))
        if len(factors[n])==1:p,e=factors[n][0];specs['prime_power'].append(dict(kind='prime_power',p=p,e=e))
        if any(e>1 for p,e in factors[n]):specs['squarefree_zero'].append(dict(kind='squarefree_zero',n=n))
        if n>=2:specs['inverse_row'].append(dict(kind='inverse_row',n=n))
    for a in range(1,H+1):
        for c in range(a,H+1):
            b.charge(8);specs['gcd_product'].append(dict(kind='gcd_product',a=a,b=c,factors_a=factors[a],factors_b=factors[c]))
            if a>=2 and a*c<=H and math.gcd(a,c)==1:specs['coprime_product'].append(dict(kind='coprime_product',a=a,b=c))
    suffix={};retained=out['math_source_counts']['retained_cells']
    def parse(serial,t):
        nonlocal retained
        b.charge(len(serial)*4+1);p=LANGUAGE.load_poly(serial)
        if len(p)>max_terms or any(len(m)>2 or any(n>t for n in m)for m in p):raise ValueError('complete bounded native state degree/horizon')
        for q in p.values():E.checked(q)
        return p
    def merge(p,q):
        r=dict(p);b.charge(len(p))
        for m,v in q.items():
            v=E.add(r.get(m,F(0)),v)
            if v:r[m]=v
            else:r.pop(m,None)
        if len(r)>max_terms:raise OverflowError('complete suffix polynomial term cap')
        return r
    for region in NATIVE.SPEC['regions']:
        ts=list(range(X,2*X)if region=='parent'else range(2*X,4*X));rows=blocks['full_'+region]
        if any(len(row)!=15 for row in rows):raise ValueError('full15 state dimension')
        running=[{}for _ in range(15)]
        for t,state in reversed(list(zip(ts,rows))):
            running=[merge(p,parse(q,t))for p,q in zip(running,state)];suffix[region,t]=running;b.cells(retained+sum(len(p)for v in suffix.values()for p in v))
    groups=[]
    descriptors=[dict(primitive_family=f,region=r,atom_index=i)for f in NATIVE.SPEC['primitive_families']for r in NATIVE.SPEC['regions']for i in range(15)]
    for desc in descriptors:
        region=desc['region'];ts=list(range(X,2*X)if region=='parent'else range(2*X,4*X));group=[]
        for spec in specs[desc['primitive_family']]:
            b.charge(2);anchor=NATIVE._anchor(spec)
            if anchor>ts[-1]:continue
            p=suffix[region,max(ts[0],anchor)][desc['atom_index']]
            if len(p)>max_source_cells-retained:raise OverflowError('retained primitive source cell cap before serialization')
            retained+=len(p);b.charge(len(p)*4+1);serial=LANGUAGE.dump_poly(p);group.append(dict(spec=spec,multiplier=serial))
        groups.append(group)
    out['instance']['relation_groups'].extend(groups);out.update(gram_program=NATIVE.SPEC,primitive_state_spec=NATIVE.SPEC,probe_constructor=NATIVE_CONSTRUCTOR,probe_construction_counts=b.counts(),probe_primitive_retained_cells=retained,probe_optional_expanded_hashes=False)
    if checkpoint:checkpoint(dict(phase='complete_native_source_built',counts=b.counts(),**FLAGS))
    return out

class NativeSourceGuard(BaseException):
    """Unswallowable by legacy except Exception; converted only outside tracing."""


def build_native_metered(program,X,*,deadline,max_line_events=150000000,max_operations=50000000,max_source_cells=4000000,max_coefficient_bits=4096,max_horizon=27,max_terms=100000,checkpoint=None):
    """One-thread Python LINE_EVENTS cap across ALL nested source helpers.

    Explicit runtime proxy, not arithmetic or machine-instruction work. Exact
    operation diagnostics overlap these events and are not charged twice.
    """
    import sys
    if type(max_line_events)is not int or not 1<=max_line_events<=150000000:raise ValueError('bounded aggregate source line-event cap')
    if type(deadline)not in (int,float)or not math.isfinite(deadline):raise ValueError('finite source deadline')
    previous=sys.gettrace();events=0;guard_reason=None;native=None
    def trace(frame,event,arg):
        nonlocal events,guard_reason
        if event=='line':
            events+=1
            if events>max_line_events:guard_reason='aggregate native source LINE_EVENTS cap';raise NativeSourceGuard(guard_reason)
            if events%1024==0 and time.monotonic()>deadline:guard_reason='native source cooperative deadline';raise NativeSourceGuard(guard_reason)
        return trace
    try:
        sys.settrace(trace)
        try:
            native=build_native(program,X,deadline=deadline,max_operations=max_operations,max_source_cells=max_source_cells,max_coefficient_bits=max_coefficient_bits,max_horizon=max_horizon,max_terms=max_terms,checkpoint=None)
        except NativeSourceGuard:
            # CPython disables a raising tracer. Conversion occurs here, outside
            # the legacy call, and no result is allowed after this guard fired.
            raise OverflowError(guard_reason or 'native source guard') from None
        if guard_reason is not None or sys.gettrace()is not trace:raise OverflowError(guard_reason or 'native source tracer removed during construction')
    finally:
        sys.settrace(previous)
        if sys.gettrace()is not previous:raise RuntimeError('native source previous tracer restoration failed')
    if time.monotonic()>deadline:raise TimeoutError('native source final deadline')
    native['probe_source_meter']=dict(metric='all Python LINE_EVENTS during complete native source call',line_events=events,cap=max_line_events,nested_resets_counted=True,one_affine_source_build=True,optional_expanded_hashes=False)
    if checkpoint:checkpoint(dict(phase='complete_native_source_built',source_meter=native['probe_source_meter'],**FLAGS))
    return native
