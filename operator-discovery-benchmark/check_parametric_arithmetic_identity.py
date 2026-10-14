"""Independent bounded kernel for universal FORMAL_EQ in a finite-sum fragment.

No certificate producer imports, finite sampling, Mobius promotion or estimates.
Opaque arithmetic atoms retain their exact syntax; source adapters must separately
bind project domains and horizons. Ratio atoms use denominator-zero extension 0;
scaled roots use negative-input extension 0 and 0**0=1. Actual arithmetic
nonzero and positive domains require independent source binding. Resource
exhaustion gives no formal theorem.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import time

SCHEMA='parametric-arithmetic-identity-v1'
LIMITS=dict(max_operations=25000000,max_ast_nodes=50000,max_proof_nodes=4096,
            max_ring_cells=20000,max_coefficient_bits=4096,max_depth=128,
            max_receipt_bytes=16777216)
FLAGS=dict(candidate_admitted=False,full_target_proved=False,global_bound_proved=False,
           RH_proved=False,inequality_proved=False,MU_EQ_proved=False)


def require(test,message):
    if not test:raise ValueError(message)


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
def digest(value):return hashlib.sha256(encoded(value)).hexdigest()


class Budget:
    def __init__(self,limits,deadline):
        require(type(limits)is dict and set(limits)==set(LIMITS) and all(type(v)is int and 0<v<=LIMITS[k] for k,v in limits.items()),'strict authorized formal replay limits')
        require(deadline is None or type(deadline)in (int,float) and math.isfinite(deadline),'finite absolute formal replay deadline')
        self.limits=limits;self.deadline=deadline;self.operations=0;self.peak_ring_cells=0;self.ring_fill_cells=0
    def charge(self,n=1):
        self.operations+=n
        if self.operations>self.limits['max_operations']:raise OverflowError('formal replay operation cap')
        if self.deadline is not None and time.monotonic()>self.deadline:raise TimeoutError('formal replay deadline')
    def rational(self,text):
        self.charge();require(type(text)is str and 0<len(text)<=4*self.limits['max_coefficient_bits']+4 and all(c in '0123456789+-/' for c in text),'bounded explicit exact coefficient text')
        value=F(text);require(str(value)==text,'canonical exact coefficient text');return self.check_q(value)
    def check_q(self,value):
        self.charge()
        if max(abs(value.numerator).bit_length(),value.denominator.bit_length())>self.limits['max_coefficient_bits']:raise OverflowError('formal exact coefficient bit cap')
        return value
    def cells(self,value):
        self.charge();self.peak_ring_cells=max(self.peak_ring_cells,value)
        if value>self.limits['max_ring_cells']:raise OverflowError('formal local ring cell cap')
    def fill(self,n):self.ring_fill_cells+=n;self.charge(n)


class Ring:
    """Exact local commuting polynomial arithmetic; opaque atoms stay distinct."""
    def __init__(self,budget,atom_degrees=None):self.budget=budget;self.atom_degrees={} if atom_degrees is None else atom_degrees
    def constant(self,q):return {():q} if q else {}
    def atom(self,key,degree):self.atom_degrees[key]=degree;return {(key,):F(1)}
    def size(self,poly):
        self.budget.charge(len(poly)+1);return sum(len(m)+1 for m in poly)
    def add(self,a,b):
        result=dict(a);self.budget.charge(self.size(a));self.budget.cells(self.size(a)+self.size(b)+self.size(result))
        for monomial,value in b.items():
            q=self.budget.check_q(result.get(monomial,F(0))+value);self.budget.charge(len(monomial)+1)
            if q:result[monomial]=q
            else:result.pop(monomial,None)
            self.budget.cells(self.size(result));self.budget.fill(len(monomial)+1)
        return result
    def multiply(self,a,b,boolean_atoms=frozenset()):
        result={};self.budget.cells(self.size(a)+self.size(b))
        for ma,qa in a.items():
            for mb,qb in b.items():
                self.budget.charge(len(ma)+len(mb)+1)
                if len(ma)+len(mb)+1>self.budget.limits['max_ring_cells']:raise OverflowError('formal prospective monomial factor cap')
                combined=sorted(ma+mb);m=tuple(k for i,k in enumerate(combined) if k not in boolean_atoms or i==0 or combined[i-1]!=k)
                q=self.budget.check_q(self.budget.check_q(qa*qb)+result.get(m,F(0)))
                if q:result[m]=q
                else:result.pop(m,None)
                self.budget.fill(len(m)+1);self.budget.cells(self.size(a)+self.size(b)+self.size(result))
        return result


class AST:
    def __init__(self,nodes,context,budget):
        require(type(context)is dict and set(context)=={'integer_parameters','functions'},'explicit typed formal context')
        params=context['integer_parameters'];functions=context['functions']
        require(type(params)is list and type(functions)is list and len(params)+len(functions)<=128,'bounded declared formal names')
        self.parameters={};self.functions={};self.budget=budget;self.nodes=nodes;self.keys=[];self.free=[];self.depth=[]
        def name(value):return type(value)is str and 0<len(value)<=64 and value.isidentifier()
        for p in params:
            require(type(p)is dict and set(p)=={'name','lower'} and name(p['name']) and p['name']not in self.parameters and type(p['lower'])is int,'unique integer parameter declarations')
            require(abs(p['lower']).bit_length()<=budget.limits['max_coefficient_bits'],'bounded declared integer lower endpoint');self.parameters[p['name']]=p['lower'];budget.charge()
        for f in functions:
            require(type(f)is dict and set(f)=={'name','arity','definition_hash'} and name(f['name']) and f['name']not in self.functions and type(f['arity'])is int and 0<=f['arity']<=16 and _hash(f['definition_hash']),'unique hash-bound opaque commuting function declarations')
            self.functions[f['name']]=f;budget.charge()
        require(type(nodes)is list,'explicit typed AST DAG')
        if len(nodes)>budget.limits['max_ast_nodes']:raise OverflowError('formal AST node cap')
        for i,node in enumerate(nodes):
            require(type(node)is dict and set(node)=={'sort','op','args','data'},'strict typed AST node fields')
            sort,op,args,data=(node[k] for k in ('sort','op','args','data'))
            require(sort in ('Int','Bool','Poly') and type(op)is str and type(args)is list and type(data)is dict and all(type(j)is int and 0<=j<i for j in args),'only earlier AST references')
            childsort=[nodes[j]['sort'] for j in args];budget.charge(len(args)+1)
            def signature(expected,fields=()):require(childsort==list(expected) and set(data)==set(fields),'typed AST operation '+op)
            if sort=='Int':
                if op=='int':
                    signature([],['value']);require(type(data['value'])is int and abs(data['value']).bit_length()<=budget.limits['max_coefficient_bits'],'bounded integer literal')
                elif op=='v':signature([],['name']);require(data['name']in self.parameters,'declared integer parameter')
                elif op=='bound':signature([],['index']);require(type(data['index'])is int and 0<=data['index']<budget.limits['max_depth'],'bounded deBruijn index')
                elif op in ('iadd','imul','isub','min','max'):signature(['Int','Int'])
                elif op=='scaled_root':
                    signature(['Int'],['rounding','coefficient','power','negative_extension'])
                    require(data['rounding']in ('floor','ceiling') and data['negative_extension']=='zero','distinct exact root conventions')
                    require(budget.rational(data['coefficient'])>=0 and budget.rational(data['power'])>=0,'nonnegative canonical rational root parameters')
                else:raise ValueError('unsupported integer operation')
            elif sort=='Bool':
                if op in ('true','false'):signature([])
                elif op in ('le','lt','eq','divides','coprime'):signature(['Int','Int'])
                elif op=='not':signature(['Bool'])
                elif op in ('and','or'):signature(['Bool','Bool'])
                else:raise ValueError('unsupported Boolean operation')
            else:
                if op=='q':signature([],['value']);budget.rational(data['value'])
                elif op in ('x','embed'):signature(['Int'])
                elif op=='ratio':signature(['Int','Int'])
                elif op=='symbol':
                    require(set(data)=={'function'} and data['function']in self.functions and childsort==['Int']*self.functions[data['function']]['arity'],'declared hash-bound opaque function arity')
                elif op in ('add','mul'):signature(['Poly','Poly'])
                elif op=='scale':signature(['Poly'],['coefficient']);budget.rational(data['coefficient'])
                elif op=='guard':signature(['Bool','Poly'])
                elif op=='sum':signature(['Int','Int','Poly'],['binder']);require(name(data['binder']),'bounded cosmetic binder label')
                else:raise ValueError('unsupported polynomial operation, no MU primitive promotion')
            free=set().union(*(self.free[j] for j in args)) if args else set()
            if op=='bound':free={data['index']}
            if op=='sum':free=self.free[args[0]]|self.free[args[1]]|{k-1 for k in self.free[args[2]] if k>0}
            depth=1+max((self.depth[j] for j in args),default=0)
            if depth>budget.limits['max_depth']:raise OverflowError('typed AST depth cap')
            self.free.append(free);self.depth.append(depth)
            semantic_data={} if op=='sum' else data
            self.keys.append(self.key(sort,op,[self.keys[j] for j in args],semantic_data))
    def key(self,sort,op,args,data):
        value=[sort,op,args,data];payload=encoded(value);self.budget.charge(len(payload)//64+1);return hashlib.sha256(payload).hexdigest()
    def equivalent(self,a,b):return self.keys[a]==self.keys[b]
    def shifted_key(self,index,delta,cutoff=0,memo=None):
        memo={} if memo is None else memo;token=(index,delta,cutoff)
        if token in memo:return memo[token]
        node=self.nodes[index];op=node['op'];data=dict(node['data']);args=node['args'];self.budget.charge()
        if op=='bound' and data['index']>=cutoff:
            data['index']+=delta;require(data['index']>=0,'capture-free deBruijn shift')
        shifted=[self.shifted_key(j,delta,cutoff+(op=='sum' and k==2),memo) for k,j in enumerate(args)]
        key=self.key(node['sort'],op,shifted,{} if op=='sum' else data);memo[token]=key;return key


def _hash(value):return type(value)is str and len(value)==64 and all(c in '0123456789abcdef' for c in value)


class Normalizer:
    def __init__(self,ast,boolean=False):
        self.ast=ast;self.budget=ast.budget;self.ring=Ring(self.budget);self.boolean=boolean;self.boolatoms=set();self.cache={};self.resident=0
    def remember(self,key,poly):
        cells=self.ring.size(poly);self.resident+=cells;self.budget.cells(self.resident);self.cache[key]=poly;return poly
    def poly(self,index):
        key=('poly',index)
        if key in self.cache:return self.cache[key]
        node=self.ast.nodes[index];op=node['op'];args=node['args'];require(node['sort']=='Poly','polynomial normal form sort')
        if op=='q':result=self.ring.constant(self.budget.rational(node['data']['value']))
        elif op=='add':result=self.ring.add(self.poly(args[0]),self.poly(args[1]))
        elif op=='mul':result=self.ring.multiply(self.poly(args[0]),self.poly(args[1]),self.boolatoms)
        elif op=='scale':result=self.ring.multiply(self.ring.constant(self.budget.rational(node['data']['coefficient'])),self.poly(args[0]),self.boolatoms)
        elif op=='guard' and self.boolean:result=self.ring.multiply(self.boolean_poly(args[0]),self.poly(args[1]),self.boolatoms)
        else:result=self.ring.atom(self.ast.keys[index],0)
        return self.remember(key,result)
    def boolean_poly(self,index):
        key=('bool',index)
        if key in self.cache:return self.cache[key]
        node=self.ast.nodes[index];op=node['op'];args=node['args'];require(node['sort']=='Bool','Boolean normal form sort')
        one=self.ring.constant(F(1));minus=self.ring.constant(F(-1))
        if op=='true':result=one
        elif op=='false':result={}
        elif op=='not':result=self.ring.add(one,self.ring.multiply(minus,self.boolean_poly(args[0]),self.boolatoms))
        elif op=='and':result=self.ring.multiply(self.boolean_poly(args[0]),self.boolean_poly(args[1]),self.boolatoms)
        elif op=='or':
            a=self.boolean_poly(args[0]);b=self.boolean_poly(args[1]);result=self.ring.add(self.ring.add(a,b),self.ring.multiply(minus,self.ring.multiply(a,b,self.boolatoms),self.boolatoms))
        else:
            # Integer total order: a<b is exactly not(b<=a), including equality.
            atom=self.ast.key('Bool','le',[self.ast.keys[args[1]],self.ast.keys[args[0]]],{}) if op=='lt' else self.ast.keys[index]
            self.boolatoms.add(atom);result=self.ring.atom(atom,0)
            if op=='lt':result=self.ring.add(one,self.ring.multiply(minus,result,self.boolatoms))
        return self.remember(key,result)


def _ring_equal(ast,lhs,rhs,boolean=False):
    normal=Normalizer(ast,boolean);return normal.poly(lhs)==normal.poly(rhs)


def _sum_parts(ast,index):
    node=ast.nodes[index];require(node['sort']=='Poly' and node['op']=='sum','explicit finite sum operand');return node['args']


def _linear_sums(ast,index,lo,hi):
    """Collect an external rational combination of exactly the same finite sums."""
    node=ast.nodes[index];op=node['op'];args=node['args'];budget=ast.budget;budget.charge()
    if op=='q':require(budget.rational(node['data']['value'])==0,'no omitted finite domain constant');return []
    if op=='add':
        a=_linear_sums(ast,args[0],lo,hi);b=_linear_sums(ast,args[1],lo,hi)
        budget.charge(len(a)+len(b))
        if len(a)+len(b)>budget.limits['max_ring_cells']:raise OverflowError('formal sum-linear term cap')
        return a+b
    if op=='scale':
        q=budget.rational(node['data']['coefficient']);return [(budget.check_q(q*c),body) for c,body in _linear_sums(ast,args[0],lo,hi)]
    if op=='mul':
        for a,b in ((args[0],args[1]),(args[1],args[0])):
            if ast.nodes[a]['op']=='q':
                q=budget.rational(ast.nodes[a]['data']['value']);return [(budget.check_q(q*c),body) for c,body in _linear_sums(ast,b,lo,hi)]
    a,b,body=_sum_parts(ast,index);require(ast.equivalent(a,lo) and ast.equivalent(b,hi),'identical complete inclusive sum domains');return [(F(1),body)]


def replay_rule(ast,proof,index):
    node=proof[index];budget=ast.budget
    require(type(node)is dict and set(node)=={'rule','scope','judgment','premises','lhs','rhs','data'},'strict formal proof node fields')
    rule,scope,premises,lhs,rhs,data=(node[k] for k in ('rule','scope','premises','lhs','rhs','data'))
    require(node['judgment']=='FORMAL_EQ','no MU_EQ or arithmetic-to-formal promotion')
    require(type(scope)is int and 0<=scope<=budget.limits['max_depth'] and type(premises)is list and all(type(p)is int and 0<=p<index for p in premises),'only earlier scoped proof references')
    require(type(lhs)is int and type(rhs)is int and 0<=lhs<len(ast.nodes) and 0<=rhs<len(ast.nodes) and ast.nodes[lhs]['sort']==ast.nodes[rhs]['sort']=='Poly','typed polynomial equality operands')
    require(all(k<scope for k in ast.free[lhs]|ast.free[rhs]),'proof operands remain in declared binder scope')
    fields={'SUM_PULL':{'factor','body'},'RANGE_SPLIT':{'cut'}}.get(rule,set())
    require(type(data)is dict and set(data)==fields,'explicit whitelisted rule side conditions')
    for value in data.values():require(type(value)is int and 0<=value<len(ast.nodes),'bounded side-condition AST reference')
    budget.charge(len(premises)+1)
    def eq(a,b):return ast.equivalent(a,b)
    def premise_count(n):require(len(premises)==n,'complete rule premise list')
    def same_scope(p):require(proof[p]['scope']==scope,'same local equality scope')
    if rule in ('REFL','ALPHA'):
        premise_count(0);require(eq(lhs,rhs),'capture-free structural alpha equivalence')
    elif rule=='SYM':
        premise_count(1);p=premises[0];same_scope(p);require(eq(lhs,proof[p]['rhs']) and eq(rhs,proof[p]['lhs']),'exact reversed equality')
    elif rule=='TRANS':
        premise_count(2);a,b=premises;same_scope(a);same_scope(b)
        require(eq(lhs,proof[a]['lhs']) and eq(proof[a]['rhs'],proof[b]['lhs']) and eq(rhs,proof[b]['rhs']),'complete transitive equality chain')
    elif rule in ('RING','GUARD_BOOL'):
        premise_count(0);require(_ring_equal(ast,lhs,rhs,rule=='GUARD_BOOL'),'independent exact local ring/Boolean identity')
    elif rule=='CONGRUENCE':
        a=ast.nodes[lhs];b=ast.nodes[rhs]
        require(a['op']==b['op'] and a['op']!='sum' and a['data']==b['data'] and len(a['args'])==len(b['args']),'same typed congruence constructor')
        poly_pairs=[]
        for x,y in zip(a['args'],b['args']):
            if ast.nodes[x]['sort']=='Poly':poly_pairs.append((x,y))
            else:require(eq(x,y),'unchanged exact integer/predicate congruence operands')
        premise_count(len(poly_pairs))
        for p,(x,y) in zip(premises,poly_pairs):same_scope(p);require(eq(x,proof[p]['lhs']) and eq(y,proof[p]['rhs']),'complete ordered polynomial child equality premises')
    elif rule=='SUM_CONGRUENCE':
        premise_count(1);a,b,body=_sum_parts(ast,lhs);c,d,other=_sum_parts(ast,rhs);p=proof[premises[0]]
        require(eq(a,c) and eq(b,d) and p['scope']==scope+1 and eq(body,p['lhs']) and eq(other,p['rhs']),'capture-free finite sum congruence')
    elif rule=='SUM_LINEAR':
        premise_count(0);lo,hi,body=_sum_parts(ast,lhs);parts=_linear_sums(ast,rhs,lo,hi);normal=Normalizer(ast);combined={}
        for coefficient,term in parts:combined=normal.ring.add(combined,normal.ring.multiply(normal.ring.constant(coefficient),normal.poly(term)))
        require(normal.poly(body)==combined,'complete finite sum linearity with exact multiplicity')
    elif rule=='SUM_PULL':
        premise_count(0);lo,hi,body=_sum_parts(ast,lhs);a=ast.nodes[body];b=ast.nodes[rhs]
        require(a['op']=='mul' and b['op']=='mul','explicit factor pull constructors')
        matched=False
        for factor,term in (a['args'],list(reversed(a['args']))):
            if not(eq(factor,data['factor']) and eq(term,data['body'])):continue
            if 0 in ast.free[factor]:continue
            outside=ast.shifted_key(factor,-1)
            for external,total in (b['args'],list(reversed(b['args']))):
                if ast.nodes[total]['op']!='sum':continue
                x,y,inside=_sum_parts(ast,total)
                if outside==ast.keys[external] and eq(lo,x) and eq(hi,y) and eq(term,inside):matched=True
        require(matched,'factor independence and capture-free bound-slot shift')
    elif rule in ('PARTITION','RANGE_SPLIT'):
        premise_count(0);lo,hi,body=_sum_parts(ast,lhs);out=ast.nodes[rhs]
        require(out['op']=='add','complete two-piece finite partition')
        predicates=[]
        for child in out['args']:
            a,b,term=_sum_parts(ast,child);require(eq(a,lo) and eq(b,hi),'partition preserves complete finite domain')
            guard=ast.nodes[term];require(guard['op']=='guard' and eq(guard['args'][1],body),'partition preserves every summand and multiplicity')
            predicates.append(guard['args'][0])
        normal=Normalizer(ast,True);combined=normal.ring.add(normal.boolean_poly(predicates[0]),normal.boolean_poly(predicates[1]))
        require(combined==normal.ring.constant(F(1)),'exact complementary guards including equality boundary')
        if rule=='RANGE_SPLIT':
            inside,outside=(ast.nodes[p] for p in predicates)
            require(ast.nodes[data['cut']]['sort']=='Int' and all(k<scope for k in ast.free[data['cut']]) and ast.shifted_key(data['cut'],1)==ast.keys[inside['args'][1]],'range cutoff stays outside the binder with capture-free shift')
            require(inside['op']=='le' and outside['op']=='lt' and ast.nodes[inside['args'][0]]['op']=='bound' and ast.nodes[inside['args'][0]]['data']['index']==0 and eq(inside['args'][0],outside['args'][1]) and eq(inside['args'][1],outside['args'][0]),'inclusive lower piece and strict complementary upper piece')
    else:raise ValueError('unsupported formal proof rule')


def verify_certificate(certificate,*,deadline=None,max_operations=25000000,max_ast_nodes=50000,
                       max_proof_nodes=4096,max_ring_cells=20000,max_coefficient_bits=4096,
                       max_depth=128,max_receipt_bytes=16777216,expected_source_bindings=None,
                       expected_recipe_ids=None,expected_context=None,expected_function_bindings=None,
                       expected_roots=None,expected_lhs_tree=None,expected_rhs_tree=None):
    """Verify only the declared parametric FORMAL_EQ; no full detector admission."""
    requested=dict(max_operations=max_operations,max_ast_nodes=max_ast_nodes,max_proof_nodes=max_proof_nodes,max_ring_cells=max_ring_cells,max_coefficient_bits=max_coefficient_bits,max_depth=max_depth,max_receipt_bytes=max_receipt_bytes)
    budget=Budget(requested,deadline)
    require(type(certificate)is dict,'explicit bounded formal certificate');raw=encoded(certificate)
    if len(raw)>max_receipt_bytes:raise OverflowError('formal receipt byte cap')
    budget.charge(len(raw)//64+1)
    require(certificate.get('schema')==SCHEMA and certificate.get('judgment')=='FORMAL_EQ','known strictly formal certificate judgment')
    status=certificate.get('status');require(status in ('proved','unknown') and certificate.get('complete')is (status=='proved'),'strict bounded formal completion')
    for key in FLAGS:
        if key in certificate:require(certificate[key]is False,'no candidate/inequality/MU promotion '+key)
    for key in ('certified','exact_admission','infeasibility_proved','accepted_proposal'):
        if key in certificate:require(certificate[key]is False,'unsupported promotion '+key)
    limits=certificate.get('limits');Budget(limits,deadline)
    sources=certificate.get('source_bindings');recipes=certificate.get('recipe_ids')
    require(type(sources)is dict and len(sources)<=256 and all(type(k)is str and 0<len(k)<=256 and _hash(v) for k,v in sources.items()),'bounded exact source bindings')
    require(type(recipes)is list and len(recipes)<=4096 and all(type(r)is str and 0<len(r)<=256 for r in recipes) and len(set(recipes))==len(recipes),'explicit unique covered source recipe IDs')
    if expected_source_bindings is not None:require(sources==expected_source_bindings,'trusted exact source definition bindings')
    if expected_recipe_ids is not None:require(recipes==expected_recipe_ids,'exact independently adapted source coverage')
    if expected_context is not None:require(certificate.get('context')==expected_context,'same parametric source context')
    ast=AST(certificate.get('ast'),certificate.get('context'),budget)
    if expected_function_bindings is not None:require({name:f['definition_hash'] for name,f in ast.functions.items()}==expected_function_bindings,'independently bound opaque coefficient definitions')
    proof=certificate.get('proof');require(type(proof)is list,'explicit acyclic formal proof DAG')
    if len(proof)>max_proof_nodes:raise OverflowError('formal proof node cap')
    lhs,rhs=certificate.get('lhs'),certificate.get('rhs')
    suppressed=status=='unknown' and lhs is None and rhs is None
    if suppressed:
        for i in range(len(proof)):replay_rule(ast,proof,i)
        counts=certificate.get('counts');require(type(counts)is dict and set(counts)=={'operations','ast_nodes','proof_nodes','peak_ring_cells','receipt_bytes'} and all(type(v)is int and v>=0 for v in counts.values()),'strict UNKNOWN retained counters')
        require(counts['ast_nodes']==len(ast.nodes) and counts['proof_nodes']==len(proof) and counts['receipt_bytes']==len(raw) and certificate.get('conclusion')is None and type(certificate.get('reason'))is str and bool(certificate['reason']),'bounded UNKNOWN has no theorem roots/conclusion')
        return dict(verified=True,complete=False,FORMAL_EQ_verified=False,judgment=None,source_semantics_independently_bound=False,covered_recipe_ids=recipes,reason=certificate['reason'],audit_operations=budget.operations,audit_peak_ring_cells=budget.peak_ring_cells,audit_ring_fill_cells=budget.ring_fill_cells,independent_audit_work_reserve=budget.operations+len(raw)+len(ast.nodes)+len(proof)+1,**FLAGS)
    require(type(lhs)is int and type(rhs)is int and 0<=lhs<len(ast.nodes) and 0<=rhs<len(ast.nodes) and ast.nodes[lhs]['sort']==ast.nodes[rhs]['sort']=='Poly' and not(ast.free[lhs]|ast.free[rhs]),'closed universally parametric polynomial roots')
    if expected_roots is not None:require(expected_roots==dict(lhs=ast.keys[lhs],rhs=ast.keys[rhs]),'independently adapted formal source roots')
    if expected_lhs_tree is not None or expected_rhs_tree is not None:
        require(expected_lhs_tree is not None and expected_rhs_tree is not None and expected_context is not None,'complete trusted named source trees and context')
        left=translate_named_tree(expected_lhs_tree,expected_context,budget);right=translate_named_tree(expected_rhs_tree,expected_context,budget)
        require(ast.keys[lhs]==left['semantic_hash'] and ast.keys[rhs]==right['semantic_hash'],'independent named source to deBruijn binding')
    for i in range(len(proof)):replay_rule(ast,proof,i)
    counts=certificate.get('counts')
    require(type(counts)is dict and set(counts)=={'operations','ast_nodes','proof_nodes','peak_ring_cells','receipt_bytes'} and all(type(v)is int and v>=0 for v in counts.values()),'strict declared producer counts')
    require(counts['ast_nodes']==len(ast.nodes) and counts['proof_nodes']==len(proof) and counts['receipt_bytes']==len(raw),'complete declared DAG/byte counts')
    require(len(ast.nodes)<=limits['max_ast_nodes'] and len(proof)<=limits['max_proof_nodes'],'declared producer DAG caps')
    if status=='proved':
        require(counts['operations']<=limits['max_operations'] and counts['peak_ring_cells']<=limits['max_ring_cells'],'complete producer resource caps')
        conclusion=certificate.get('conclusion');require(type(conclusion)is int and 0<=conclusion<len(proof),'complete explicit formal conclusion')
        node=proof[conclusion];require(node['scope']==0 and ast.equivalent(node['lhs'],lhs) and ast.equivalent(node['rhs'],rhs),'same closed formal theorem conclusion')
    else:require(certificate.get('conclusion')is None and type(certificate.get('reason'))is str and bool(certificate['reason']),'explicit UNKNOWN with no formal conclusion')
    return dict(verified=True,complete=status=='proved',FORMAL_EQ_verified=status=='proved',judgment='FORMAL_EQ' if status=='proved' else None,
                lhs_semantic_hash=ast.keys[lhs],rhs_semantic_hash=ast.keys[rhs],context=certificate['context'],covered_recipe_ids=recipes,
                source_semantics_independently_bound=expected_source_bindings is not None and expected_context is not None and (expected_roots is not None or expected_lhs_tree is not None),
                formal_degree_or_project_horizon_inferred=False,numerical_sampling_used=False,
                audit_operations=budget.operations,audit_peak_ring_cells=budget.peak_ring_cells,audit_ring_fill_cells=budget.ring_fill_cells,
                independent_audit_work_reserve=budget.operations+len(raw)+len(ast.nodes)+len(proof)+1,**FLAGS)


def translate_named_tree(tree,context,budget):
    """Independent named-binder translation for audited source adapter trees."""
    nodes=[]
    def visit(term,stack,depth):
        budget.charge()
        if depth>budget.limits['max_depth']:raise OverflowError('named source tree depth cap')
        require(type(term)is list and term and type(term[0])is str,'explicit named source tree')
        op=term[0];data={};children=[]
        def arity(n):require(len(term)==n+1,'complete named source operands')
        if op=='int':arity(1);sort='Int';data={'value':term[1]}
        elif op=='v':
            arity(1);sort='Int';require(type(term[1])is str,'named integer variable')
            if term[1]in stack:op='bound';data={'index':stack[::-1].index(term[1])}
            else:data={'name':term[1]}
        elif op=='q':arity(1);sort='Poly';data={'value':term[1]}
        elif op in ('iadd','imul','isub','min','max'):arity(2);sort='Int';children=[visit(t,stack,depth+1) for t in term[1:]]
        elif op=='root':
            arity(3);sort='Int';require(type(term[2])is int and type(term[3])is int and term[2]>=0 and term[3]>0,'exact named rational root exponent')
            data={'rounding':'floor','coefficient':'1','power':str(F(term[2],term[3])),'negative_extension':'zero'};op='scaled_root';children=[visit(term[1],stack,depth+1)]
        elif op=='scaled_root':
            arity(4);sort='Int';data={'rounding':term[1],'coefficient':term[2],'power':term[3],'negative_extension':'zero'};children=[visit(term[4],stack,depth+1)]
        elif op in ('true','false'):arity(0);sort='Bool'
        elif op in ('le','lt','eq','divides','coprime','and','or'):arity(2);sort='Bool';children=[visit(t,stack,depth+1) for t in term[1:]]
        elif op=='not':arity(1);sort='Bool';children=[visit(term[1],stack,depth+1)]
        elif op in ('x','embed'):arity(1);sort='Poly';children=[visit(term[1],stack,depth+1)]
        elif op in ('ratio','add','mul','guard'):arity(2);sort='Poly';children=[visit(t,stack,depth+1) for t in term[1:]]
        elif op=='scale':arity(2);sort='Poly';data={'coefficient':term[1]};children=[visit(term[2],stack,depth+1)]
        elif op=='symbol':
            require(len(term)>=2 and type(term[1])is str,'explicit named opaque polynomial function');sort='Poly';data={'function':term[1]};children=[visit(t,stack,depth+1) for t in term[2:]]
        elif op=='sum':
            arity(4);sort='Poly';require(type(term[1])is str and term[1].isidentifier(),'named finite-sum binder')
            data={'binder':term[1]};children=[visit(term[2],stack,depth+1),visit(term[3],stack,depth+1),visit(term[4],stack+[term[1]],depth+1)]
        else:raise ValueError('unsupported named source operation')
        if len(nodes)>=budget.limits['max_ast_nodes']:raise OverflowError('named source node cap')
        node={'sort':sort,'op':op,'args':children,'data':data};nodes.append(node);return len(nodes)-1
    root=visit(tree,[],1);ast=AST(nodes,context,budget)
    require(not ast.free[root],'closed named source expression')
    return dict(ast=nodes,root=root,semantic_hash=ast.keys[root])


def from_tree(tree,context,*,deadline=None,**limits):
    """Bounded public adapter API, independent of the certificate producer."""
    caps=dict(LIMITS);caps.update(limits);budget=Budget(caps,deadline)
    result=translate_named_tree(tree,context,budget)
    return dict(result,audit_operations=budget.operations)
