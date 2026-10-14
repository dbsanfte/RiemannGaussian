"""Bounded symbolic FORMAL_EQ proof producer for guarded finite-sum identities.

Formal arrays are indexed by all integers. Source-domain and arithmetic-function
binding belong to the independently checked adapter, never finite-grid evidence.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import time

SCHEMA='parametric-arithmetic-identity-v1'
LIMITS=dict(max_operations=25000000,max_ast_nodes=50000,max_proof_nodes=4096,max_ring_cells=20000,max_coefficient_bits=4096,max_depth=128,max_receipt_bytes=16777216)


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
def digest(value):return hashlib.sha256(encoded(value)).hexdigest()

class Limit(Exception):pass

class Producer:
    def __init__(self,context,*,source_bindings=None,recipe_ids=None,limits=None,deadline=None):
        self.limits=dict(LIMITS if limits is None else limits)
        if set(self.limits)!=set(LIMITS) or any(type(v)is not int or not 0<v<=LIMITS[k] for k,v in self.limits.items()):raise ValueError('strict bounded producer limits')
        self.deadline=time.monotonic()+60 if deadline is None else deadline
        if type(self.deadline)not in (int,float) or not math.isfinite(self.deadline):raise ValueError('finite deadline')
        if type(context)is not dict or set(context)!={'integer_parameters','functions'}:raise ValueError('exact typed context fields')
        if any(type(context[k])is not list or len(context[k])>256 for k in context):raise ValueError('bounded context declarations')
        self.context=json.loads(encoded(context));self.params={};self.functions={}
        for record in self.context['integer_parameters']:
            if type(record)is not dict or set(record)!={'name','lower'} or type(record['name'])is not str or not record['name'] or len(record['name'])>256 or type(record['lower'])is not int or record['name'] in self.params:raise ValueError('distinct declared integer parameters')
            self.params[record['name']]=record['lower']
        for record in self.context['functions']:
            if type(record)is not dict or set(record)!={'name','arity','definition_hash'} or type(record['name'])is not str or not record['name'] or len(record['name'])>256 or type(record['arity'])is not int or not 0<=record['arity']<=128 or not self._hash(record['definition_hash']) or record['name'] in self.functions:raise ValueError('distinct bound formal polynomial functions')
            self.functions[record['name']]=record
        self.source_bindings=dict(source_bindings or {});self.recipe_ids=list(recipe_ids or [])
        if len(self.source_bindings)>256 or len(self.recipe_ids)>4096 or any(type(k)is not str or not k or len(k)>256 or not self._hash(v) for k,v in self.source_bindings.items()) or any(type(s)is not str or not s or len(s)>256 for s in self.recipe_ids) or len(set(self.recipe_ids))!=len(self.recipe_ids):raise ValueError('explicit source/recipe bindings')
        self.ast=[];self.proof=[];self._nodes={};self._proofs={};self._slots=[];self._depth=[];self._normalized={};self.operations=0;self.peak_ring_cells=0;self._dag_bytes=0
        self.charge(len(encoded(context))+len(encoded(self.source_bindings))+len(encoded(self.recipe_ids))+1)
    @staticmethod
    def _hash(h):return type(h)is str and len(h)==64 and all(c in '0123456789abcdef' for c in h)
    def charge(self,n=1):
        self.operations+=n
        if self.operations>self.limits['max_operations']:raise Limit('operation cap')
        if time.monotonic()>self.deadline:raise Limit('deadline')
    def rational(self,value):
        self.charge()
        if type(value)not in (str,int,F):raise ValueError('exact rational coefficient')
        if type(value)is str and (len(value)>4*self.limits['max_coefficient_bits']+4 or any(c not in '0123456789+-/' for c in value)):raise ValueError('bounded rational text')
        q=F(value)
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>self.limits['max_coefficient_bits']:raise Limit('coefficient bit cap')
        return q
    def node(self,op,args=(),data=None):
        self.charge();args=list(args);data={} if data is None else dict(data)
        if any(type(i)is not int or not 0<=i<len(self.ast) for i in args):raise ValueError('earlier AST references')
        sorts=[self.ast[i]['sort'] for i in args]
        if op=='int':
            sort='Int'
            if args or set(data)!={'value'} or type(data['value'])is not int:raise ValueError('integer literal')
            self.rational(data['value'])
        elif op=='v':
            sort='Int'
            if args or set(data)!={'name'} or data['name'] not in self.params:raise ValueError('declared integer parameter')
        elif op=='bound':
            sort='Int'
            if args or set(data)!={'index'} or type(data['index'])is not int or not 0<=data['index']<self.limits['max_depth']:raise ValueError('bounded deBruijn index')
        elif op in ('iadd','imul','isub','max','min'):
            sort='Int'
            if sorts!=['Int','Int'] or data:raise ValueError('binary exact integer operator')
        elif op=='scaled_root':
            sort='Int'
            if sorts!=['Int'] or set(data)!={'rounding','coefficient','power','negative_extension'} or data['rounding']not in ('floor','ceiling') or data['negative_extension']!='zero':raise ValueError('exact total scaled rational-root definition')
            for field in ('coefficient','power'):
                q=self.rational(data[field])
                if q<0:raise ValueError('nonnegative rational root parameters')
                data[field]=str(q)
        elif op in ('true','false'):
            sort='Bool'
            if args or data:raise ValueError('Boolean constant')
        elif op in ('le','lt','eq','divides','coprime'):
            sort='Bool'
            if sorts!=['Int','Int'] or data:raise ValueError('exact integer predicate')
        elif op=='not':
            sort='Bool'
            if sorts!=['Bool'] or data:raise ValueError('Boolean not')
        elif op in ('and','or'):
            sort='Bool'
            if sorts!=['Bool','Bool'] or data:raise ValueError('binary Boolean connective')
        elif op=='q':
            sort='Poly'
            if args or set(data)!={'value'}:raise ValueError('rational polynomial constant')
            data['value']=str(self.rational(data['value']))
        elif op=='x':
            sort='Poly'
            if sorts!=['Int'] or data:raise ValueError('formal integer-indexed indeterminate')
        elif op=='symbol':
            sort='Poly'
            if set(data)!={'function'} or data['function']not in self.functions or sorts!=['Int']*self.functions[data['function']]['arity']:raise ValueError('bound opaque polynomial-valued function')
        elif op in ('embed','ratio'):
            sort='Poly'
            if sorts!=['Int']*(1 if op=='embed' else 2) or data:raise ValueError('exact integer coefficient or total ratio')
        elif op in ('add','mul'):
            sort='Poly'
            if sorts!=['Poly','Poly'] or data:raise ValueError('binary polynomial ring operator')
        elif op=='scale':
            sort='Poly'
            if sorts!=['Poly'] or set(data)!={'coefficient'}:raise ValueError('rational scale')
            data['coefficient']=str(self.rational(data['coefficient']))
        elif op=='guard':
            sort='Poly'
            if sorts!=['Bool','Poly'] or data:raise ValueError('guarded polynomial')
        elif op=='sum':
            sort='Poly'
            if sorts!=['Int','Int','Poly'] or set(data)!={'binder'} or type(data['binder'])is not str or not data['binder'] or len(data['binder'])>256:raise ValueError('finite inclusive integer sum')
        else:raise ValueError('unsupported typed AST operator '+str(op))
        depth=1+max((self._depth[i] for i in args),default=0)
        if depth>self.limits['max_depth']:raise Limit('AST depth cap')
        slots=set()
        for k,i in enumerate(args):
            if op=='sum' and k==2:slots.update(j-1 for j in self._slots[i] if j>0)
            else:slots.update(self._slots[i])
        if op=='bound':slots.add(data['index'])
        value=dict(sort=sort,op=op,args=args,data=data);key=encoded(value)
        if key in self._nodes:return self._nodes[key]
        if len(self.ast)>=self.limits['max_ast_nodes']:raise Limit('AST node cap')
        self.charge(len(key)//64+1)
        if self._dag_bytes+len(key)+1>self.limits['max_receipt_bytes']:raise Limit('incremental DAG byte cap')
        self._dag_bytes+=len(key)+1;index=len(self.ast);self.ast.append(value);self._nodes[key]=index;self._slots.append(frozenset(slots));self._depth.append(depth);return index
    def q(self,value):return self.node('q',data={'value':str(self.rational(value))})
    def add(self,*ids):
        if not ids:return self.q(0)
        out=ids[0]
        for i in ids[1:]:out=self.node('add',[out,i])
        return out
    def mul(self,*ids):
        if not ids:return self.q(1)
        out=ids[0]
        for i in ids[1:]:out=self.node('mul',[out,i])
        return out
    def scale(self,q,expr):return self.node('scale',[expr],{'coefficient':str(self.rational(q))})
    def from_tree(self,tree,binders=(),_depth=0):
        self.charge()
        if _depth>self.limits['max_depth']:raise Limit('named tree depth cap')
        if type(tree)is not list or not tree or type(tree[0])is not str:raise ValueError('typed named list tree')
        op=tree[0]
        child=lambda t:self.from_tree(t,binders,_depth+1)
        if op=='q' and len(tree)==2:return self.q(tree[1])
        if op=='int' and len(tree)==2:return self.node('int',data={'value':tree[1]})
        if op=='v' and len(tree)==2:
            if tree[1] in binders:return self.node('bound',data={'index':tuple(binders).index(tree[1])})
            return self.node('v',data={'name':tree[1]})
        if op=='sum' and len(tree)==5:
            if type(tree[1])is not str or not tree[1]:raise ValueError('named sum binder')
            lo=child(tree[2]);hi=child(tree[3]);body=self.from_tree(tree[4],(tree[1],*binders),_depth+1)
            return self.node('sum',[lo,hi,body],{'binder':tree[1]})
        if op in ('add','mul') and len(tree)>=3:return (self.add if op=='add' else self.mul)(*[child(t) for t in tree[1:]])
        if op=='scale' and len(tree)==3:return self.scale(tree[1],child(tree[2]))
        if op=='symbol' and len(tree)>=2:return self.node('symbol',[child(t) for t in tree[2:]],{'function':tree[1]})
        if op=='scaled_root' and len(tree)==5:return self.node(op,[child(tree[4])],dict(rounding=tree[1],coefficient=tree[2],power=tree[3],negative_extension='zero'))
        if op in ('true','false') and len(tree)==1:return self.node(op)
        arity={'x':1,'embed':1,'ratio':2,'guard':2,'le':2,'lt':2,'eq':2,'divides':2,'coprime':2,'not':1,'and':2,'or':2,'iadd':2,'imul':2,'isub':2,'max':2,'min':2}.get(op)
        if arity is not None and len(tree)==arity+1:return self.node(op,[child(t) for t in tree[1:]])
        raise ValueError('unsupported named-tree spelling '+op)
    def proof_node(self,rule,lhs,rhs,premises=(),scope=0,data=None):
        self.charge()
        if type(scope)is not int or not 0<=scope<=self.limits['max_depth'] or any(self.ast[i]['sort']!='Poly' or any(k>=scope for k in self._slots[i]) for i in (lhs,rhs)):raise ValueError('well-scoped formal polynomial proof')
        if any(type(p)is not int or not 0<=p<len(self.proof) for p in premises):raise ValueError('earlier proof premises')
        value=dict(rule=rule,scope=scope,judgment='FORMAL_EQ',premises=list(premises),lhs=lhs,rhs=rhs,data={} if data is None else dict(data));key=encoded(value)
        if key in self._proofs:return self._proofs[key]
        if len(self.proof)>=self.limits['max_proof_nodes']:raise Limit('proof node cap')
        self.charge(len(key)//64+1)
        if self._dag_bytes+len(key)+1>self.limits['max_receipt_bytes']:raise Limit('incremental DAG byte cap')
        self._dag_bytes+=len(key)+1;index=len(self.proof);self.proof.append(value);self._proofs[key]=index;return index
    def refl(self,i,scope):return self.proof_node('REFL',i,i,scope=scope)
    def trans(self,p,q):
        a=self.proof[p];b=self.proof[q]
        if a['rhs']!=b['lhs'] or a['scope']!=b['scope']:raise ValueError('exact transitive proof endpoints')
        if a['lhs']==a['rhs']:return q
        if b['lhs']==b['rhs']:return p
        return self.proof_node('TRANS',a['lhs'],b['rhs'],[p,q],a['scope'])
    def _ring_cells(self,nf):
        cells=sum(1+len(m) for m in nf);self.peak_ring_cells=max(self.peak_ring_cells,cells)
        if cells>self.limits['max_ring_cells']:raise Limit('local ring cell cap')
        self.charge(cells+1);return nf
    def _nf_add(self,a,b):
        out=dict(a)
        for m,c in b.items():
            self.charge(len(m)+1);q=self.rational(out.get(m,F(0))+c)
            if q:out[m]=q
            else:out.pop(m,None)
            self._ring_cells(out)
        return out
    def _nf_scale(self,q,a):
        out={}
        for m,c in a.items():
            v=self.rational(q*c)
            if v:out[m]=v
        return self._ring_cells(out)
    def _nf_mul(self,a,b,*,boolean=False):
        self.charge(len(a)*len(b)+1);out={}
        for m,c in a.items():
            for n,d in b.items():
                if len(m)+len(n)+1>self.limits['max_ring_cells']:raise Limit('ring factor-cell cap before expansion')
                self.charge(len(m)+len(n)+1);key=tuple(sorted(set(m+n))) if boolean else tuple(sorted(m+n));q=self.rational(out.get(key,F(0))+self.rational(c*d))
                if q:out[key]=q
                else:out.pop(key,None)
                self._ring_cells(out)
        return out
    def ring_nf(self,i,_depth=0):
        self.charge()
        if _depth>self.limits['max_depth']:raise Limit('ring recursion depth')
        node=self.ast[i];op=node['op'];args=node['args']
        if op=='q':
            q=self.rational(node['data']['value']);return {():q} if q else {}
        if op=='add':return self._nf_add(self.ring_nf(args[0],_depth+1),self.ring_nf(args[1],_depth+1))
        if op=='mul':return self._nf_mul(self.ring_nf(args[0],_depth+1),self.ring_nf(args[1],_depth+1))
        if op=='scale':return self._nf_scale(self.rational(node['data']['coefficient']),self.ring_nf(args[0],_depth+1))
        if node['sort']!='Poly':raise ValueError('ring polynomial sort')
        return {(i,):F(1)}
    def bool_nf(self,i,_depth=0):
        self.charge()
        if _depth>self.limits['max_depth']:raise Limit('Boolean recursion depth')
        node=self.ast[i];op=node['op'];args=node['args']
        if op=='true':return {():F(1)}
        if op=='false':return {}
        if op=='lt':return self._nf_add({():F(1)},self._nf_scale(F(-1),{(self.node('le',[args[1],args[0]]),):F(1)}))
        if op=='not':return self._nf_add({():F(1)},self._nf_scale(F(-1),self.bool_nf(args[0],_depth+1)))
        if op in ('and','or'):
            a=self.bool_nf(args[0],_depth+1);b=self.bool_nf(args[1],_depth+1);ab=self._nf_mul(a,b,boolean=True)
            return ab if op=='and' else self._nf_add(self._nf_add(a,b),self._nf_scale(F(-1),ab))
        if node['sort']!='Bool':raise ValueError('Boolean predicate sort')
        return {(i,):F(1)}
    def nf_ast(self,nf,*,boolean=False):
        terms=[]
        for monomial,q in sorted(nf.items()):
            factors=[self.node('guard',[i,self.q(1)]) for i in monomial] if boolean else list(monomial)
            value=self.mul(*factors) if monomial else self.q(q)
            if monomial and q!=1:value=self.scale(q,value)
            terms.append(value)
        return self.add(*terms)
    def normalize(self,i,scope=0):
        self.charge();key=(i,scope)
        if key in self._normalized:return self._normalized[key]
        n=self.ast[i];op=n['op'];args=n['args']
        if n['sort']!='Poly':raise ValueError('polynomial normalization only')
        if op in ('q','x','symbol','embed','ratio'):
            result=(i,self.refl(i,scope));self._normalized[key]=result;return result
        if op=='guard' and args[1]==self.q(1) and self.ast[args[0]]['op']not in ('true','false','not','and','or','lt'):
            result=(i,self.refl(i,scope));self._normalized[key]=result;return result
        newargs=list(args);premises=[]
        poly_positions=[k for k,a in enumerate(args) if self.ast[a]['sort']=='Poly']
        for k in poly_positions:
            target,proof=self.normalize(args[k],scope+1 if op=='sum' and k==2 else scope);newargs[k]=target;premises.append(proof)
        rebuilt=self.node(op,newargs,n['data'])
        p=self.refl(i,scope) if rebuilt==i else self.proof_node('SUM_CONGRUENCE' if op=='sum' else 'CONGRUENCE',i,rebuilt,premises,scope)
        if op=='guard':
            truth=self.nf_ast(self.bool_nf(newargs[0]),boolean=True);expanded=self.mul(truth,newargs[1]);q=self.proof_node('GUARD_BOOL',rebuilt,expanded,scope=scope);p=self.trans(p,q);rebuilt=expanded
        elif op=='sum':
            canonical=self.node('sum',newargs,{'binder':'_'})
            if canonical!=rebuilt:p=self.trans(p,self.proof_node('ALPHA',rebuilt,canonical,scope=scope))
            body_nf=self.ring_nf(newargs[2]);pieces=[]
            for m,q in sorted(body_nf.items()):
                term=self.node('sum',[newargs[0],newargs[1],self.mul(*m)],{'binder':'_'})
                pieces.append(term if q==1 else self.scale(q,term))
            expanded=self.add(*pieces);p=self.trans(p,self.proof_node('SUM_LINEAR',canonical,expanded,scope=scope));rebuilt=expanded
        canonical=self.nf_ast(self.ring_nf(rebuilt));p=self.trans(p,self.proof_node('RING',rebuilt,canonical,scope=scope));result=(canonical,p);self._normalized[key]=result;return result
    def shift(self,i,amount,cutoff=0,_depth=0):
        self.charge()
        if _depth>self.limits['max_depth']:raise Limit('capture-free shift depth')
        n=self.ast[i]
        if n['op']=='bound':
            k=n['data']['index'];j=k+amount if k>=cutoff else k
            if j<0:raise ValueError('capture-free shift would drop a live binder')
            return self.node('bound',data={'index':j})
        args=[self.shift(a,amount,cutoff+1 if n['op']=='sum' and k==2 else cutoff,_depth+1) for k,a in enumerate(n['args'])]
        return self.node(n['op'],args,n['data'])
    def partition(self,sum_id,predicate,scope=0):
        n=self.ast[sum_id]
        if n['op']!='sum' or self.ast[predicate]['sort']!='Bool' or any(i>=scope+1 for i in self._slots[predicate]):raise ValueError('same-domain bound predicate partition')
        lo,hi,body=n['args'];inside=self.node('sum',[lo,hi,self.node('guard',[predicate,body])],n['data']);outside=self.node('sum',[lo,hi,self.node('guard',[self.node('not',[predicate]),body])],n['data']);rhs=self.add(inside,outside)
        return rhs,self.proof_node('PARTITION',sum_id,rhs,scope=scope)
    def range_split(self,sum_id,cut,scope=0):
        if self.ast[cut]['sort']!='Int' or any(i>=scope for i in self._slots[cut]):raise ValueError('range cut outside binder')
        n=self.ast[sum_id]
        if n['op']!='sum':raise ValueError('finite sum range split')
        shifted=self.shift(cut,1);bound=self.node('bound',data={'index':0});predicate=self.node('le',[bound,shifted]);lo,hi,body=n['args']
        head=self.node('sum',[lo,hi,self.node('guard',[predicate,body])],n['data']);tail=self.node('sum',[lo,hi,self.node('guard',[self.node('lt',[shifted,bound]),body])],n['data']);rhs=self.add(head,tail)
        return rhs,self.proof_node('RANGE_SPLIT',sum_id,rhs,scope=scope,data={'cut':cut})
    def pull_factor(self,sum_id,factor,body,scope=0):
        n=self.ast[sum_id]
        if n['op']!='sum' or 0 in self._slots[factor] or n['args'][2]!=self.mul(factor,body):raise ValueError('binder-independent exact sum factor')
        rhs=self.mul(self.shift(factor,-1),self.node('sum',[n['args'][0],n['args'][1],body],n['data']))
        return rhs,self.proof_node('SUM_PULL',sum_id,rhs,scope=scope,data={'factor':factor,'body':body})
    def alpha(self,sum_id,binder,scope=0):
        n=self.ast[sum_id]
        if n['op']!='sum':raise ValueError('alpha requires finite sum')
        rhs=self.node('sum',n['args'],{'binder':binder});return rhs,self.proof_node('ALPHA',sum_id,rhs,scope=scope)
    def _receipt(self,lhs,rhs,conclusion,status,reason=None):
        out=dict(schema=SCHEMA,status=status,complete=status=='proved',judgment='FORMAL_EQ',context=self.context,source_bindings=self.source_bindings,recipe_ids=self.recipe_ids,ast=self.ast,proof=self.proof,lhs=lhs,rhs=rhs,conclusion=conclusion,limits=self.limits,counts=dict(operations=self.operations,ast_nodes=len(self.ast),proof_nodes=len(self.proof),peak_ring_cells=self.peak_ring_cells,receipt_bytes=0))
        if reason is not None:out['reason']=reason
        for _ in range(4):
            size=len(encoded(out))
            if out['counts']['receipt_bytes']==size:break
            out['counts']['receipt_bytes']=size
        if len(encoded(out))>self.limits['max_receipt_bytes']:
            out.update(status='unknown',complete=False,reason='receipt byte cap; DAG suppressed',ast=[],proof=[],lhs=None,rhs=None,conclusion=None)
            out['counts'].update(ast_nodes=0,proof_nodes=0,receipt_bytes=0)
            for _ in range(8):
                size=len(encoded(out))
                if out['counts']['receipt_bytes']==size:break
                out['counts']['receipt_bytes']=size
            if len(encoded(out))>self.limits['max_receipt_bytes']:raise Limit('receipt cap cannot retain bounded UNKNOWN header')
        return out
    def prove(self,lhs,rhs):
        try:
            if any(type(i)is not int or not 0<=i<len(self.ast) or self.ast[i]['sort']!='Poly' or self._slots[i] for i in (lhs,rhs)):raise ValueError('closed formal theorem roots')
            left,p=self.normalize(lhs);right,q=self.normalize(rhs)
            if left!=right:return self._receipt(lhs,rhs,None,'unknown','distinct symbolic normal forms; no unsupported arithmetic equivalence claim')
            reverse=self.proof_node('SYM',right,rhs,[q]);conclusion=self.trans(p,reverse);return self._receipt(lhs,rhs,conclusion,'proved')
        except (Limit,MemoryError) as e:return self._receipt(lhs,rhs,None,'unknown',str(e) or type(e).__name__)
    def certificate(self,lhs,rhs,conclusion):
        node=self.proof[conclusion]
        if node['lhs']!=lhs or node['rhs']!=rhs or node['scope']!=0:raise ValueError('closed complete conclusion')
        return self._receipt(lhs,rhs,conclusion,'proved')


def prove_trees(lhs,rhs,context,*,source_bindings=None,recipe_ids=None,limits=None,deadline=None):
    """Bounded convenience entry; no callbacks or finite evaluation."""
    producer=Producer(context,source_bindings=source_bindings,recipe_ids=recipe_ids,limits=limits,deadline=deadline)
    try:return producer.prove(producer.from_tree(lhs),producer.from_tree(rhs))
    except (Limit,MemoryError) as error:return producer._receipt(None,None,None,'unknown',str(error) or type(error).__name__)
