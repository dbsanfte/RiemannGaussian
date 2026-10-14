"""Independent bounded exact arithmetic for structural potential candidates.

The interpreter implements its own syntax/type checks and obtains Möbius
values by trial factorization. It imports no producer or hash machinery.
Finite checked cases do not establish a uniform signed innovation estimate.
"""
from fractions import Fraction as F
from math import gcd, isfinite, isqrt
import time


def require(condition,message):
    if not condition:raise ValueError(message)


class Meter:
    def __init__(self,max_operations,*,deadline=None,max_cells=6000000,max_bits=4096):
        require(type(max_operations)is int and 0<max_operations<=450000000,'bounded shared exact work')
        require(type(max_cells)is int and 0<max_cells<=6000000 and type(max_bits)is int and 0<max_bits<=4096,'bounded cells and bits')
        deadline=time.monotonic()+3600 if deadline is None else deadline
        require(type(deadline)in(int,float)and isfinite(deadline),'finite exact deadline')
        self.max_operations=max_operations;self.deadline=deadline;self.max_cells=max_cells;self.max_bits=max_bits
        self.operations=0;self.peak_live_cells=0;self.maximum_rational_bits=0

    def charge(self,n=1):
        require(type(n)is int and n>=0,'nonnegative work charge')
        if n>self.max_operations-self.operations:raise OverflowError('shared independent work cap')
        self.operations+=n
        if time.monotonic()>self.deadline:raise TimeoutError('independent exact deadline')

    def live(self,cells):
        self.charge();require(type(cells)is int and cells>=0,'nonnegative live cells')
        self.peak_live_cells=max(self.peak_live_cells,cells)
        if cells>self.max_cells:raise OverflowError('independent live-cell cap')

    def number(self,value):
        self.charge();require(type(value)in(int,F),'exact scalar or strict integer')
        bits=max(abs(value.numerator).bit_length(),value.denominator.bit_length())
        self.maximum_rational_bits=max(self.maximum_rational_bits,bits)
        if bits>self.max_bits:raise OverflowError('independent exact coefficient/index bits')
        return value

    def counts(self):
        return dict(operations=self.operations,peak_live_cells=self.peak_live_cells,maximum_rational_bits=self.maximum_rational_bits)


def _rational(text,meter):
    meter.charge();require(type(text)is str,'canonical rational string')
    if len(text)>2*meter.max_bits+3:raise OverflowError('rational text preflight')
    require(text and all(c in '-0123456789/'for c in text),'canonical rational syntax')
    parts=text.split('/');require(len(parts)<=2 and all(p and p!='-'for p in parts),'rational integer components')
    digits=1+meter.max_bits*30103//100000
    if any(len(p.lstrip('-'))>digits for p in parts):raise OverflowError('rational integer allocation preflight')
    integers=[int(p)for p in parts]
    require(len(integers)==1 or integers[1]>0,'positive denominator')
    for value in integers:meter.number(value)
    value=meter.number(F(*integers));require(str(value)==text,'canonical exact rational');return value


class _Node:
    __slots__=('op','args','dependencies','key','kind')
    def __init__(self,op,args,kind):
        self.op=op;self.args=args;self.kind=kind
        children=[a for a in args if type(a)is _Node]
        dependencies=set().union(*(a.dependencies for a in children))if children else set()
        if op=='v':dependencies.add(args[0])
        if op=='sum':dependencies.discard(args[0])
        self.dependencies=tuple(sorted(dependencies))
        self.key=(op,*(a.key if type(a)is _Node else a for a in args))


def _validate(candidate,meter):
    require(type(candidate)is dict and set(candidate)=={'states'}and type(candidate['states'])is list
        and len(candidate['states'])<=2,'zero to two explicit potential states')
    nodes=0
    index_binary={'iadd','isub','imul','idiv','imod','gcd','min','max'}
    compare={'eq','le','lt','divides'}
    signatures={**{op:('index',('index','index'))for op in index_binary},
        **{op:('bool',('index','index'))for op in compare},
        'prime':('bool',('index',)),'squarefree':('bool',('index',)),
        'and':('bool',('bool','bool')),'or':('bool',('bool','bool')),'not':('bool',('bool',)),
        'x':('scalar',('index',)),'embed':('scalar',('index',)),'ratio':('scalar',('index','index')),
        'add':('scalar',('scalar','scalar')),'mul':('scalar',('scalar','scalar')),'guard':('scalar',('bool','scalar'))}
    def visit(tree,scope,depth=0):
        nonlocal nodes
        meter.charge();nodes+=1
        if nodes>256 or depth>24:raise OverflowError('complete candidate syntax cap')
        require(type(tree)is list and tree and type(tree[0])is str,'explicit AST node')
        op=tree[0]
        if op=='int':
            require(len(tree)==2 and type(tree[1])is int,'strict literal index');meter.number(tree[1]);return _Node(op,(tree[1],),'index')
        if op=='v':
            require(len(tree)==2 and type(tree[1])is str and tree[1]in scope,'lexically bound index variable');return _Node(op,(tree[1],),'index')
        if op=='q':
            require(len(tree)==2,'rational scalar arity');return _Node(op,(_rational(tree[1],meter),),'scalar')
        if op=='root':
            require(len(tree)==4 and type(tree[2])is int and tree[2]>=0 and type(tree[3])is int and tree[3]>=1,'exact fractional-root parameters')
            meter.number(tree[2]);meter.number(tree[3]);child=visit(tree[1],scope,depth+1)
            require(child.kind=='index','root index input');return _Node(op,(child,tree[2],tree[3]),'index')
        if op=='scale':
            require(len(tree)==3,'scalar scaling arity');coefficient=_rational(tree[1],meter);child=visit(tree[2],scope,depth+1)
            require(child.kind=='scalar','scalar scaling input');return _Node(op,(coefficient,child),'scalar')
        if op=='sum':
            require(len(tree)==5 and type(tree[1])is str and tree[1].isidentifier()and tree[1]not in scope and tree[1]!='N','fresh lexical sum binder excluding reserved N')
            lo=visit(tree[2],scope,depth+1);hi=visit(tree[3],scope,depth+1);body=visit(tree[4],scope|{tree[1]},depth+1)
            require(lo.kind==hi.kind=='index'and body.kind=='scalar','inclusive scalar summation types')
            return _Node(op,(tree[1],lo,hi,body),'scalar')
        require(op in signatures,'supported exact AST production');kind,wants=signatures[op]
        require(len(tree)==len(wants)+1,'exact AST arity');children=tuple(visit(child,scope,depth+1)for child in tree[1:])
        require(all(child.kind==want for child,want in zip(children,wants)),'exact AST type checking')
        return _Node(op,children,kind)
    states=[]
    for state in candidate['states']:
        require(type(state)is dict and set(state)=={'weight','tree'},'explicit squared state and weight')
        weight=_rational(state['weight'],meter);require(weight>=0,'nonnegative potential weight')
        node=visit(state['tree'],{'X','t'});require(node.kind=='scalar','scalar state expression');states.append((weight,node))
    return nodes,states


def validate_candidate(candidate,meter):
    return _validate(candidate,meter)[0]


class Checker:
    def __init__(self,horizon,meter,*,source='mu'):
        require(type(horizon)is int and horizon>=1,'positive complete source horizon');meter.number(horizon)
        require(source in('mu','one','partial_prime_2'),'declared actual or diagnostic control source')
        self.horizon=horizon;self.meter=meter;self.source=source
        self._base_cells=8*(horizon+1);meter.live(self._base_cells)
        self._factor_cache={};self._memo={};self._prefix={};self._candidates={};self._memo_cells=0;self._prefix_cells=0;self._syntax_cells=0
        mu=[0]+[self._mobius(n)for n in range(1,horizon+1)]
        if source=='mu':self.values=mu
        elif source=='one':
            meter.charge(horizon);self.values=[0]+[1]*horizon
        else:
            meter.charge(3*horizon);self.values=[0]+[q*q*(-1 if n%2==0 else 1)for n,q in enumerate(mu[1:],1)]
        self._squares=[F(0)];summatory=0
        for value in self.values[1:]:
            summatory=meter.number(summatory+value)
            square=meter.number(summatory*summatory)
            self._squares.append(meter.number(self._squares[-1]+square))
        self._live()

    def _live(self,extra=0):
        self.meter.live(self._base_cells+self._memo_cells+self._prefix_cells+self._syntax_cells+2*len(self._factor_cache)+extra)

    def _mobius(self,n):
        if n<1:return 0
        if n in self._factor_cache:self.meter.charge();return self._factor_cache[n]
        remaining=n;sign=1;divisor=2
        while divisor*divisor<=remaining:
            self.meter.charge(4)
            if remaining%divisor==0:
                remaining//=divisor;sign=-sign
                self.meter.charge(2)
                if remaining%divisor==0:sign=0;break
            divisor=3 if divisor==2 else divisor+2
        if sign and remaining>1:sign=-sign;self.meter.charge()
        self._factor_cache[n]=sign;return sign

    def _prime(self,n):
        if n<2:return False
        for d in range(2,isqrt(n)+1):
            self.meter.charge(2)
            if n%d==0:return False
        return True

    def _root(self,n,a,b):
        require(n>=0,'nonnegative exact fractional-power base')
        common=gcd(a,b);a//=common;b//=common
        if a==0:return 1
        if n in(0,1):return n
        bits=max(a*n.bit_length(),b*n.bit_length())
        if bits>self.meter.max_bits:raise OverflowError('fractional-power temporary integer bits')
        self.meter.charge(bits);target=n**a;lo=0;hi=1<<((target.bit_length()+b-1)//b)
        while lo+1<hi:
            self.meter.charge(b*max(1,hi.bit_length()));mid=(lo+hi)//2
            if mid**b<=target:lo=mid
            else:hi=mid
        return self.meter.number(lo)

    def _run(self,node,env):
        self.meter.charge();key=(node.key,tuple((name,env[name])for name in node.dependencies))
        if key in self._memo:return self._memo[key]
        op=node.op;args=node.args
        if op in('int','q'):value=args[0]
        elif op=='v':value=env[args[0]]
        elif op=='x':
            index=self._run(args[0],env);require(1<=index<=self.horizon,'source index outside declared horizon');value=F(self.values[index])
        elif op=='embed':value=F(self._run(args[0],env))
        elif op=='guard':value=self._run(args[1],env)if self._run(args[0],env)else F(0)
        elif op=='and':value=self._run(args[0],env)and self._run(args[1],env)
        elif op=='or':value=self._run(args[0],env)or self._run(args[1],env)
        elif op=='not':value=not self._run(args[0],env)
        elif op=='prime':value=self._prime(self._run(args[0],env))
        elif op=='squarefree':value=self._mobius(self._run(args[0],env))!=0
        elif op=='root':value=self._root(self._run(args[0],env),args[1],args[2])
        elif op=='scale':value=self.meter.number(args[0]*self._run(args[1],env))
        elif op=='sum':
            name,lower,upper,body=args;lo=self._run(lower,env);hi=self._run(upper,env)
            if lo>hi:value=F(0)
            else:
                # Endpoints select a prefix. Only summand dependencies remain
                # in its family key; whole-expression memo above includes all
                # endpoint variables as well. Never extend beyond requested hi.
                dependencies=tuple((var,env[var])for var in body.dependencies if var!=name)
                prefix_key=(node.key,lo,dependencies)
                if prefix_key not in self._prefix:
                    self._live(2);self._prefix[prefix_key]=[F(0)];self._prefix_cells+=2+2*len(dependencies)
                prefix=self._prefix[prefix_key];needed=hi-lo+1
                self.meter.charge(max(0,needed+1-len(prefix)))
                while len(prefix)<=needed:
                    index=lo+len(prefix)-1;inner=dict(env);inner[name]=index
                    term=self._run(body,inner);total=self.meter.number(prefix[-1]+term)
                    self._live(1);prefix.append(total);self._prefix_cells+=1
                value=prefix[needed]
        else:
            left=self._run(args[0],env);right=self._run(args[1],env)
            if op=='ratio':require(right!=0,'nonzero exact rational denominator');value=F(left,right)
            elif op=='add':value=left+right
            elif op=='mul':value=left*right
            elif op=='eq':value=left==right
            elif op=='le':value=left<=right
            elif op=='lt':value=left<right
            elif op=='divides':value=left!=0 and right%left==0
            else:
                if op in('idiv','imod'):require(right!=0,'nonzero exact index divisor')
                if op=='iadd':value=left+right
                elif op=='isub':value=left-right
                elif op=='imul':
                    if left and right and abs(left).bit_length()+abs(right).bit_length()>self.meter.max_bits+1:
                        raise OverflowError('index product bit preflight')
                    value=left*right
                elif op=='idiv':value=left//right
                elif op=='imod':value=left%right
                elif op=='gcd':value=gcd(left,right)
                elif op=='min':value=min(left,right)
                elif op=='max':value=max(left,right)
                else:raise ValueError('unsupported exact scalar production')
        if type(value)is not bool:value=self.meter.number(value)
        self._live(2*len(node.dependencies)+2)
        self._memo[key]=value;self._memo_cells+=2*len(node.dependencies)+2
        return value

    def _prepare(self,candidate):
        nodes,states=_validate(candidate,self.meter);key=tuple((weight,node.key)for weight,node in states)
        self._live(8*nodes+8)
        if key not in self._candidates:
            self._candidates[key]=states;self._syntax_cells+=8*nodes+8
        return self._candidates[key]

    def measure(self,candidate,X):
        require(type(X)is int and X>=1 and 2*X-1<=self.horizon,'complete measure scale within source horizon')
        self.meter.number(X);states=self._prepare(candidate)
        energy=self.meter.number((self._squares[2*X-1]-self._squares[X-1])/F(X*X));potential=F(0)
        for t in range(X,2*X):
            self.meter.charge()
            for weight,node in states:
                value=self._run(node,{'X':X,'t':t})
                contribution=self.meter.number(weight*self.meter.number(value*value))
                potential=self.meter.number(potential+contribution)
        potential=self.meter.number(potential/F(X*X));whole=self.meter.number(energy+potential)
        return dict(X=X,E=str(energy),V=str(potential),W=str(whole))

    def case(self,candidate,X):
        require(type(X)is int and X>=1 and 4*X-1<=self.horizon,'complete parent and child scale horizon')
        parent=self.measure(candidate,X);child=self.measure(candidate,2*X)
        innovation=self.meter.number(F(child['W'])-F(parent['W']))
        return dict(X=X,parent=parent,child=child,innovation=str(innovation))

    def _measure_record(self,record):
        require(type(record)is dict and set(record)=={'X','E','V','W'}and type(record['X'])is int,'full exact measure record')
        for key in('E','V','W'):_rational(record[key],self.meter)

    def verify_measure(self,candidate,record):
        self._measure_record(record);computed=self.measure(candidate,record['X'])
        require(record==computed,'independent full E, potential and anchored W equality');return computed

    def verify_case(self,candidate,record):
        require(type(record)is dict and set(record)=={'X','parent','child','innovation'}and type(record['X'])is int,'full signed innovation record')
        self._measure_record(record['parent']);self._measure_record(record['child']);_rational(record['innovation'],self.meter)
        computed=self.case(candidate,record['X']);require(record==computed,'independent complete parent, child and signed innovation equality');return computed
