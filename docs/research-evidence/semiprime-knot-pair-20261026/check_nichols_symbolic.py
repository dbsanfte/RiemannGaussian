"""Universal Laurent-polynomial checks of the explicit rank-four operator."""
from itertools import product, permutations
import json

class P(dict):
    def __add__(self, y):
        r=P(self)
        for e,c in poly(y).items():
            r[e]=r.get(e,0)+c
            if not r[e]: del r[e]
        return r
    __radd__=__add__
    def __neg__(self):return P({e:-c for e,c in self.items()})
    def __sub__(self,y):return self+-poly(y)
    def __rsub__(self,y):return poly(y)+-self
    def __mul__(self,y):
        r=P()
        for e,c in self.items():
            for f,d in poly(y).items():
                g=tuple(x+y for x,y in zip(e,f))
                r[g]=r.get(g,0)+c*d
        return P({e:c for e,c in r.items() if c})
    __rmul__=__mul__
    def __pow__(self,n):
        assert n>=0
        r=poly(1)
        for _ in range(n):r=r*self
        return r

def poly(x):return x if isinstance(x,P) else P({(0,0):x}) if x else P()
a,b,ai,bi=(P({e:1}) for e in [(1,0),(0,1),(-1,0),(0,-1)])
A,B=1-a,1-b
E=A+B
R={
 (0,0):{(0,0):1},(0,1):{(0,1):A,(1,0):a},(0,2):{(0,2):B,(2,0):b},
 (0,3):{(0,3):E,(1,2):-A*B,(2,1):-b*A*B,(3,0):a*b},
 (1,0):{(0,1):1},(1,1):{(1,1):-a},(1,2):{(0,3):1,(2,1):-b},
 (1,3):{(1,3):A,(3,1):a*b},(2,0):{(0,2):1},(2,1):{(0,3):bi,(1,2):-bi},
 (2,2):{(2,2):-b},(2,3):{(2,3):B,(3,2):1},(3,0):{(0,3):1},
 (3,1):{(1,3):bi},(3,2):{(2,3):b},(3,3):{(3,3):1}}
Ri={
 (0,0):{(0,0):1},(0,1):{(1,0):1},(0,2):{(2,0):1},(0,3):{(3,0):1},
 (1,0):{(0,1):ai,(1,0):-A*ai},(1,1):{(1,1):-ai},(1,2):{(3,0):1,(2,1):-b},
 (1,3):{(3,1):b},(2,0):{(0,2):bi,(2,0):-B*bi},(2,1):{(3,0):bi,(1,2):-bi},
 (2,2):{(2,2):-bi},(2,3):{(3,2):bi},
 (3,0):{(0,3):ai*bi,(1,2):-A*B*ai*bi,(2,1):-A*B*ai,(3,0):(2*A*B-E)*ai*bi},
 (3,1):{(1,3):ai*bi,(3,1):-A*ai},(3,2):{(2,3):1,(3,2):-B*bi},(3,3):{(3,3):1}}

def act(vec,op,site=0):
    out={}
    for idx,c in vec.items():
        for pair,r in op[idx[site:site+2]].items():
            key=idx[:site]+pair+idx[site+2:]
            out[key]=out.get(key,poly(0))+poly(c)*r
    return {k:v for k,v in out.items() if v}

def word(idx,steps):
    vec={idx:poly(1)}
    for op,site in steps:vec=act(vec,op,site)
    return vec

for idx in product(range(4),repeat=3):
    assert word(idx,[(R,0),(R,1),(R,0)])==word(idx,[(R,1),(R,0),(R,1)]),idx
for idx in product(range(4),repeat=2):
    assert word(idx,[(R,0),(Ri,0)])=={idx:poly(1)}
    assert word(idx,[(Ri,0),(R,0)])=={idx:poly(1)}

def rotate(op):
    out={idx:{} for idx in product(range(4),repeat=2)}
    for (i,j),terms in op.items():
        for (k,l),c in terms.items():out[k,i][l,j]=poly(c)
    return out

def solve_T(y):
    y=lambda ij,y=y:poly(y.get(ij,0))
    x={}
    x[0,0]=y((0,0));x[1,1]=(A*x[0,0]-y((1,1)))*ai;x[2,2]=(B*x[0,0]-y((2,2)))*bi
    x[3,3]=y((3,3))-E*x[0,0]-A*x[1,1]-B*x[2,2]
    x[0,1]=y((1,0));x[1,0]=y((0,1))*ai;x[2,3]=(y((3,2))-y((1,0)))*bi;x[3,2]=y((2,3))+A*B*y((0,1))*ai
    x[0,2]=y((2,0));x[2,0]=y((0,2))*bi;x[1,3]=b*y((3,1))-y((2,0));x[3,1]=(y((1,3))+A*B*y((0,2)))*ai*bi
    x[3,0]=y((0,3))*ai*bi;x[0,3]=y((3,0));x[2,1]=-y((1,2))*bi;x[1,2]=-b*y((2,1))
    return x

def solve_U(y):
    y=lambda ij,y=y:poly(y.get(ij,0))
    x={}
    C=(2*A*B-E)*ai*bi
    x[3,3]=y((3,3));x[1,1]=-a*y((1,1))-A*x[3,3];x[2,2]=-b*y((2,2))-B*x[3,3]
    x[0,0]=y((0,0))+A*x[1,1]*ai+B*x[2,2]*bi-C*x[3,3]
    x[2,3]=y((3,2));x[3,2]=b*y((2,3));x[1,0]=y((0,1))-y((2,3));x[0,1]=a*y((1,0))+A*B*y((3,2))
    x[1,3]=a*b*y((3,1));x[3,1]=y((1,3))*bi;x[2,0]=y((0,2))-y((1,3))*bi;x[0,2]=b*y((2,0))+b*A*B*y((3,1))
    x[3,0]=y((0,3));x[0,3]=a*b*y((3,0));x[2,1]=-y((1,2))*bi;x[1,2]=-b*y((2,1))
    return x
for op,solve in [(rotate(R),solve_T),(rotate(Ri),solve_U)]:
    for idx in product(range(4),repeat=2):assert act(solve({idx:1}),op)=={idx:poly(1)},idx

mu=[1,-1,-1,1]
def trace_second(op,n):
    out={}
    for i,j in product(range(4),repeat=2):
        for (k,l),c in word((i,j),[(op,0)]*n).items():
            if l==j:out[i,k]=out.get((i,k),poly(0))+mu[j]*c
    return {k:v for k,v in out.items() if v}
I={(i,i):poly(1) for i in range(4)}
assert trace_second(R,1)==I
assert trace_second(Ri,1)==I
J=1-(a+b)*(1-a)*(1-b)
assert trace_second(R,3)=={(i,i):J for i in range(4)}
assert J==a*b*((a+ai-1)*(b+bi-1)+1-a*b)
print(json.dumps({'ring':'Z[a^±1,b^±1]','YB_all_64_basis_words':True,'R_inverse_both_orders':True,
 'both_rotated_inverse_solves':True,'both_curl_partial_traces':'identity','trefoil_full_cut_scalar':'1-(a+b)*(1-a)*(1-b)',
 'trefoil_correction':'ab*(Delta(a)*Delta(b)+1-ab)'},indent=2))
