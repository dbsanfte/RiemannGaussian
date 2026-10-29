"""Exact polynomial checks for the displayed formal operator, not a coverage experiment."""
from itertools import product, permutations
import json

class Poly(dict):
    def __add__(self, other):
        other = cast(other)
        result = Poly(self)
        for e, c in other.items():
            result[e] = result.get(e, 0) + c
            if not result[e]: del result[e]
        return result
    __radd__ = __add__
    def __neg__(self): return Poly({e: -c for e, c in self.items()})
    def __sub__(self, other): return self + -cast(other)
    def __rsub__(self, other): return cast(other) + -self
    def __mul__(self, other):
        result = Poly()
        for e, c in self.items():
            for f, d in cast(other).items():
                g = tuple(x+y for x,y in zip(e,f))
                result[g] = result.get(g, 0) + c*d
        return Poly({e:c for e,c in result.items() if c})
    __rmul__ = __mul__
    def __pow__(self, n):
        assert n >= 0
        r = cast(1)
        for _ in range(n): r = r*self
        return r
    def restrict(self, kind):
        result=Poly()
        for (i,j,k),c in self.items():
            e = (0,j,k) if kind == 'p=1' else (i,j+k,0)
            result = result + Poly({e:c})
        return result

def cast(x): return x if isinstance(x,Poly) else Poly({(0,0,0):x}) if x else Poly()
p,a,b = (Poly({e:1}) for e in [(1,0,0),(0,1,0),(0,0,1)])
R={
 (0,0):{(0,0):1}, (0,1):{(0,1):1-a,(1,0):a}, (0,2):{(0,2):1-b,(2,0):b},
 (0,3):{(0,3):(1-a)*(1-p*b),(1,2):a*(1-b),(2,1):-p*b*(1-a),(3,0):a*b},
 (1,0):{(0,1):1}, (1,1):{(1,1):-a}, (1,2):{(0,3):1-p*b,(2,1):-p*b},
 (1,3):{(1,3):-a*(1-p*b),(3,1):p*a*b},
 (2,0):{(0,2):1}, (2,1):{(0,3):a-1+(p-1)*b,(1,2):-a,(2,1):(p-1)*b},
 (2,2):{(2,2):-b}, (2,3):{(2,3):-b*(1-p*a),(3,2):a*b},
 (3,0):{(0,3):1}, (3,1):{(1,3):a}, (3,2):{(2,3):p*b}, (3,3):{(3,3):p*a*b}}

def act(vec, site):
    out={}
    for idx,c in vec.items():
        for pair,r in R[idx[site:site+2]].items():
            key=idx[:site]+pair+idx[site+2:]
            out[key]=out.get(key,cast(0))+c*r
    return out

def braid(idx,word):
    vec={idx:cast(1)}
    for site in word: vec=act(vec,site)
    return vec

for idx in product(range(4),repeat=3):
    x,y=braid(idx,[0,1,0]),braid(idx,[1,0,1])
    for key in x.keys()|y.keys():
        d=x.get(key,cast(0))-y.get(key,cast(0))
        assert not d.restrict('p=1'),(idx,key,'p=1')
        assert not d.restrict('a=b'),(idx,key,'a=b')
        if idx==(0,1,2) and key==(0,0,3):
            assert d==p*b**2*(p-1)*(a-b)

colors=[(0,0),(1,0),(0,1),(1,1)]
blocks={}
for i,j in product(range(4),repeat=2):
    grade=tuple(x+y for x,y in zip(colors[i],colors[j]))
    blocks.setdefault(grade,[]).append((i,j))
    assert all(tuple(x+y for x,y in zip(colors[u],colors[v]))==grade for u,v in R[i,j])
determinant=cast(1)
for basis in blocks.values():
    d=cast(0)
    for perm in permutations(range(len(basis))):
        inversions=sum(perm[i]>perm[j] for i in range(len(perm)) for j in range(i+1,len(perm)))
        term=cast((-1)**inversions)
        for col,row in enumerate(perm): term=term*R[basis[col]].get(basis[row],0)
        d=d+term
    determinant=determinant*d
assert determinant==p**4*(a*b)**8
print(json.dumps({'method':'exact identities in Z[p,a,b]; no numerical parameter instances',
                  'all_64_input_basis_words_checked':True,'p=1_YB':True,'a=b_YB':True,
                  'target_YB_defect':'p*b^2*(p-1)*(a-b)','determinant':'p^4*(a*b)^8'},indent=2))
