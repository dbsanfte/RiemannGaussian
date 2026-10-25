import itertools
import unittest
from math import gcd
from sheared_norm import (norm_tangent,evaluate_sparse,trace_prefix,sparse_product,
                         rational_moments,inverse_moments,NonunitError)

P,Q=1009,1013
N=P*Q

def primitive(p):
    factors=[];v=p-1;k=2
    while k*k<=v:
        if v%k==0:
            factors.append(k)
            while v%k==0:v//=k
        k+=1
    if v>1:factors.append(v)
    return next(a for a in range(2,p) if all(pow(a,(p-1)//r,p)!=1 for r in factors))
ETA=(primitive(P)+P*((primitive(Q)-primitive(P))*pow(P,-1,Q)%Q))%N

def mat_poly(poly,p,y,n):
    """Independent multiplication matrix, Laurent exponents via X^p=y."""
    out=[[0]*p for _ in range(p)]
    for col in range(p):
        for exponent,c in poly.items():
            quotient,row=divmod(exponent+col,p)
            out[row][col]=(out[row][col]+c*pow(y,quotient,n))%n
    return out

def determinant_dual(a,b,n):
    """Independent Leibniz determinant over n[eps]/eps² (no pivots/inverses)."""
    p=len(a);real=tangent=0
    for perm in itertools.permutations(range(p)):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(p) for j in range(i+1,p))
        r,t=1,0
        for i,j in enumerate(perm):r,t=r*a[i][j]%n,(t*a[i][j]+r*b[i][j])%n
        real=(real+sign*r)%n;tangent=(tangent+sign*t)%n
    return real,tangent

def mat_mul(a,b,n):
    return [[sum(x*y for x,y in zip(row,col))%n for col in zip(*b)] for row in a]

def matrix_inverse(a,n):
    p=len(a);w=[row[:]+[int(i==j) for j in range(p)] for i,row in enumerate(a)]
    for j in range(p):
        k=next(k for k in range(j,p) if gcd(w[k][j],n)==1)
        w[j],w[k]=w[k],w[j]
        v=pow(w[j][j],-1,n);w[j]=[x*v%n for x in w[j]]
        for i in range(p):
            if i!=j:
                v=w[i][j];w[i]=[(x-v*y)%n for x,y in zip(w[i],w[j])]
    return [row[p:] for row in w]

def determinant_coefficient_oracle(m,s,gamma,t,u,y,n):
    """Leibniz determinant with independent z-polynomial dual arithmetic."""
    a0=mat_poly({0:gamma*gamma,1:2*gamma,2:1},m,y,n)
    a1=mat_poly({s+i:-t*t*c for i,c in enumerate((1,2*gamma,gamma*gamma))},m,y,n)
    tangent=mat_poly(dict(enumerate(u)),m,y,n)
    def pmul(a,b):
        out=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,v in enumerate(b):out[i+j]=(out[i+j]+x*v)%n
        return out
    def padd(a,b):
        out=[0]*max(len(a),len(b))
        for i,x in enumerate(a):out[i]=(out[i]+x)%n
        for i,x in enumerate(b):out[i]=(out[i]+x)%n
        return out
    real=[0]*(m+1);derivative=[0]*(m+1)
    for perm in itertools.permutations(range(m)):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(m) for j in range(i+1,m))
        r,v=[1],[0]
        for i,j in enumerate(perm):
            f=[a0[i][j],a1[i][j]]
            r,v=pmul(r,f),padd(pmul(v,f),pmul(r,[tangent[i][j]]))
        for j,c in enumerate(r):real[j]=(real[j]+sign*c)%n
        for j,c in enumerate(v):derivative[j]=(derivative[j]+sign*c)%n
    return real,derivative

class TestSheared(unittest.TestCase):
    def test_actual_moments_and_inverse(self):
        nodes=[pow(ETA,e,N) for e in (0,1,7,13)]
        coeff=[4,0,19,N-2]
        values=rational_moments(coeff,nodes,len(nodes),N)
        self.assertEqual(values,[sum(c*pow(x,i,N) for c,x in zip(coeff,nodes))%N
                                 for i in range(len(nodes))])
        self.assertEqual(inverse_moments(values,nodes,N),coeff)
        a={(0,0):3,(1,1):5};b={(0,0):7,(1,0):2}
        support=[(j,e) for j in range(3) for e in range(3)]
        result=sparse_product(a,b,support,ETA,N)
        expected={}
        for (j,e),c in a.items():
            for (k,f),d in b.items():expected[j+k,e+f]=(expected.get((j+k,e+f),0)+c*d)%N
        self.assertEqual(result,expected)

    def test_independent_determinants_negative_large_shifts(self):
        gamma,t=4,2
        for m,s in ((1,-7),(2,-17),(2,19),(4,-17),(4,-1),(4,0),(4,1),(4,31)):
            # Degree exactly 2m exercises the wide tangent support.
            u=[(j*j+3*j+1)%N for j in range(2*m+1)]
            norm,tangent,ledger=norm_tangent(m,s,gamma,t,u,N,ETA)
            for z,y in ((0,2),(3,2),(5,3)):
                f={0:gamma*gamma,1:2*gamma,2:1}
                for e,c in enumerate((1,2*gamma,gamma*gamma)):
                    f[s+e]=(f.get(s+e,0)-z*t*t*c)%N
                mat=mat_poly(f,m,y,N)
                du=mat_poly(dict(enumerate(u)),m,y,N)
                a,b=determinant_dual(mat,du,N)
                self.assertEqual(evaluate_sparse(norm,z,y,N),a,(m,s,z,y))
                self.assertEqual(evaluate_sparse(tangent,z,y,N),b,(m,s,z,y))
            self.assertTrue(all(step['span']<16*m*m for step in ledger))
            self.assertEqual([x['p'] for x in ledger],[1<<j for j in range(m.bit_length()-1)])

    def test_trace_prefix_independent_matrix_oracle(self):
        m,s,gamma,t=4,-3,4,2
        b=[2,3,4,5];g=[gamma*gamma,2*gamma,1]
        u=[0]*(len(b)+len(g)-1)
        for i,x in enumerate(b):
            for j,y in enumerate(g):u[i+j]+=x*y
        q,v,_=norm_tangent(m,s,gamma,t,u,N,ETA)
        got=trace_prefix(q,v,m,N)
        gm=mat_poly(dict(enumerate(g)),m,1,N)
        fm=mat_poly({s+i:t*t*c for i,c in enumerate((1,2*gamma,gamma*gamma))},m,1,N)
        base=mat_mul(matrix_inverse(gm,N),fm,N)
        bm=mat_poly(dict(enumerate(b)),m,1,N)
        expected=[]
        for _ in range(m):
            expected.append(sum(bm[i][i] for i in range(m))%N)
            bm=mat_mul(bm,base,N)
        self.assertEqual(got,expected)

    def test_precision_independent_coefficient_oracle(self):
        m,s,gamma,t=4,-17,4,2
        u=[j*j+2*j+3 for j in range(2*m+1)]
        for y in (2,3):
            expected_q,expected_v=determinant_coefficient_oracle(m,s,gamma,t,u,y,N)
            for h in (1,2,3,5):
                q,v,ledger=norm_tangent(m,s,gamma,t,u,N,ETA,precision=h)
                def coefficients(f):
                    out=[0]*h
                    for (j,e),c in f.items():
                        self.assertLess(j,h)
                        out[j]=(out[j]+c*pow(y,e,N))%N
                    return out
                self.assertEqual(coefficients(q),expected_q[:h])
                self.assertEqual(coefficients(v),expected_v[:h])
                for step in ledger:
                    self.assertEqual(step['q'],min(step['p'],h-1))
                    self.assertEqual(step['radix'],2*step['q']+1)
                    self.assertLess(step['span'],16*m*m)
        # Explicit high-term aliasing countercontrol: reconstructing from a
        # support with the z^2 term discarded corrupts the LOW coefficients.
        a={(0,0):1,(1,0):1}
        bad=sparse_product(a,a,[(0,0),(1,0)],ETA,N)
        self.assertNotEqual(bad,{(0,0):1,(1,0):2})
        full=sparse_product(a,a,[(0,0),(1,0),(2,0)],ETA,N)
        self.assertEqual({key:c for key,c in full.items() if key[0]<2},
                         {(0,0):1,(1,0):2})
        for h in (0,-1,True,1.5):
            with self.assertRaises(ValueError):
                norm_tangent(m,s,gamma,t,u,N,ETA,precision=h)

    def test_guards_zero_and_invalid(self):
        with self.assertRaises(ValueError):
            sparse_product({(0,0):1},{},[],ETA,N)
        with self.assertRaises(NonunitError) as exc:
            sparse_product({(0,0):1},{(0,0):1},[(0,0),(0,4)],2,35)
        self.assertEqual(exc.exception.divisor,5)
        with self.assertRaises(NonunitError) as exc:
            sparse_product({(0,0):1},{(0,0):1},[(0,0),(0,1)],1,35)
        self.assertEqual(exc.exception.divisor,35)
        q,v,_=norm_tangent(2,-1,4,2,[],N,ETA)
        self.assertEqual(v,{})
        for m,n,u in ((3,N,[]),(2,10,[]),(2,N,[1]*6)):
            with self.assertRaises(ValueError):norm_tangent(m,1,4,2,u,n,ETA)

if __name__=='__main__':unittest.main()
