#!/usr/bin/env python3
"""Exact orientation/initialization checks for the companion-Bezout transfer."""
from pathlib import Path
from random import Random
rng=Random(20261026)
N,q=101*103,2
qi=pow(q,-1,N)
def mm(A,B):
    return [[sum(a*b for a,b in zip(row,col))%N for col in zip(*B)] for row in A]
def tr(A): return list(map(list,zip(*A)))
def det(A):
    # Fraction-free exact integer Bareiss; here only the integer H is used.
    A=[r[:] for r in A]; n=len(A); sign=1; prev=1
    for k in range(n-1):
        if A[k][k]==0:
            j=next(j for j in range(k+1,n) if A[j][k])
            A[k],A[j]=A[j],A[k]; sign=-sign
        pivot=A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n): A[i][j]=(A[i][j]*pivot-A[i][k]*A[k][j])//prev
        for i in range(k+1,n): A[i][k]=0
        prev=pivot
    return sign*A[-1][-1]
checks=0
for L in range(1,8):
    for sample in range(10):
        g=[rng.randrange(N) for _ in range(L)]+[1]
        H=[[g[i+j+1] if i+j+1<=L else 0 for j in range(L)] for i in range(L)]
        assert det(H)==(-1)**(L*(L-1)//2)
        C=[[0]*L for _ in range(L)]
        for i in range(1,L): C[i][i-1]=1
        for i in range(L): C[i][-1]=(-g[i])%N
        assert mm(C,H)==mm(H,tr(C))
        B=H; R=[1]+[0]*(L-1)
        for n in range(10):
            assert [row[-1]%N for row in B]==R
            assert B==tr(B) if n else True
            a=(pow(qi,n+1,N)+pow(q,n+2,N))%N
            A=[[ (C[i][j]-(a if i==j else 0))%N for j in range(L)] for i in range(L)]
            B=mm(A,B)
            top=R[-1]
            R=[((R[i-1] if i else 0)-a*R[i]-top*g[i])%N for i in range(L)]
            checks+=1
result=f'PASS {checks} exact companion/Bezout remainder-column steps over N={N}; 70 unimodular Hankel determinants and adjoint identities\n'
Path(__file__).with_name('boundary-validation.txt').write_text(result)
print(result,end='')
