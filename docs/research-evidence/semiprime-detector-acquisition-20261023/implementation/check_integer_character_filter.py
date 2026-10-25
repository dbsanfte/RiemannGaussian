"""One fixed structured row: tests a proposed character substitution only."""
from math import gcd,isqrt

def jacobi(a,n):
    a %= n
    answer=1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3,5): answer=-answer
        a,n=n,a
        if a % 4 == n % 4 == 3: answer=-answer
        a %= n
    return answer if n == 1 else 0

r,P,Q=43,59447,59747
N,H,M=P*Q,r*r,r**4
prime=lambda n: n>=2 and all(n%j for j in range(2,isqrt(n)+1))
dp,dq=(P-1)//2,(Q-1)//2
assert all(prime(n) for n in (P,Q,dp,dq))
assert min(dp,dq)>16*H and gcd(dp,dq)==1 and dp*dq>256*M
assert pow(4,dp,P)==pow(4,dq,Q)==1 and N<=r**6
P0=32*H
A=isqrt(N)//P0
T=H//(A+1)
a,C,s,c,B=1,331,345,41,1082824
b,d,sigma=586,343984,48
assert P0<=P<=2*P0 and A==1 and 0<C<=T
assert 1<=c<r and 1<=s<H and s%r==1
assert C*N % r == a and (C*N-a*s*s)%H==0
assert B==(H*b-2*a*s) and H*H*d-H*b*s+a*s*s==C*N
assert abs(B)<=M//2 and c*P==s+H*((c*P-s)//H)
h=(c*P-s)//H
assert a*h*h+b*h+d==P*sigma and abs(sigma)<4*r
D0=b*b-4*a*d
assert (2*a*h+b)**2==D0+4*a*P*sigma
actual_discriminant=D0*c*c-2*B*c*sigma+M*sigma*sigma
assert isqrt(actual_discriminant)**2==actual_discriminant
assert jacobi(D0+4*a*sigma,N)==-1
assert jacobi(D0+4*a*sigma,P)==1
print({'N':N,'window_P0':P0,'a':a,'C':C,'s':s,'c':c,'B':B,
       'b':b,'d':d,'sigma':sigma,'D0':D0,
       'true_integer_square':D0+4*a*P*sigma,
       'public_normalized_discriminant':actual_discriminant,
       'jacobi_of_proposed_small_argument':jacobi(D0+4*a*sigma,N)})
