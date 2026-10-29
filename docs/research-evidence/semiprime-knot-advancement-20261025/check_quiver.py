from fractions import Fraction as Q

def mul(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def add(a,b):
    c=[Q(0)]*max(len(a),len(b))
    for i,x in enumerate(a): c[i]+=x
    for i,x in enumerate(b): c[i]+=x
    return c

def scale(a,s): return [x*s for x in a]
def rem(a,g):
    a=a[:]
    while len(a)>=len(g):
        c=a[-1]/g[-1]; d=len(a)-len(g)
        for j,x in enumerate(g): a[d+j]-=c*x
        a.pop()
    return a+[Q(0)]*(len(g)-1-len(a))

for q in [Q(2), Q(3,2), Q(-2)]:
    for M in range(0,13):
        C=[[Q(1)]]; fac=[Q(1)]
        for j in range(1,M+1):
            C.append(mul(C[-1],[-q**j-q**(-j),Q(1)]))
            fac.append(fac[-1]*(1-q**j))
        left=scale(C[M],(-1)**M*q**(M*(M+1)//2)/fac[M]**2)
        s=[Q(0)]
        for i in range(M):
            s=add(s,scale(C[i],(-1)**i*q**(i*(i+3)//2)/fac[i+1]**2))
        right=add([Q(1)],scale(mul([Q(2),Q(-1)],s),q))
        assert left+[Q(0)]*max(0,len(right)-len(left))==right+[Q(0)]*max(0,len(left)-len(right))
        for g in [[Q(1),Q(-2),Q(1)],[Q(3),Q(1),Q(0),Q(1)]]:
            assert rem(left,g)==rem(right,g)
        H=[scale(C[j],(-1)**j*q**(j*(j+1)//2)/fac[j]**2) for j in range(M+1)]
        # Coefficients of L Psi_<M, including its sole upper boundary.
        for n in range(M+1):
            ln=scale(H[n],(1-q**n)**2) if n<M else [Q(0)]
            if n>0:
                ln=add(ln,scale(mul([Q(1)+q**(2*n),-q**n],H[n-1]),-1))
            expected=scale(H[M],-(1-q**M)**2) if n==M else [Q(0)]
            assert rem(ln,[Q(3),Q(1),Q(0),Q(1)])==rem(expected,[Q(3),Q(1),Q(0),Q(1)])
        for m in range(-2,3):
            D=lambda n: sum_polys([scale(C[j],q**(n*j)) for j in range(M)])
            def sum_polys(items):
                out=[Q(0)]
                for a in items: out=add(out,a)
                return out
            lhs=add(scale(D(m+1),q**(m+1)),mul([Q(1)-0,-q**m],D(m)))
            # middle term is (1-Z*q^m)D_m.
            lhs=add(lhs,scale(D(m-1),q**(m-1)))
            rhs=add([Q(1)],scale(C[M],-q**(m*M)))
            # Arrays may retain trailing zero coefficients.
            assert rem(lhs,[Q(3),Q(1),Q(0),Q(1)])==rem(rhs,[Q(3),Q(1),Q(0),Q(1)])
        for u in [Q(3),Q(5,2)]:
            Z=u+1/u
            cv=Q(1); p1=Q(1); p2=Q(1); bs=Q(1); uj=Q(1); fj=Q(1)
            for j in range(1,M+1):
                cv*=Z-q**j-q**(-j)
                p1*=1-u*q**j; p2*=1-q**j/u
                uj*=(1-u*q**(j-1))*(1-q**(j-1)/u)
                fj*=1-q**j
                bs+=q**j*uj/fj**2
            assert cv==(-1)**M*q**(-M*(M+1)//2)*p1*p2
            assert bs==p1*p2/fac[M]**2
            for d in [1,2,4]:
                if M%d: continue
                split=Q(1)
                for s in range(1,d+1):
                    for r in range(M//d):
                        v=q**(s+d*r)
                        split*=(1-u*v)*(1-v/u)/(1-v)**2
                assert split==p1*p2/fac[M]**2
            cmneg=Q(1); cmsquare=Q(1)
            for r in range(1,M+1):
                cmneg*= -Z-q**r-q**(-r)
                cmsquare*= Z**2-2-q**(2*r)-q**(-2*r)
            assert cv*cmneg==(-1)**M*cmsquare
print('Exact checks passed: A, B, C, quotient reductions, descendant boundaries, normalized q-difference boundary, decimation, trace norm; M=0..12, three rational q values.')
