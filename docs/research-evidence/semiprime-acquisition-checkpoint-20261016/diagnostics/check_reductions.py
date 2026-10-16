from math import gcd


def simple_roots(N, a, t, r, k):
    roots = [x for x in range(r) if (a*x*x-t*x+N) % r == 0
             and (2*a*x-t) % r]
    modulus = r
    for _ in range(1, k):
        next_roots = []
        for x in roots:
            c = (a*x*x-t*x+N) // modulus
            correction = (-c * pow(2*a*x-t, -1, r)) % r
            y = x + modulus*correction
            assert (a*y*y-t*y+N) % (modulus*r) == 0
            next_roots.append(y)
        roots = next_roots
        modulus *= r
    return set(roots)


def square_catalog(N, t, r):
    n = r*r
    D = (t*t-4*N) % n
    if D % r == 0:
        if D:
            return set()
        ys = [r*j for j in range(r)]
    else:
        ys=[]
        for y in range(r):
            if (y*y-D)%r == 0:
                correction = ((D-y*y)//r * pow(2*y,-1,r)) % r
                ys.append(y+r*correction)
    inv2=pow(2,-1,n)
    return {((y+t)*inv2)%n for y in ys}


square_cases=linear_cases=0
for r in [3,5,7,11]:
    n=r*r
    for N in range(1,n):
        if gcd(N,r)>1: continue
        singular=0
        for t in range(n):
            got=square_catalog(N,t,r)
            want={x for x in range(n) if (x*x-t*x+N)%n==0}
            assert got==want,(r,N,t,got,want)
            assert len(got)<=r
            if (t*t-4*N)%n==0: singular+=1
            elif len(got)>2: raise AssertionError((r,N,t))
            square_cases+=1
        assert singular<=2
    for k in [1,2,3]:
        n=r**k
        # Full unit-pair check at small r; sampled all residue classes at larger r.
        units=[x for x in range(n) if x%r]
        if len(units)>150:
            units=units[:75]+units[-75:]
        for P in units:
            for Q in units:
                N=(P*Q)%n
                S=set()
                for a in [1,2]:
                    t=(a*P+Q)%n
                    roots=simple_roots(N,a,t,r,k)
                    assert len(roots)<=2
                    S.update(roots)
                assert P in S,(r,k,P,Q,S)
                assert len(S)<=4
                linear_cases+=1
print({'square_fiber_cases':square_cases,'two_linear_form_cases':linear_cases,'status':'PASS'})
