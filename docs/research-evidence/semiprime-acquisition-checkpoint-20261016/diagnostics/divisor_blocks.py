from math import isqrt

def cube_ceiling(n):
    lo, hi = 0, 1 << ((n.bit_length()+2)//3)
    while lo + 1 < hi:
        m = (lo+hi)//2
        if m*m*m < n: lo=m
        else: hi=m
    return hi

def slope_approx(n, a, h):
    # Largest continued-fraction convergent denominator at most h.
    v, w = n, a*a
    p0, p1, q0, q1 = 0, 1, 1, 0
    while w:
        d, rem = divmod(v, w)
        p, q = d*p1+p0, d*q1+q0
        if q > h: break
        p0,p1,q0,q1 = p1,p,q1,q
        v,w=w,rem
    return -p1,q1

def divisors_below_sqrt(n, lower=1):
    u, end = cube_ceiling(n), isqrt(n)
    found, blocks, scalar = set(),0,0
    start=lower
    while start <= end and start < 2*u:
        scalar += 1
        if n % start == 0: found.add(start)
        start += 1
    while start <= end:
        h=min(start//(2*u),end-start+1)
        a,q=slope_approx(n,start,h)
        z=(2*q*n+start)//(2*start)
        assert q <= h and abs(n*q+a*start*start)*h <= start*start
        inv=pow(a,-1,q) if q > 1 else 0
        for j in {v % q for v in (0,1,2,q-2,q-1)}:
            k0=((j-z)*inv)%q
            if k0 >= h: continue
            c=(z+a*k0)//q
            tmax=(h-1-k0)//q
            x0=start+k0
            for d in range(-2,4):
                aa=q*a
                bb=q*(c+d)+x0*a
                cc=x0*(c+d)-n
                disc=bb*bb-4*aa*cc
                if disc < 0: continue
                sq=isqrt(disc)
                if sq*sq != disc: continue
                for num in (-bb-sq,-bb+sq):
                    if num % (2*aa): continue
                    t=num//(2*aa)
                    if 0 <= t <= tmax:
                        x=x0+q*t
                        if n%x == 0: found.add(x)
        start += h
        blocks += 1
    return sorted(found), {'blocks':blocks,'scalar':scalar}

if __name__ == '__main__':
    import random
    rng=random.Random(629)
    values=list(range(1,501))+[rng.randrange(10**10,10**11) for _ in range(8)]
    for n in values:
        got,counts=divisors_below_sqrt(n)
        want=[d for d in range(1,isqrt(n)+1) if n%d==0]
        assert got == want,(n,got,want,counts)
    n=1000003*1000033
    divs,counts=divisors_below_sqrt(n)
    print({'regressions':len(values), 'semiprime':n,'divisors_below_sqrt':divs,**counts})
