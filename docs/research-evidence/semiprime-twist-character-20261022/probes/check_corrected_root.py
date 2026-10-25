import runpy
from math import gcd
s=runpy.run_path(__file__.replace("check_corrected_root.py","check_formulas.py"))

def local_tau(z,p):
    e=1 if p%4==1 else -1
    if e<0:z=(z[0]%p,-z[1]%p)
    else:z=(z[0]%p,z[1]%p)
    y=s["fp_pow"](z,(p-e)//4,p,-1)
    return next(h for h,u in enumerate(s["units"]) if (u[0]%p,u[1]%p)==y)
count=0
for p,q in ((3,7),(5,13),(5,7),(7,17),(13,17),(11,19)):
    N=p*q;sig=1 if N%4==1 else-1;E=N-sig;k=E//4
    for a in range(1,N):
        nn=a*a+1
        if gcd(nn,N)>1:continue
        z=((a*a-1)*pow(nn,-1,N)%N,2*a*pow(nn,-1,N)%N)
        h=s["quartic"]((a,1),(N,0))
        C=s["fp_mul"](s["fp_pow"](z,k,N,-1),s["units"][(-sig*h)%4],N,-1)
        assert s["fp_pow"](C,4,N,-1)==s["fp_pow"](z,E,N,-1)
        assert (local_tau(C,p)+local_tau(C,q))%4==0
        for t in range(1,5):
            Ct=s["fp_pow"](C,k**(t-1),N,-1)
            assert s["fp_pow"](Ct,4,N,-1)==s["fp_pow"](z,E*k**(t-1),N,-1)
            assert (local_tau(Ct,p)+local_tau(Ct,q))%4==0
        count+=1
print({"corrected_root_cases":count,"sign_patterns":["++","+-","-+","--"],"iterations_checked":4})
