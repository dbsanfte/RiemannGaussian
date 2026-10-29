#!/usr/bin/env python3
"""Small deterministic arithmetic diagnostics; no factoring/group simulation.
Checks cylinder finite-difference iff and exact-content phase-fibre bounds.
These examples do not prove universal coverage or an algorithmic speedup.
"""
import argparse,json,math
from pathlib import Path

def centered(x,M):
    x%=M
    return x-M if x>=M//2 else x

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('content-structure-results.json'))
    args=parser.parse_args()
    counts=dict(cylinder_rows=0,cylinder_iff_checks=0,phase_rows=0,
                phase_root_lifts=0,periodicity_checks=0)
    for e in (3,4):
        K=2*3**e;H=K*K;N=K**6-1
        units=[j for j in range(1,K) if math.gcd(j,K)==1]
        for j in units[:3]:
            for a in range(-9,10):
                if not a:continue
                c0=a*j*j*pow(N,-1,K)%K
                for z in (-1,0,1):
                    c=c0+z*K
                    ell=centered(-a*j-c*N*pow(j,-1,H),H)
                    assert (a*j*j+ell*j+c*N)%H==0
                    counts['cylinder_rows']+=1
                    for v in range(e):
                        m=3**v;step=K//m
                        criterion=a%(m*m)==0 and (2*a*j+ell)%(K*m)==0
                        direct=all((a*(j+step*t)**2+ell*(j+step*t)+c*N)%H==0
                                   for t in range(2*m+1))
                        assert direct==criterion
                        counts['cylinder_iff_checks']+=1
        for t in range(e):
            g=3**t;mod=K//g;M=2*e-t;pm=3**M
            for j in units[:2]:
                for A in (1,2,4):
                    C=A*j*j*pow(N,-1,mod)%mod
                    if (g*A+g*C*N)%4:C+=mod
                    a,c=g*A,g*C
                    ell=centered(-a*j-c*N*pow(j,-1,H),H)
                    assert ell%g==0 and C%3
                    F=lambda x:A*x*x+(ell//g)*x+C*N
                    roots=[x for x in range(3**e) if F(x)%pm==0]
                    assert len(roots)**2<=4*g
                    counts['phase_rows']+=1
                    for x in roots:
                        derivative=2*A*x+ell//g
                        assert derivative%(3**(e-t))==0
                        for z in range(3**(M-e)):
                            assert F(x+3**e*z)%pm==0
                            counts['periodicity_checks']+=1
                    allroots=sum(F(x)%pm==0 for x in range(pm))
                    assert allroots==len(roots)*3**(M-e)
                    counts['phase_root_lifts']+=allroots
    out=dict(status='PASS',checks=counts,
             scope='small public arithmetic identities only; no coverage/factoring campaign')
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))
if __name__=='__main__':main()
