#!/usr/bin/env python3
"""Exploratory native half derivative; rigorously encloses the infinite tail."""

from fractions import Fraction as Q
from pathlib import Path
import json
import time
import flint

BASE=Path(__file__).resolve().parent
DEST=BASE/'fractional-prime-results'


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def box(r):return flint.acb(flint.arb(0,r),flint.arb(0,r))


def numerator(s,sigma,K=12,U=8):
    delta=Q(1,32);R=Q(1,16)
    series=flint.acb_series([s,1],prec=K+1).zeta()
    low=-sum((series[k]*real(delta)**(2*k-1)/(2*k-1) for k in range(1,K+1)),flint.acb(0))
    M=(s+box(real(R))).zeta().abs_upper()
    q=real(delta*delta/R)
    low_error=M/real(delta)*q**(K+1)/(2*K+1)/(1-q)
    z=s.zeta()
    def integrand(u,analytic):
        # This quotient is meromorphic: non-finite values at possible poles
        # automatically reject analytic integration enclosures.
        return (z-(s+u*u).zeta())/(u*u)
    mid=flint.acb(0)
    edges=[real(delta),flint.arb('0.25'),flint.arb(1),flint.arb(3),flint.arb(U)]
    for a,b in zip(edges,edges[1:]):
        mid+=flint.acb.integral(integrand,a,b,abs_tol=flint.arb('1e-25'),rel_tol=flint.arb('1e-25'),eval_limit=20000,depth_limit=30)
    high=(z-1)/U
    x=real(sigma+U*U)
    high_error=flint.arb(2)**(-x)*(1+2/(x-1))/(2*flint.arb(2).log()*U**3)
    E=(low_error+high_error)/flint.arb.pi().sqrt()
    value=(low+mid+high)/flint.arb.pi().sqrt()+box(E)
    return value,{'low_error_ball':low_error.str(25),'tail_error_ball':high_error.str(25),
                  'mid_integral_ball':mid.str(25),'K':K,'U':U,'all_passed':value.is_finite()}


def main():
    start=time.monotonic();flint.ctx.prec=320;flint.ctx.cap=20;rows=[]
    for sigma,height in ((Q(4),'3.83'),(Q(1,2),'14.13472514173469379046'),(Q(1,2),'21.02203963877155499263')):
        s=flint.acb(real(sigma),height);N,data=numerator(s,sigma)
        row={'s':[str(sigma),height],'native_fractional_numerator_ball':N.str(25),**data}
        rows.append(row);print(row,flush=True)
    DEST.mkdir(exist_ok=True)
    out={'records':rows,'exploratory_bridge_only':True,'historical_novelty_established':False,
         'all_passed':all(r['all_passed'] for r in rows),'seconds':time.monotonic()-start}
    (DEST/'fractional_prime_probe.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Native half-derivative probe seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
