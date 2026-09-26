#!/usr/bin/env python3
"""Optional least-coordinate collision diagnostic; NOT a carrier estimate.

The exact two-chamber transform is checked by quadrature. A separate rate
test combines balanced synthetic modes with the actual factorial boundary
proportions. A positive budget does not prove that its residue survives the
Riesz kernel or the joined count sum. Neither test samples actual primes.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.optimize import minimize_scalar
from scipy.special import gammaln, logsumexp
from scipy.stats import binom

U = mp.mpf(10001)/20000
DELTA = mp.mpf(1)/40000
ETA = mp.mpf(3)/500


def length_with_error(N):
    """Literal floor length, or its asymptotic value with a proved envelope.

    If X=u^-N/(N+1), then 0<L_N-2*log(X)<=4/X. The high-order
    calculation does not substitute the fixed slice T=2N.
    """
    xlog = -N*mp.log(U)-mp.log(N+1)
    if N <= 8192:
        cutoff = 20000**N//(10001**N*(N+1))
        return 2*mp.log(cutoff+2), mp.mpf(0)
    return 2*xlog, 4*mp.exp(-xlog)


def equal_riesz(k, r, d):
    """Exactly the binomially grouped finite-difference kernel.

    Equality of cofactor logs is a continuum boundary, not a squarefree
    arithmetic label. This evaluates only the kernel on that boundary.
    """
    return mp.fsum((-1)**j*math.comb(k,j)*max(mp.mpf(0),d-j*r)
                   for j in range(k+1))


def entropy_cost(p, k, b):
    r = (1-p)/k
    a = min(max((1-b)*p/(1-r), mp.mpf(21)/40), mp.mpf(23)/40)
    return mp.fsum(x*mp.log(x/y) for x,y in
                   zip((a,b,1-a-b),(p,r,1-p-r)))


def budget(p, k, b):
    return mp.log(U/(U-DELTA*(1-p)))-entropy_cost(p,k,b)


def face_log(N,p,r,b):
    """The literal beta face times the whole marked-owner order band.

    Low face h=ceil(N/100)-2; high face h=floor(N/25)-1.
    These include the existing +1 derivative-order convention.
    """
    jlo,jhi=(21*N+39)//40,23*N//40
    h = (N+99)//100-2 if b == mp.mpf(1)/100 else N//25-1
    assert 0 <= h < N and jlo <= jhi
    r,p=float(r),float(p)
    lbeta = gammaln(N+2)-gammaln(h+1)-gammaln(N-h+1)
    lbeta += h*math.log(r)+(N-h)*math.log1p(-r)
    orders=np.arange(jlo,jhi+1)
    conditional=logsumexp(binom.logpmf(orders,N-h,p/(1-r)))
    return float(lbeta+conditional),h


def minimum_checks():
    d=U-DELTA
    a,b=d+mp.j*ETA,d-mp.j*ETA
    ia=mp.quad(lambda v:mp.exp(-a*v),[0,mp.inf])
    ib=mp.quad(lambda v:mp.exp(-b*v),[0,mp.inf])
    rows=[]
    for h in (0,1,4,12):
        observed=mp.quad(lambda r:r**h/mp.factorial(h)*mp.exp(-2*d*r)*(ia+ib),
                         [0,mp.inf])
        expected=1/(a*b*(2*d)**h)
        err=abs(observed-expected)
        assert err < mp.mpf('1e-65')
        rows.append(dict(h=h,integral=mp.nstr(observed,40),absolute_error=mp.nstr(err,8)))
    return dict(scope='Two ordered continuum chambers, with no Riesz/count projection',
        source_radius=mp.nstr(U,30),node_real=mp.nstr(d,30),node_norm=mp.nstr(abs(a),30),
        separate_leg_log_rate=mp.nstr(mp.log(U/abs(a)),30),
        normalized_minimum_log_rate=mp.nstr(mp.log(U/d),30),quadrature=rows)


def interior_checks():
    """A zero-cost candidate at count 45, not a full response calculation."""
    p,r,b=mp.mpf(14)/25,mp.mpf(1)/100,mp.mpf(1)/100
    cost=entropy_cost(p,44,b)
    assert abs(cost)<mp.mpf('1e-85')
    kernel=equal_riesz(44,r,mp.mpf(693)/1000-p)
    assert abs(kernel-mp.mpf(106328047)/125)<mp.mpf('1e-65')
    rows=[]
    for excess in ('0.00005','0.000001','0.000000001'):
        u=mp.mpf('.5')+mp.mpf(excess)
        delta=(u-mp.mpf('.5'))/2
        gain=mp.log(u/(u-(1-p)*delta))
        assert gain>0 and abs(u-delta+mp.j*ETA)>u
        rows.append(dict(radius=mp.nstr(u,30),horizontal_gain=mp.nstr(delta,30),
                         candidate_budget=mp.nstr(gain,30)))
    return dict(total_prime_count=45,owner_share=mp.nstr(p,30),least_share=mp.nstr(r,30),
                entropy_cost=mp.nstr(cost,30),equal_cofactor_kernel=mp.nstr(kernel,30),
                shrinking_radius_tests=rows,
                warning='A positive candidate rate is not a nonzero integrated residue or a prime-sum obstruction.')


def row(N,k,b,p=None):
    if p is None:
        p=mp.mpf(21)/40
    r=(1-p)/k
    alpha=U-DELTA*(1-p)
    T=mp.mpf(N)/alpha
    L,Lerr=length_with_error(N)
    lam=L/T
    coeff=equal_riesz(k,r,lam-p)
    logface,h=face_log(N,p,r,b)
    gain=(N+1)*mp.log(U/alpha)
    return dict(N=N,total_prime_count=k+1,cofactor_count=k,
        boundary='lower' if b==mp.mpf(1)/100 else 'upper',face_order=h,
        owner_share=mp.nstr(p,30),least_share=mp.nstr(r,30),
        radial_saddle_over_N=mp.nstr(T/N,30),moving_length=mp.nstr(L,40),
        length_error_bound=mp.nstr(Lerr,8),riesz_ratio=mp.nstr(lam,30),
        equal_cofactor_kernel=mp.nstr(coeff,30),
        kernel_length_error_bound=mp.nstr(2**k*Lerr/T,8),
        log_factorial_face=logface,log_radial_gain=mp.nstr(gain,30),
        candidate_log_amplitude=float(gain)+logface,
        candidate_log_amplitude_per_N=(float(gain)+logface)/N,
        limiting_budget=mp.nstr(budget(p,k,b),30),
        warning='The candidate amplitude omits the oscillatory residue, integration and cross-count cancellation.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',nargs='+',type=int,default=[256,640,1536,4096,8192,65536,262144,1048576])
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    mp.mp.dps=90
    global U,DELTA,ETA
    U,DELTA,ETA=mp.mpf(10001)/20000,mp.mpf(1)/40000,mp.mpf(3)/500
    report=dict(scope='Diagnostic only: no actual prime sum, full modal counterexample, or signed floor',
        target_unchanged='lowerThresholdPacket(3..55)-shortOverflowPacket(3..13)',
        unresolved='Nonzero joint residue and cancellation across count classes must be checked next.',
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        exact_minimum_model=minimum_checks(),interior_zero_cost=interior_checks(),
        boundary_scan=[],finite_faces=[])
    for b,counts in ((mp.mpf(1)/25,range(2,14,2)),(mp.mpf(1)/100,range(14,56,2))):
        for k in counts:
            result=minimize_scalar(lambda p:-float(budget(mp.mpf(p),k,b)),
                bounds=(.5,.6),method='bounded',options={'xatol':1e-13})
            p=mp.mpf(result.x)
            report['boundary_scan'].append(dict(total_prime_count=k+1,
                boundary=float(b),optimized_owner=float(p),candidate_budget=mp.nstr(budget(p,k,b),30)))
    for N in args.orders:
        assert N >= 256
        for k,b in ((12,mp.mpf(1)/25),(48,mp.mpf(1)/100)):
            report['finite_faces'].append(row(N,k,b))
        report['finite_faces'].append(row(N,44,mp.mpf(1)/100,mp.mpf(14)/25))
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(minimum=report['exact_minimum_model'],
        final_faces=report['finite_faces'][-3:]),indent=2))


if __name__=='__main__':
    main()
