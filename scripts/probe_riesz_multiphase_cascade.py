#!/usr/bin/env python3
"""Exploratory all-count continuum stress test with several spectral modes.

Uses the same Riesz kernel, largest/least-share masks and positive-cutoff
all-count inverse as probe_riesz_zero_parity.py. The added modes are NOT
actual zeta zeros. This tests a proposed inference from complete one-leg
phase limits; it is not an arithmetic packet calculation or a certificate.
FFT discretisation is checked by the exact inverse-convolution identity.
No ordinary build or CI invokes this script.
"""
import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.signal import fftconvolve
from probe_riesz_zero_parity import DelayModel


def convolve(x,y,step):
    return fftconvolve(x,y)[:len(x)]*step


def inverse_factors(model,grid,r,xis):
    step=grid[1]
    regular=grid>=r-1e-14
    a0=np.zeros_like(grid)
    b0=np.zeros_like(grid)
    a0[regular]=-model.R(grid[regular]/r-1)/grid[regular]
    b0[regular]=model.W(grid[regular]/r)/r
    # Half-weight the density jump at the aligned integration boundary.
    start=round(r/step)
    if abs(grid[start]-r)<1e-12:
        a0[start]=-1/(2*r); b0[start]=1/(2*r)
    a=np.zeros_like(grid,dtype=complex)
    b=np.zeros_like(grid,dtype=complex)
    for xi in xis:
        mode=np.exp(xi*grid)
        ai,bi=a0*mode,b0*mode
        a=a+ai+convolve(a,ai,step)
        b=b+bi+convolve(b,bi,step)
    return a,b


def packet_at_total(model,n,slope,resolution,modes):
    u=10001/20000
    total=slope*n
    length=-2*n*math.log(u)-2*math.log(n+1)
    lam=length/total
    gap=1-lam
    step=1/resolution
    grid=np.arange(round(.5*resolution)+1)*step
    # Negative simple-zero phase plus optional two farther modes.
    eps=u-20001/40000
    xis=[0j] if modes==1 else [0j,(eps-.1j)*total,(eps+(43/370)*1j)*total]
    selected=(grid>=7/16-1e-14)&(grid<=37/80+1e-14)
    s=grid[selected]
    p=1-s
    G=[]; audits=[]
    for r in (3/250,7/250):
        a,b=inverse_factors(model,grid,r,xis)
        f=np.maximum(0,grid-gap)*a
        value=-f-convolve(f,b,step)
        G.append(value[selected])
        inverse_error=a+b+convolve(a,b,step)
        audits.append({'r':r,'inverse_convolution_error_on_packet':float(np.max(np.abs(inverse_error[selected]))),
                       'maximum_cascade_on_packet':float(np.max(np.abs(value[selected])))})
    owner=sum(np.exp(xi*p) for xi in xis)
    integrand=owner*(G[0]-G[1])/(lam*p)
    integral=np.trapezoid(integrand,s)
    # Separate the known same-mode contribution: its large fixed-slice
    # value need not survive radial factorial integration.
    nodes,weights=np.polynomial.legendre.leggauss(48)
    sample=7/16+(37/80-7/16)*(nodes+1)/2
    baseline=np.array([model.G(float(si),float(si-gap),3/250)-
                       model.G(float(si),float(si-gap),7/250) for si in sample])
    baseline_integral=(37/80-7/16)/2*(weights@(baseline/(lam*(1-sample))))
    diagonal=baseline_integral*sum(np.exp(xi) for xi in xis)
    return {'N':n,'log_n_over_N':slope,'lambda':lam,'resolution':resolution,'modes':modes,
            'packet_real':float(integral.real),'packet_imag':float(integral.imag),
            'packet_norm':float(abs(integral)),
            'approximate_same_mode_norm':float(abs(diagonal)),
            'approximate_mixed_mode_norm':float(abs(integral-diagonal)),
            'cutoff_checks':audits}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',nargs='+',type=int,default=[4096,16384,65536])
    parser.add_argument('--resolutions',nargs='+',type=int,default=[32000,64000])
    parser.add_argument('--slope',type=float,default=2.)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    model=DelayModel(3200)
    report={'status':'Uncertified multi-mode continuum stress test; no actual zeta or prime data.',
            'warning':'Fixed total-log slice only. Radial factorial integration and the actual prime measure are not evaluated.',
            'rows':[]}
    for n in args.orders:
        for resolution in args.resolutions:
            for modes in (1,3):
                row=packet_at_total(model,n,args.slope,resolution,modes)
                report['rows'].append(row)
                print(json.dumps(row),flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    main()
