#!/usr/bin/env python3
"""Optional coupled radial/share audit; not actual primes or a certificate.

The ordered modal sector assigns leftMode to the largest prime and
rightMode to every cofactor prime. All cofactor counts, their Riesz signs,
both least-share cutoffs, the physical lower cutoff and the exact integer
moving length are retained. The count inverse is the independently
cross-checked Dickman/Buchstab MODEL in probe_riesz_zero_parity.py; its
identification is not yet a Lean theorem. This sector is not the sum over
all assignments of both modes to every prime.

The literal e^(-T/2) radial kernel is multiplied by the mode density
e^((1/2-pole(q))*T), giving e^(-pole(q)*T). Using (u/pole)^k inside another
radial integral would integrate the Gamma weight twice.

Requires numpy, scipy and gmpy2. No ordinary build or CI invokes this probe.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import gmpy2
import numpy as np
import scipy
from numpy.polynomial import Chebyshev
from scipy.integrate import quad
from scipy.special import gammaln, gammainc

from probe_riesz_zero_parity import DelayModel
from probe_riesz_multiphase_cascade import inverse_factors, convolve

U = 10001/20000
AXIS = 20001/40000
QLO, QHI = 43/80, 9/16
RLO, RHI = 3/250, 7/250
SLO, SHI = 39/20, 203/100
GAMMA = 8/37
OMEGA = GAMMA*(QHI-QLO)


def literal_length(n):
    """Compute the repo's floor as an exact integer, including the +2."""
    cutoff = gmpy2.mpz(20000)**n//((gmpy2.mpz(10001)**n)*(n+1))
    with gmpy2.context(precision=192):
        value = 2*gmpy2.log(cutoff+2)
        return float(value), str(value), cutoff.bit_length()


def radial_nodes(n, rate, degree):
    """Composite Gaussian quadrature on the ENTIRE prescribed radial window."""
    shape = n+1
    spread = math.sqrt(shape)
    lo, hi = (rate*SLO*n-shape)/spread, (rate*SHI*n-shape)/spread
    edges = np.linspace(lo, hi, max(1, math.ceil((hi-lo)/2))+1)
    z, w = np.polynomial.legendre.leggauss(degree)
    points, weights = [], []
    for a, b in zip(edges, edges[1:]):
        t = (a+b)/2+(b-a)/2*z
        x = shape+spread*t
        # Stirling subtraction is safe for the present N range; exact
        # Gamma window mass below independently audits this quadrature.
        density = np.exp(n*np.log(x)-x-gammaln(shape))*spread
        points.extend(x/rate)
        weights.extend(w*(b-a)/2*density)
    return np.asarray(points), np.asarray(weights)


def amplitude(model, n, total, length, q, physical=True):
    lam = length/total
    rmin = max(RLO, 2*math.log(n)/total) if physical else RLO
    if rmin >= RHI or q >= lam:
        return 0.
    s, d = 1-q, lam-q
    assert 0 < d < s and s < q and q < lam
    return (model.G(s, d, rmin)-model.G(s, d, RHI))/(lam*q)


def share_integral(model, n, total, length, degree, physical=True):
    # Lobatto points include both hard endpoints. A polynomial surrogate
    # removes interpolation noise from QAWO's high-frequency moments.
    q = (QLO+QHI)/2+(QHI-QLO)/2*np.cos(np.arange(degree+1)*math.pi/degree)
    vals = np.array([amplitude(model,n,total,length,float(x),physical) for x in q])
    poly = Chebyshev.fit(q-QLO,vals,degree,domain=[0,QHI-QLO])
    frequency = GAMMA*total
    rc, ec = quad(poly,0,QHI-QLO,weight='cos',wvar=frequency,
                  epsabs=1e-27,epsrel=2e-11,limit=120)
    rs, es = quad(poly,0,QHI-QLO,weight='sin',wvar=frequency,
                  epsabs=1e-27,epsrel=2e-11,limit=120)
    leading = (vals[-1]-vals[0]*np.exp(-1j*frequency*(QHI-QLO)))/(1j*frequency)
    return complex(rc,-rs), leading, ec+es


def describe(value, log_prefactor, n):
    if value == 0:
        return {'norm':0.,'log10_norm':None,'raw_log10_norm':None,'phase':None}
    lognorm = math.log(abs(value))+log_prefactor
    phase = math.atan2(value.imag,value.real)
    norm = math.exp(lognorm) if lognorm < 700 else None
    return {'norm':norm,'real':None if norm is None else norm*math.cos(phase),
            'imag':None if norm is None else norm*math.sin(phase),
            'log10_norm':lognorm/math.log(10),
            'raw_log10_norm':(lognorm-(n+1)*math.log(U))/math.log(10),
            'phase':phase}


def sample(model, n, radial_degree, share_degree):
    length, length192, bits = literal_length(n)
    ts, ws = radial_nodes(n,AXIS,radial_degree)
    values, leading, errors = [], [], []
    for t in ts:
        a,b,c = share_integral(model,n,float(t),length,share_degree)
        values.append(a); leading.append(b); errors.append(c)
    value = ws@np.asarray(values)
    pref = (n+1)*math.log(U/AXIS)
    # This bare model is exactly the same two-mode resonance, with the
    # radial power N rather than the older Lean example's N+1.
    bare = ws@(-np.expm1(-1j*OMEGA*ts)/(1j*GAMMA*ts))
    complete_bare = U/(1j*GAMMA*n)*((U/AXIS)**n-(U/complex(AXIS,OMEGA))**n)
    # The genuine single-phase continuum MODEL is integrated separately,
    # with rate u, including the moving lambda. It is not frozen at 2N.
    tb, wb = radial_nodes(n,U,radial_degree)
    z,w = np.polynomial.legendre.leggauss(share_degree+8)
    qs = (QLO+QHI)/2+(QHI-QLO)/2*z
    baseline = sum(weight*(QHI-QLO)/2*sum(
        wi*amplitude(model,n,float(t),length,float(q)) for wi,q in zip(w,qs))
        for t,weight in zip(tb,wb))
    exact_mass = gammainc(n+1,AXIS*SHI*n)-gammainc(n+1,AXIS*SLO*n)
    saddle = n/AXIS
    endpoint_amp = amplitude(model,n,saddle,length,QLO)
    return {'N':n,'radial_degree':radial_degree,'share_degree':share_degree,
            'radial_evaluations':len(ts),'length_192bit':length192,'cutoff_bit_length':bits,
            'lambda_at_resonant_saddle':length/saddle,
            'gamma_window_mass':float(exact_mass),
            'gamma_mass_quadrature_error':float(ws.sum()-exact_mass),
            'bare_window':describe(complex(bare),pref,n),
            'bare_complete':describe(complex(complete_bare),0.,n),
            'all_count_ordered_sector':describe(complex(value),pref,n),
            'share_endpoint_approximation':describe(complex(ws@np.asarray(leading)),pref,n),
            'single_phase_all_count':describe(complex(baseline),0.,n),
            'endpoint_amplitude_at_saddle':endpoint_amp,
            'unscaled_inner_quadrature_error_bound':float(np.abs(ws)@np.asarray(errors)),
            'warning':'Ordered modal sector only; full mixed-colour assignments and literal primes are not evaluated. Original factorial and allocation weights are not simulated; their already-proved arithmetic error estimates do not automatically transfer to this model. QAWO reports only its inner quadrature error, not a total error bound.'}


def sample_mixture(model,n,radial_degree,resolution):
    """All assignments of the same two modes to all prime legs.

    This independent FFT test is useful only with resolution refinement.
    It has absolute convolution/roundoff errors and must not be used to
    certify residuals smaller than those errors.
    """
    length,length192,bits=literal_length(n)
    ts,ws=radial_nodes(n,AXIS,radial_degree)
    grid=np.arange(round(.5*resolution)+1)/resolution
    selected=(grid>=7/16-1e-14)&(grid<=37/80+1e-14)
    s=grid[selected];q=1-s
    values=[];audits=[]
    for total in ts:
        lam=length/total;gap=1-lam
        rlow=max(RLO,2*math.log(n)/total)
        xis=[-.1j*total,(43/370)*1j*total]
        owner=sum(np.exp(xi*q) for xi in xis)
        pieces=[]
        for r in (rlow,RHI):
            a,b=inverse_factors(model,grid,r,xis)
            f=np.maximum(0,grid-gap)*a
            G=-f-convolve(f,b,1/resolution)
            pieces.append(G[selected])
            audits.append(float(np.max(np.abs((a+b+convolve(a,b,1/resolution))[selected]))))
        values.append(np.trapezoid(owner*(pieces[0]-pieces[1])/(lam*q),s))
    value=complex(ws@np.asarray(values))
    return {'N':n,'resolution':resolution,'radial_degree':radial_degree,
            'radial_evaluations':len(ts),'length_192bit':length192,'cutoff_bit_length':bits,
            'all_assignments':describe(value,(n+1)*math.log(U/AXIS),n),
            'maximum_inverse_convolution_residual':max(audits),
            'warning':'Full two-mode continuum mixture, FFT discretisation. The inverse residual is a diagnostic, not a proved error bar for the packet. Refine radial degree as well as FFT resolution: high-frequency same-mode terms can alias. Small residuals do not settle the full-mixture limit.'}


def endpoint_diagnostics(model):
    """Endpoint data, not an evaluation or bound of all mode assignments."""
    lam = -2*AXIS*math.log(U)
    s,d = 1-QLO,lam-QLO
    rows = []
    for r in (RLO,RHI):
        rows.append({'r':r,
                     'ordered_endpoint_amplitude':model.G(s,d,r)/(lam*QLO),
                     'first_mixed_boundary_amplitude':
                         (model.G(s-r,d,r)-model.G(s-r,d-r,r))/(r*lam*QLO),
                     'first_mixed_boundary_imaginary_pole':GAMMA*r,
                     'complete_radial_rate_at_first_mixed_boundary':
                         math.log(U/abs(complex(AXIS,GAMMA*r)))})
    return {'limiting_lambda_at_resonant_saddle':lam,'rows':rows,
            'warning':'Spectral endpoint diagnostics only. A separated endpoint does not by itself bound the full remaining assignments with moving Riesz masks.'}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders',nargs='+',type=int,default=[256,640,1536,4096,8192,32768,131072,524288,1048576])
    ap.add_argument('--steps',type=int,default=3200)
    ap.add_argument('--radial-degree',type=int,default=16)
    ap.add_argument('--share-degree',type=int,default=24)
    ap.add_argument('--mixture',action='store_true',help='Evaluate all two-mode assignments using the independent FFT audit')
    ap.add_argument('--resolution',type=int,default=128000)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    model=DelayModel(args.steps)
    rate=math.log(U/AXIS)
    report={'status':('Exploratory full two-mode continuum mixture; unresolved numerical cancellation audit.' if args.mixture else
                      'Exploratory radial all-count ordered-mode model, not an arithmetic certificate.'),
            'numpy':np.__version__,'scipy':scipy.__version__,'gmpy2':gmpy2.version(),
            'steps_per_unit':args.steps,
            'input_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
                            (Path(__file__),Path(__file__).with_name('probe_riesz_zero_parity.py'),
                             Path(__file__).with_name('probe_riesz_multiphase_cascade.py'))},
            'modes':{'left':'20001/40000+i/10','right':'20001/40000-43i/370'},
            'normalization':'u^(N+1) integral T^N/N! exp(-T/2) exp((1/2-pole(q))*T) A(L_N/T,q) dq dT',
            'growth_exponent':rate,'saddle_T_over_N':1/AXIS,
            'radial_tail_rates':{str(t):AXIS*t-1-math.log(AXIS*t) for t in (SLO,SHI)},
            'endpoint_diagnostics':endpoint_diagnostics(model),
            'rows':[]}
    for n in args.orders:
        row=(sample_mixture(model,n,args.radial_degree,args.resolution) if args.mixture else
             sample(model,n,args.radial_degree,args.share_degree))
        report['rows'].append(row)
        print(json.dumps(row),flush=True)
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    main()
