#!/usr/bin/env python3
"""Optional all-count coupled Riesz diagnostic; NOT a prime-sum estimate.

Discretize the cofactor log-share measure, then sum EVERY count by the
exponential-series recurrence. Keep the finite rectangle, moving L/T,
radial core window, distinguished least share and complex modes together.
The old allocation factor is omitted only after JointAllocationError's
independent arithmetic bound. Largest-share exteriors/other owners have
their separate proved arithmetic bounds. No completed-leg transfer is used.

This is a synthetic continuum model with uncertified quadrature/grid error.
Its finite grid is not a Lean certificate. Never run it in routine CI.
"""
import argparse
import hashlib
import itertools
import json
import math
from collections import Counter
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import gammaln
from scipy.signal import fftconvolve

from probe_riesz_joint_masked import rectangle_values, rectangle_grid_values


def gauss(order, lower, upper):
    x, w = leggauss(order)
    return lower+(upper-lower)*(x+1)/2, w*(upper-lower)/2


def series_pair(a):
    """A=exp(-sum a_i X^i), B=exp(+sum a_i X^i), through last index.

    a[:,0]=0. Recurrence is exact for this finite formal power series,
    apart from floating point. No prime-count truncation is made.
    """
    batch, size = a.shape
    aa, bb = np.zeros_like(a), np.zeros_like(a)
    aa[:,0] = bb[:,0] = 1
    deriv = a*np.arange(size)
    for n in range(1,size):
        aa[:,n] = -np.einsum('ij,ij->i',deriv[:,1:n+1],aa[:,n-1::-1])/n
        bb[:,n] = np.einsum('ij,ij->i',deriv[:,1:n+1],bb[:,n-1::-1])/n
    return aa, bb


def modal_series_pair(lambdas, amplitudes, least, step, size):
    """Finite-mode differential recurrence for the same cutoff series.

    D(X)=prod(1-lambda_i X); D X A'=-V A and D X B'=V B.
    V is supported in just m+1 degrees starting at the cutoff cell.
    Complexity is linear in size for a fixed finite mode family.
    The fractional first cell is retained exactly as in series_pair.
    """
    batch, count = lambdas.shape
    dpoly = np.zeros((batch,count+1),dtype=complex)
    dpoly[:,0] = 1
    for j in range(count):
        dpoly[:,1:j+2] -= lambdas[:,j,None]*dpoly[:,:j+1].copy()
    ell = np.maximum(1,np.ceil(least/step-.5).astype(int))
    fraction = np.clip(ell+.5-least/step,0,1)
    gfirst = sum(c*lambdas[:,j]**ell for j,c in enumerate(amplitudes))
    vpoly = fraction[:,None]*gfirst[:,None]*dpoly
    for j,c in enumerate(amplitudes):
        quotient = np.zeros((batch,count),dtype=complex)
        quotient[:,0] = 1
        for h in range(1,count):
            quotient[:,h] = dpoly[:,h]+lambdas[:,j]*quotient[:,h-1]
        vpoly[:,1:] += (c*lambdas[:,j]**(ell+1))[:,None]*quotient
    # A conjugation-invariant mode multiset has exactly real coefficients.
    # Pair every entry once, rather than discarding a numerically small phase
    # in an arbitrary complex model. This prevents an artificial imaginary
    # roundoff channel in the symmetric close-mode stress test.
    remaining = list(range(count))
    real_family = True
    while remaining:
        i = remaining[0]
        match = next((j for j in remaining
                      if amplitudes[j]==np.conj(amplitudes[i]) and
                      np.array_equal(lambdas[:,j],np.conj(lambdas[:,i]))),None)
        if match is None:
            real_family = False
            break
        remaining.remove(i)
        if match!=i:
            remaining.remove(match)
    if real_family:
        dpoly,vpoly = dpoly.real,vpoly.real
    aa = np.zeros((batch,size),dtype=float if real_family else complex)
    bb = np.zeros_like(aa)
    aa[:,0] = bb[:,0] = 1
    rows = np.arange(batch)
    for n in range(1,size):
        for h in range(1,min(count,n)+1):
            common = dpoly[:,h]*(n-h)/n
            aa[:,n] -= common*aa[:,n-h]
            bb[:,n] -= common*bb[:,n-h]
        for h in range(count+1):
            jj = n-ell-h
            valid = jj>=0
            idx = np.maximum(jj,0)
            vv = vpoly[:,h]*valid/n
            aa[:,n] -= vv*aa[rows,idx]
            bb[:,n] += vv*bb[rows,idx]
    return aa,bb


def modal_regression():
    """Cross-check the accelerated recurrence against the quadratic one."""
    step, size = .5/512, 514
    r = np.array([.0123,.0278,.0512])
    lam = np.exp(np.array([[.001+.03j,.0002-.11j,0j]])*np.array([[1],[2],[3]]))
    amplitudes = [1,1,-1]
    x = step*np.arange(size)
    widths = np.clip(x[None,:]+step/2-r[:,None],0,step)
    widths[:,0] = 0
    g = sum(c*lam[:,j,None]**np.arange(size) for j,c in enumerate(amplitudes))
    a = g*widths/np.where(x==0,1,x)
    old = series_pair(a)
    new = modal_series_pair(lam,amplitudes,r,step,size)
    error = max(float(np.max(np.abs(x-y))) for x,y in zip(old,new))
    assert error<1e-10, error
    return {'grid':512,'maximum_coefficient_difference':error}


def modal_precision_check():
    """Audit recurrence rounding against its defining series at 65 digits.

    The accelerated differential recurrence can accumulate more error than
    the quadratic recurrence when its modal roots are close. Report that
    error rather than equating a small inverse-product check with accuracy.
    This does not enclose the continuum or quadrature error.
    """
    import mpmath as mp
    mp.mp.dps = 65
    grid, size = 1024, 1026
    step = .5/grid
    least = np.array([.0123,.0278,.0512])
    totals = np.array([10000,20000,30000])
    modes, amplitudes = [0j,.000025-.006j,.000025+.006j],[1,3,3]
    lam = np.exp(np.array(modes)[None,:]*totals[:,None]*step)
    x = step*np.arange(size)
    widths = np.clip(x[None,:]+step/2-least[:,None],0,step)
    widths[:,0] = 0
    g = sum(c*lam[:,j,None]**np.arange(size) for j,c in enumerate(amplitudes))
    a = g*widths/np.where(x==0,1,x)
    quadratic = series_pair(a)
    accelerated = modal_series_pair(lam,amplitudes,least,step,size)
    rows = []
    for row, (r,total) in enumerate(zip(least,totals)):
        # Compare exactly the same binary input modes, not two slightly
        # different transcendental evaluations of their intended parameters.
        lm = [mp.mpc(float(z.real),float(z.imag)) for z in lam[row]]
        ell = max(1,int(np.ceil(r/step-.5)))
        fraction = mp.mpf(ell)+mp.mpf('.5')-mp.mpf(float(r))/mp.mpf(step)
        values = [mp.mpc(0)]*size
        for j in range(ell,size):
            values[j] = sum(c*l**j for c,l in zip(amplitudes,lm))*\
                (fraction if j==ell else 1)/j
        aa,bb = [mp.mpc(0)]*size,[mp.mpc(0)]*size
        aa[0] = bb[0] = 1
        for j in range(1,size):
            aa[j] = -sum(k*values[k]*aa[j-k] for k in range(ell,j+1))/j
            bb[j] = sum(k*values[k]*bb[j-k] for k in range(ell,j+1))/j
        for index,truth in enumerate((aa,bb)):
            vals = np.array([complex(z) for z in truth])
            scale = max(1,float(np.max(np.abs(vals))))
            rows.append({'T':int(total),'least_share':float(r),'series':'AB'[index],
                         'coefficient_scale':scale,
                         'quadratic_max_error':float(np.max(np.abs(vals-quadratic[index][row]))),
                         'accelerated_max_error':float(np.max(np.abs(vals-accelerated[index][row]))),
                         'accelerated_scaled_error':float(np.max(
                             np.abs(vals-accelerated[index][row])))/scale})
    return {'grid':grid,'decimal_precision':mp.mp.dps,
            'scope':'same finite grid and binary mode inputs; rounding audit only','rows':rows}


def rectangle_grid_regression():
    p,r = np.linspace(.5,.6,13),np.linspace(.005,.06,11)
    error = max(float(np.max(np.abs(rectangle_values(n,p[:,None],r[None,:])-
                                    rectangle_grid_values(n,p,r)))) for n in (25,256,640))
    assert error<1e-13,error
    return {'orders':[25,256,640],'maximum_absolute_difference':error,
            'comparison':'same full finite sum, different evaluation order; no interpolation'}


def finite_regression():
    """Independent subset enumeration on a tiny lattice, including repeats.

    Repeated grid atoms have their factorial symmetry divisor. This checks
    signs/count normalization, not squarefree prime arithmetic or convergence.
    """
    size, lower, d, r = 14, 3, 5.3, 3.2
    a = np.zeros((1,size+2),dtype=complex)
    for j in range(lower,size+2):
        a[0,j] = (1+np.exp((.03+.2j)*j))/j
    aa, bb = series_pair(a)
    via_series = response(aa,bb,1,np.array([size]),np.array([d]),np.array([r]))[0]
    direct = 0j
    for count in range(1,size//lower+1):
        for parts in itertools.combinations_with_replacement(range(lower,size+1),count):
            if sum(parts)!=size:
                continue
            symmetry = math.prod(math.factorial(m) for m in Counter(parts).values())
            hinge = 0.
            for flags in itertools.product((0,1),repeat=count):
                x = sum(p*b for p,b in zip(parts,flags))
                hinge += (-1)**sum(flags)*(max(0,d-x)-max(0,d-r-x))
            direct += (-1)**count*np.prod(a[0,list(parts)])*hinge/symmetry
    error = abs(direct-via_series)
    assert error<1e-12
    return {'direct':[float(direct.real),float(direct.imag)],
            'series':[float(via_series.real),float(via_series.imag)],
            'absolute_difference':float(error)}


def response(aa, bb, step, total_share, cutoff, least):
    """Inverse ramp difference at s and d: sum A_(s-j) B_j min(r,(d-j)+).

    Linear interpolation only in total cofactor share. Empty-cofactor and
    one-sided boundaries are included by A_0=B_0=1 and the positive part.
    The evaluated s is strictly positive; empty middle count contributes 0.
    """
    index = total_share/step
    base = np.floor(index).astype(int)
    frac = index-base
    out = np.zeros(len(index),dtype=complex)
    for shift, weight in ((0,1-frac),(1,frac)):
        n = base+shift
        jj = np.arange(int(n.max())+1)
        ni = n[:,None]-jj
        product = np.take_along_axis(aa,np.maximum(ni,0),axis=1)*bb[:,:len(jj)]
        ramp = np.minimum(least[:,None],np.maximum(0,cutoff[:,None]-step*jj))
        out += weight*np.sum(product*ramp*(ni>=0),axis=1)/step
    return out


def response_tables(aa, bb, step, gap, least):
    """Two convolutions plus exact corner corrections reproduce response."""
    x = step*np.arange(aa.shape[1])[None,:]
    ramp = np.clip(x-gap[:,None],0,least[:,None])
    slope = (x>gap[:,None]).astype(float)-(x>(gap+least)[:,None]).astype(float)
    size = aa.shape[1]
    c0 = fftconvolve(aa*ramp,bb,mode='full',axes=1)[:,:size]/step
    c1 = fftconvolve(aa*slope,bb,mode='full',axes=1)[:,:size]
    return c0,c1


def response_from_tables(aa, bb, tables, step, total_share, gap, least):
    c0,c1 = tables
    index = total_share/step
    n = np.floor(index).astype(int)
    frac = index-n
    rows = np.arange(len(n))
    low = c0[rows,n]+frac*c1[rows,n]
    high = c0[rows,n+1]+(frac-1)*c1[rows,n+1]
    for sign,boundary in ((1,gap),(-1,gap+least)):
        k = np.floor(boundary/step).astype(int)
        beta = boundary/step-k
        valid = n>=k
        bj = bb[rows,np.maximum(n-k,0)]*valid
        low += sign*aa[rows,k]*bj*np.maximum(frac-beta,0)
        high += sign*aa[rows,k+1]*bj*np.maximum(beta-frac,0)
    return (1-frac)*low+frac*high


def run(n, grid, quadrature, table, modes, least_range, amplitudes=None, fast_response=False,
        radial_window=(1.95,2.03), share_quadrature=None, radial_quadrature=None, radial_batch=16):
    amplitudes = [1]*len(modes) if amplitudes is None else amplitudes
    share_quadrature = share_quadrature or quadrature
    radial_quadrature = radial_quadrature or quadrature
    p, wp = gauss(share_quadrature,.5,.6)
    r, wr = gauss(quadrature,*least_range)
    rectangle_nodes = rectangle_grid_values(n,p,r)
    t, wt = gauss(radial_quadrature,radial_window[0]*n,radial_window[1]*n)
    total = old = 0j
    fft_error = 0. if fast_response else None
    conv_check = 0.
    accepted = 0
    for start in range(0,len(t),radial_batch):
        tc, wtc = t[start:start+radial_batch], wt[start:start+radial_batch]
        tt, rr = np.meshgrid(tc,r,indexing='ij')
        tflat, rflat = tt.ravel(), rr.ravel()
        weights = np.outer(wtc,wr).ravel()
        u = 10001/20000
        physical = 20000**n//(10001**n*(n+1))+2
        length = 2*math.log(physical)
        # Every prime represented here satisfies the literal physical masks.
        physical_mask = tflat*rflat>2*math.log(n)
        assert np.max(tflat)*.6<length
        # p>.5 is largest, hence nondominant p<.65; r is the least.
        step = .5/grid
        x = step*np.arange(grid+2)
        aa, bb = modal_series_pair(np.exp(np.array(modes)[None,:]*tflat[:,None]*step),
                                   amplitudes,rflat,step,grid+2)
        gap = 1-length/tflat-rflat
        tables = response_tables(aa,bb,step,gap,rflat) if fast_response else None
        if fast_response:
            sample = np.linspace(0,len(tflat)-1,min(16,len(tflat))).astype(int)
            sf = 1-.55-rflat[sample]
            ordinary = response(aa[sample],bb[sample],step,sf,length/tflat[sample]-.55,rflat[sample])
            fast = response_from_tables(aa[sample],bb[sample],tuple(v[sample] for v in tables),
                                        step,sf,gap[sample],rflat[sample])
            local_error = float(np.max(np.abs(ordinary-fast)))
            assert local_error<1e-9, local_error
            fft_error = max(fft_error,local_error)
        radial = np.exp((n+1)*math.log(u)+n*np.log(tflat)-u*tflat-gammaln(n+1))
        least_mode = sum(amplitude*np.exp(xi*tflat*rflat) for amplitude,xi in zip(amplitudes,modes))
        for index, (pi, wi) in enumerate(zip(p,wp)):
            s = 1-pi-rflat
            d = length/tflat-pi
            cascade = (response_from_tables(aa,bb,tables,step,s,gap,rflat) if fast_response else
                       response(aa,bb,step,s,d,rflat))
            owner_mode = sum(amplitude*np.exp(xi*tflat*pi) for amplitude,xi in zip(amplitudes,modes))
            # Exact finite binomial formula at the integration nodes, with no
            # interpolation of the rectangle weight. Floating point remains.
            finite_weight = np.tile(rectangle_nodes[index],len(tc))
            summand = cascade*owner_mode*least_mode*radial*finite_weight*physical_mask/(pi*rflat*(length/tflat))
            value = wi*np.sum(weights*summand)
            total += value
            if 43/80<=pi<=9/16:
                old += value
        accepted += np.count_nonzero(physical_mask)
        conv_check = max(conv_check,max(abs(np.dot(aa[0,:j+1],bb[0,j::-1]))
                          for j in (grid//3,grid//2,grid)))
    def encode(z):
        return {'real':float(z.real),'imag':float(z.imag),'norm':float(abs(z))}
    # A(X)B(X)=1 is a numerical regression for the count convolution.
    return {'N':n,'share_grid':grid,'quadrature_per_axis':quadrature,
            'largest_share_quadrature':share_quadrature,'radial_quadrature':radial_quadrature,
            'least_share_range':least_range,
            'radial_window':radial_window,
            'rectangle_evaluation':'direct finite binomial formula at quadrature nodes',
            'modes':[[float(z.real),float(z.imag)] for z in modes],
            'density_amplitudes':amplitudes,
            'physical_row_acceptance':float(accepted/(len(t)*len(r))),
            'radial_batch':radial_batch,
            'fft_response_sampled_difference':fft_error,
            'joint_source_normalized':encode(total),
            'old_share_coarse_diagnostic':encode(old),
            'neighbors_coarse_diagnostic':encode(total-old),
            'count_sum':'all counts supported by the discretized positive lower cutoff',
            'inverse_series_product_regression':float(conv_check),
            'log_raw_norm':float(math.log(abs(total))-(n+1)*math.log(u)) if total else None}


def precision_check(n, grid):
    """Independent high-precision recurrence at a dangerous upper least share.

    This checks rounding at one point; it does not enclose the continuum
    discretization error, radial quadrature error, or actual arithmetic sum.
    """
    import mpmath as mp
    mp.mp.dps = 60
    step, r, p, total = mp.mpf(1)/(2*grid), mp.mpf(7)/250, mp.mpf(11)/20, 2*n
    u = mp.mpf(10001)/20000
    physical = 20000**n//(10001**n*(n+1))+2
    length = 2*mp.log(physical)
    s, d = 1-p-r, length/total-p
    modes = [mp.mpc(0),mp.mpc(mp.mpf(1)/40000,-mp.mpf(1)/10),
             mp.mpc(mp.mpf(1)/40000,mp.mpf(43)/370)]
    last = int(mp.floor(s/step))+1
    rows = []
    for family in ([mp.mpc(0)],modes):
        a = [mp.mpc(0)]*(last+1)
        for j in range(1,last+1):
            x = step*j
            width = min(step,max(mp.mpf(0),x+step/2-r))
            a[j] = width*sum(mp.exp(xi*total*x) for xi in family)/x
        aa,bb = [mp.mpc(0)]*(last+1),[mp.mpc(0)]*(last+1)
        aa[0] = bb[0] = 1
        start = next(j for j in range(1,last+1) if a[j])
        for k in range(1,last+1):
            aa[k] = -sum(j*a[j]*aa[k-j] for j in range(start,k+1))/k
            bb[k] = sum(j*a[j]*bb[k-j] for j in range(start,k+1))/k
        base, frac = int(mp.floor(s/step)),mp.frac(s/step)
        val = 0
        for shift,weight in ((0,1-frac),(1,frac)):
            k = base+shift
            val += weight*sum(aa[k-j]*bb[j]*min(r,max(0,d-step*j))
                              for j in range(k+1))/step
        an = np.array([[complex(z) for z in a]])
        an = np.pad(an,((0,0),(0,1)))
        na,nb = series_pair(an)
        ordinary = response(na,nb,float(step),np.array([float(s)]),
                            np.array([float(d)]),np.array([float(r)]))[0]
        rows.append({'mode_count':len(family),'high_precision_response':[str(val.real),str(val.imag)],
                     'double_response':[float(ordinary.real),float(ordinary.imag)],
                     'absolute_rounding_difference':str(abs(val-complex(ordinary)))})
    return {'N':n,'share_grid':grid,'decimal_precision':mp.mp.dps,'p':str(p),'r':str(r),
            'T':total,'cutoff':str(d),'rows':rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',type=int,nargs='+',default=[640,1536,4096])
    parser.add_argument('--grids',type=int,nargs='+',default=[512,1024])
    parser.add_argument('--quadrature',type=int,default=24)
    parser.add_argument('--share-quadrature',type=int)
    parser.add_argument('--radial-quadrature',type=int)
    parser.add_argument('--radial-batch',type=int,default=16)
    parser.add_argument('--precision-check',action='store_true')
    parser.add_argument('--recurrence-precision-check',action='store_true',
                        help='only audit close-mode recurrence rounding at 65 digits')
    parser.add_argument('--least-range',type=float,nargs=2,default=[3/250,7/250])
    parser.add_argument('--analytic-mode',action='store_true',
                        help='stress-test a positive-residue mode analytic beyond the required disk')
    parser.add_argument('--fft-response',action='store_true')
    parser.add_argument('--negative-frequency',type=float,default=.2)
    parser.add_argument('--close-modes',action='store_true',
                        help='test the selected mode with an exposed symmetric pair at offsets +/-0.006')
    parser.add_argument('--close-gain',type=float,default=1/40000,
                        help='horizontal displacement for --close-modes (zero tests the common half-plane)')
    parser.add_argument('--close-frequency',type=float,default=3/500)
    parser.add_argument('--close-multiplicity',type=int,default=1,
                        help='positive integer multiplicity of each competing synthetic mode')
    parser.add_argument('--radial-window',type=float,nargs=2,default=[1.95,2.03])
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    result={'status':'uncertified all-count continuum diagnostic; NOT a literal prime transfer',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'error':'grid and quadrature errors must be refined; no rigorous error enclosure',
            'finite_subset_regression':finite_regression(),
            'modal_recurrence_regression':modal_regression(),
            'rectangle_dependency_sha256':hashlib.sha256(
                Path(__file__).with_name('probe_riesz_joint_masked.py').read_bytes()).hexdigest(),
            'rectangle_grid_regression':rectangle_grid_regression(),'rows':[]}
    if args.recurrence_precision_check:
        result['recurrence_precision'] = modal_precision_check()
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result['recurrence_precision']),flush=True)
        return
    u = 10001/20000
    modes = [0j,complex(u-20001/40000,-.1),complex(u-20001/40000,43/370)]
    families = [([0j],[1]),(modes,[1,1,1])]
    if args.close_modes:
        close = [0j,complex(args.close_gain,-args.close_frequency),
                 complex(args.close_gain,args.close_frequency)]
        assert args.close_multiplicity>=1
        assert all(abs(u-xi)>u for xi in close[1:])
        families = [(close,[1,args.close_multiplicity,args.close_multiplicity])]
        result['close_mode_scope'] = ('synthetic actual-style negative residues; each competing '
            'complete mode is outside the selected radius; not an actual zeta-zero configuration')
    if args.analytic_mode:
        negatives = [0j,complex(u-20001/40000,-args.negative_frequency)]
        positive = complex(u-.5,.6)
        assert abs(u-positive)>4*u/3
        families = [(negatives,[1,1]),(negatives+[positive],[1,1,-1])]
        result['analytic_mode_scope'] = ('synthetic positive-residue mode with complete-leg '
            'coefficient radius >4/3; NOT asserted to be the actual zeta remainder')
    for n in args.orders:
        if args.precision_check:
            for grid in args.grids:
                row = precision_check(n,grid)
                result['rows'].append(row)
                print(json.dumps(row),flush=True)
                args.output.write_text(json.dumps(result,indent=2)+'\n')
            continue
        for grid in args.grids:
            for family,amplitudes in families:
                row = run(n,grid,args.quadrature,None,family,args.least_range,amplitudes,
                          args.fft_response,args.radial_window,
                          args.share_quadrature,args.radial_quadrature,args.radial_batch)
                result['rows'].append(row)
                print(json.dumps(row),flush=True)
                args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()
