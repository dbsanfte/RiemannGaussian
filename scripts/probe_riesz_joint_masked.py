#!/usr/bin/env python3
"""Optional coupled factorial/least-prime/Riesz continuum stress test.

All total-log, physical, least-prime, original allocation and factorial
masks are evaluated in the integrand. Modes are synthetic, not actual
zeta zeros. Sample error and omitted prime counts are NOT certified.
No routine build invokes this probe. No spectral-to-prime transfer follows.
"""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
from scipy.interpolate import RectBivariateSpline
from scipy.special import gammaln
from scipy.stats import binom, qmc


def rectangle_values(n, p, r):
    """Exact finite multinomial probability, evaluated in floating point.

    Sum the least order first; conditional on it the marked order is
    binomial. The owner-order condition is automatic on this rectangle.
    """
    p, r = np.broadcast_arrays(p, r)
    value = np.zeros(p.shape)
    jlo, jhi = (21*n+39)//40, 23*n//40
    for h in range(max(0,(n+99)//100-1), n//25):
        assert 13*n < 40*(jlo+h) and 40*(jhi+h) <= 27*n
        conditional = binom.cdf(jhi,n+1-h,p/(1-r))-binom.cdf(jlo-1,n+1-h,p/(1-r))
        value += binom.pmf(h,n+1,r)*conditional
    return value


def rectangle_grid_values(n, ps, rs):
    """The same finite sum on a Cartesian grid, with its marginal reused.

    Only floating-point zero marginal entries are skipped. There is no
    tail-probability threshold or normal approximation. Chunking changes
    summation order, which the regression checks independently.
    """
    ps,rs = np.asarray(ps),np.asarray(rs)
    out = np.zeros((len(ps),len(rs)))
    jlo,jhi = (21*n+39)//40,23*n//40
    hs = np.arange(max(0,(n+99)//100-1),n//25)
    if not len(hs):
        return out
    assert 13*n<40*(jlo+hs[0]) and 40*(jhi+hs[-1])<=27*n
    for col,r in enumerate(rs):
        marginal = binom.pmf(hs,n+1,r)
        active = np.flatnonzero(marginal)
        for start in range(0,len(active),512):
            indices = active[start:start+512]
            remaining = n+1-hs[indices]
            probability = ps[:,None]/(1-r)
            conditional = (binom.cdf(jhi,remaining[None,:],probability)-
                           binom.cdf(jlo-1,remaining[None,:],probability))
            out[:,col] += np.sum(conditional*marginal[indices][None,:],axis=1)
    return out


def rectangle_table(n):
    ps, rs = np.linspace(.5,.6,201), np.linspace(3/250,7/250,101)
    values = rectangle_values(n,ps[:,None],rs[None,:])
    interp = RectBivariateSpline(ps,rs,values)
    rng = np.random.default_rng(20260925)
    p = rng.uniform(.5,.6,256)
    r = rng.uniform(3/250,7/250,256)
    exact = rectangle_values(n,p,r)
    error = np.max(np.abs(exact-interp.ev(p,r)))
    return interp, float(error)


def trial(n, count, power, seed, table):
    middle_count = count-2
    points = qmc.Sobol(count,scramble=True,seed=seed).random_base2(power)
    p, r = .5+.1*points[:,0], 3/250+(4/250)*points[:,1]
    total = n*(1.95+.08*points[:,2])
    u = 10001/20000
    physical = 20000**n//(10001**n*(n+1))+2
    length = 2*math.log(physical)
    lam = length/total
    free = 1-p-(middle_count+1)*r
    cuts = np.sort(points[:,3:],axis=1)
    gaps = np.diff(np.column_stack((np.zeros(len(p)),cuts,np.ones(len(p)))),axis=1)
    middle = r[:,None]+np.maximum(free,0)[:,None]*gaps
    xs = np.column_stack((p,middle,r))
    assert xs.shape[1] == count
    cofactor = xs[:,1:]
    assert np.all(1-p <= lam)
    d = lam-p
    hinge = np.zeros(len(p))
    for flags in itertools.product((0,1),repeat=count-1):
        subtotal = cofactor @ np.asarray(flags)
        hinge += (-1)**sum(flags)*np.maximum(0,d-subtotal)
    physical_mask = np.all((xs*total[:,None] > 2*math.log(n)) &
                           (xs*total[:,None] < length),axis=1)
    mask = physical_mask & (free>0)
    j = np.arange(n+2)
    unpaid = j[(j<=13*n//32)&(5*(n+1-j)<4*n)]
    allocated = np.sum(binom.cdf(int(unpaid[-1]),n+1,1-xs)-
                       binom.cdf(int(unpaid[0])-1,n+1,1-xs),axis=1)
    rectangle = np.clip(table.ev(p,r),0,1)
    volume = .1*(4/250)*np.maximum(free,0)**(middle_count-1)
    volume /= math.factorial(middle_count-1)*math.factorial(middle_count)
    radial = np.exp((n+1)*math.log(u)+n*np.log(total)-u*total-gammaln(n+1))*(.08*n)
    real_density = (-1)**count*hinge*volume/(lam*np.prod(xs,axis=1))
    real_density *= radial*rectangle*(1-allocated)*mask
    eps = u-20001/40000
    # Every added complete-leg denominator has modulus >u. This is only
    # an exposed-style synthetic family, not an actual zero divisor.
    multi = np.prod(1+np.exp((eps-.1j)*xs*total[:,None])+
                    np.exp((eps+(43/370)*1j)*xs*total[:,None]),axis=1)
    old = (43/80<=p)&(p<=9/16)
    def stats(v):
        mean = np.mean(v)
        return {'real':float(np.real(mean)), 'imag':float(np.imag(mean)),
                'norm':float(abs(mean)), 'sample_l2_over_sqrt_samples':float(np.std(v)/math.sqrt(len(v)))}
    return {'N':n,'count':count,'seed':seed,'samples':len(p),
            'pure_selected':stats(real_density),
            'joint_modes':stats(real_density*multi),
            'old_share_modes':stats(real_density*multi*old),
            'neighbors_modes':stats(real_density*multi*(~old)),
            'physical_acceptance':float(np.mean(mask))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',type=int,nargs='+',default=[640,1536,4096])
    parser.add_argument('--power',type=int,default=15)
    parser.add_argument('--seeds',type=int,default=2)
    parser.add_argument('--max-count',type=int,default=9)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    result={'status':'uncertified coupled continuum diagnostic; no actual-prime estimate',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'omitted_count_tail':'UNBOUNDED in this experiment',
            'interpolation_checks':[],'rows':[],'summaries':[]}
    for n in args.orders:
        table, error=rectangle_table(n)
        result['interpolation_checks'].append({'N':n,'maximum_sampled_absolute_error':error})
        partial=[]
        for seed in range(args.seeds):
            rows=[trial(n,count,args.power,seed,table) for count in range(3,args.max_count+1)]
            result['rows'].extend(rows)
            partial.append({name:[sum(row[name]['real'] for row in rows),
                                  sum(row[name]['imag'] for row in rows)]
                            for name in ('pure_selected','joint_modes','old_share_modes','neighbors_modes')})
        summary={'N':n,'per_seed_partial_sums':partial}
        result['summaries'].append(summary)
        print(json.dumps(summary),flush=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()
