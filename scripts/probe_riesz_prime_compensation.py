#!/usr/bin/env python3
"""Optional diagnostics for the retained signed cutoff sum, not a certificate.

The first experiment measures the TWO-small-prime sign/magnitude criterion
in the existing ordinary-prime-density model. The second integrates the
radial exponential exactly up to an explicitly bounded endpoint-series
truncation, before Sobol integration over shares. Neither approximates the
actual prime sum by a proved theorem; the omitted count tail stays unpaid.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.special import gammainc, gammaln
from scipy.stats import qmc

from probe_riesz_label_anatomy import length
from probe_riesz_signed_cutoff import U, encode, marked_weights, profiles, shapes


def compensation_row(N, count, power, seed):
    T, xs, volume = shapes(N, count, power, seed)
    L = float(length(N))
    lam = L/T
    W, _ = marked_weights(N, xs, count)
    J, _, _, _, _, _ = profiles(xs, lam)
    valid = (volume > 0) & np.all(xs*T[:, None] < L, axis=1)
    radial = np.exp((N+1)*np.log(U)+N*np.log(T)-T/2-gammaln(N+1))
    base = volume*radial*W/(lam*np.prod(xs, axis=1))*valid
    mid = np.sort(xs[:, 1:-1], axis=1)
    r, a, D = xs[:, -1], mid[:, 0], lam-xs[:, 0]
    # Every composite divisor of the remaining b lies beyond D.
    certified = (r+a <= D) & (D <= mid[:, 1]+mid[:, 2])
    t = D[:, None]-mid[:, 1:]
    tent = (np.maximum(0, t)-np.maximum(0, t-r[:, None])
            -np.maximum(0, t-a[:, None])+np.maximum(0, t-r[:, None]-a[:, None]))
    full = -np.sum(tent, axis=1)
    plateau = np.sum((r[:, None] <= t) & (t <= a[:, None]), axis=1)
    error = float(np.max(np.abs(J[certified]-full[certified]), initial=0))
    assert error < 1e-11
    assert np.max(J[certified]+r[certified]*plateau[certified], initial=0) < 1e-11
    negative = base*np.maximum(-J, 0)
    return dict(N=N, count=count, seed=seed, samples=len(T),
        negative_mass=float(np.mean(negative)),
        certified_negative_mass=float(np.mean(negative*certified)),
        guaranteed_plateau_mass=float(np.mean(base*r*plateau*certified)),
        identity_error=error)


def radial_shapes(count, power, seed):
    """Shares independent of T, so the physical radial endpoints stay exact."""
    v = qmc.Sobol(count-1, scramble=True, seed=seed).random_base2(power)
    p = .5+.1*v[:, 0]
    width = np.maximum(np.minimum(.06, (1-p)/(count-1))-.005, 0)
    r = .005+width*v[:, 1]
    m = count-2
    cuts = np.sort(v[:, 2:], axis=1)
    gaps = np.diff(np.column_stack((np.zeros(len(p)), cuts, np.ones(len(p)))), axis=1)
    free = np.maximum(1-p-(m+1)*r, 0)
    xs = np.column_stack((p, r[:, None]+free[:, None]*gaps, r))
    # One simplex Jacobian and one symmetry factor; T is integrated below.
    volume = .1*width*free**(m-1)/math.factorial(m-1)/math.factorial(m)
    return xs, volume


def endpoint(N, degree, y, T, terms=24):
    """Normalized antiderivative for e^(-(1/2+iy)T)*T^degree.

    The exact series terminates after degree+1 terms. Here the omitted
    tail is bounded geometrically; roundoff is NOT interval-certified.
    """
    alpha = .5+1j*y
    ratio = degree/(abs(alpha)*T)
    assert np.max(ratio) < .1
    term = np.ones_like(T, dtype=complex)
    total = term.copy()
    for j in range(1, min(terms, degree+1)):
        term *= (degree-j+1)/(alpha*T)
        total += term
    amplitude = np.exp((N+1)*np.log(U)+degree*np.log(T)-T/2-gammaln(N+1))
    value = -amplitude*np.exp(-1j*y*T)*total/alpha
    bound = amplitude/abs(alpha)*ratio**terms/(1-ratio)
    return value, bound


def radial_moment(N, degree, y, lo, hi):
    """u^(N+1)/N! times the radial moment, with empty intervals zero."""
    hi = np.maximum(lo, hi)
    if y == 0:
        pref = np.exp((N+1)*np.log(U)+(degree+1)*np.log(2)
                      +gammaln(degree+1)-gammaln(N+1))
        return pref*(gammainc(degree+1, hi/2)-gammainc(degree+1, lo/2)), np.zeros_like(lo)
    left, err1 = endpoint(N, degree, y, lo)
    right, err2 = endpoint(N, degree, y, hi)
    return right-left, err1+err2


def clipped_moment(N, L, y, r, alpha, lo, hi):
    """Integral of the exact physical-log clip min(rT,(L-alpha*T)_+)."""
    cut1, cut2 = L/(alpha+r), L/alpha
    j1, e1 = radial_moment(N, N+1, y, lo, np.minimum(hi, cut1))
    midlo, midhi = np.maximum(lo, cut1), np.minimum(hi, cut2)
    j0, e0 = radial_moment(N, N, y, midlo, midhi)
    j2, e2 = radial_moment(N, N+1, y, midlo, midhi)
    value = (r*j1+j0*L-alpha*j2)/L
    return value, (r*e1+e0*L+alpha*e2)/L


def radial_row(N, count, power, seed, heights):
    xs, volume = radial_shapes(count, power, seed)
    L = float(length(N))
    W, _ = marked_weights(N, xs, count)
    p, r = xs[:, 0], xs[:, -1]
    lo = np.maximum(1.95*N, 2*np.log(N)/r)
    hi = np.minimum(2.03*N, L/p)
    valid = (hi > lo) & (volume > 0)
    weighted = volume*W/np.prod(xs, axis=1)*valid
    totals = {str(y): np.zeros(len(xs), dtype=complex) for y in heights}
    bounds = {str(y): np.zeros(len(xs)) for y in heights}
    for first in range(0, len(xs), 64):
        sl = slice(first, first+64)
        x = xs[sl]
        sums = x[:, :1].copy()
        signs = np.ones(1)
        for q in x[:, 1:-1].T:
            sums = np.concatenate((sums, sums+q[:, None]), axis=1)
            signs = np.concatenate((signs, -signs))
        # Terms with alpha*T>=L throughout the interval are identically zero.
        active = sums < (L/lo[sl])[:, None]
        rr, aa = np.broadcast_arrays(r[sl, None], sums)
        ll, hh = np.broadcast_arrays(lo[sl, None], hi[sl, None])
        ll, hh = np.broadcast_to(ll, sums.shape), np.broadcast_to(hh, sums.shape)
        for y in heights:
            val = np.zeros(sums.shape, dtype=complex)
            err = np.zeros(sums.shape)
            val[active], err[active] = clipped_moment(N, L, y,
                rr[active], aa[active], ll[active], hh[active])
            totals[str(y)][sl] = np.sum(val*signs, axis=1)
            bounds[str(y)][sl] = np.sum(err, axis=1)
    return dict(N=N, count=count, seed=seed, samples=len(xs),
        phases={str(y): encode(np.mean(weighted*totals[str(y)])) for y in heights},
        endpoint_truncation_bounds={str(y): float(np.mean(weighted*bounds[str(y)])) for y in heights},
        radial_absolute={str(y): float(np.mean(np.abs(weighted*totals[str(y)]))) for y in heights})


def validate_moments():
    """Independent high-precision incomplete-gamma checks across hinge breaks."""
    mp.mp.dps = 90
    checks = []
    for N in (256, 1024):
        L = float(length(N))
        for y in (0, 54, 100):
            for alpha, r in ((.64, .025), (.68, .025), (.73, .015)):
                lo, hi = 1.95*N, 2.03*N
                actual, trunc = clipped_moment(N, L, y, np.array([r]),
                    np.array([alpha]), np.array([lo]), np.array([hi]))
                c = mp.mpf('.5')+mp.j*y
                u = mp.mpf(10001)/20000
                pref = u**(N+1)/mp.factorial(N)
                def moment(k, a, b):
                    if b <= a:
                        return mp.mpc(0)
                    return pref*mp.gammainc(k+1, c*a, c*b)/c**(k+1)
                l, h = mp.mpf(lo), mp.mpf(hi)
                lam, aa, rr = mp.mpf(L), mp.mpf(alpha), mp.mpf(r)
                c1, c2 = lam/(aa+rr), lam/aa
                ref = (rr*moment(N+1,l,min(h,c1))+lam*moment(N,max(l,c1),min(h,c2))
                       -aa*moment(N+1,max(l,c1),min(h,c2)))/lam
                error = float(abs(complex(ref)-actual[0]))
                assert error < 5e-10, (N, y, alpha, error)
                checks.append(dict(N=N, y=y, alpha=alpha, r=r,
                                   absolute_error=error, series_tail_bound=float(trunc[0])))
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[256,512,1024])
    parser.add_argument('--power', type=int, default=11)
    parser.add_argument('--seeds', type=int, default=3)
    parser.add_argument('--max-count', type=int, default=14)
    parser.add_argument('--heights', type=int, nargs='+', default=[0,54,60,100])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert 5 <= args.max_count <= 16
    assert all(y == 0 or abs(y) >= 54 for y in args.heights)
    report = dict(scope='Ordinary-density diagnostics only; no signed prime-sum bound, floor or zero exclusion',
        target='lowerThresholdPacket(3..55)-shortOverflowPacket(3..13)',
        model='ordinary-prime density, not exposed-zero modes; no proved arithmetic transport',
        masks='moving floor length, core 1.95N..2.03N, N^2<p<exp(L), owner .5..6, least .005..06, all marked factorial slots',
        omitted_count_tail=f'{args.max_count+1}..55 UNBOUNDED',
        error_scope='Endpoint series tail bounded algebraically; floating point and Sobol error are not certified',
        hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
            [Path(__file__),Path(__file__).with_name('probe_riesz_signed_cutoff.py'),
             Path(__file__).with_name('probe_riesz_label_anatomy.py')]},
        validation=validate_moments(), compensation=[], radial=[], summaries=[])
    def save():
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    for N in args.orders:
        for scramble in range(args.seeds):
            rows = []
            for count in range(3,args.max_count+1):
                seed = 20261002+100*scramble+count
                row = radial_row(N,count,args.power,seed,args.heights)
                rows.append(row)
                report['radial'].append(row)
                if count >= 5:
                    report['compensation'].append(compensation_row(N,count,args.power,seed))
            summary = dict(N=N, scramble=scramble,
                phases={str(y):np.sum([row['phases'][str(y)] for row in rows],axis=0).tolist() for y in args.heights},
                endpoint_truncation_bound={str(y):sum(row['endpoint_truncation_bounds'][str(y)] for row in rows) for y in args.heights})
            report['summaries'].append(summary)
            print(json.dumps(summary), flush=True)
            save()
    save()


if __name__ == '__main__':
    main()
