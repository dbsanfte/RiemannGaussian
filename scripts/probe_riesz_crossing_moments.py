#!/usr/bin/env python3
"""Resolve clustered Riesz crossings by their signed variance moments.

Optional numerical research, outside builds/CI. The continuous owner model
retains the original moving cutoff, factorial kernel, allocation and phase.
It does NOT count actual primes or certify the native floor. A crossing is
never skipped: its exact second subset moment pays a Lipschitz remainder.
Logarithms, quadrature and numerical bounds are not interval certificates.
"""

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import subprocess
from functools import lru_cache

import mpmath as mp
import numpy as np
from scipy.stats import binom

from probe_riesz_structure_detector import (
    clusters, common_binary_scale, features, geometry, grouped_riesz, parameters, REFERENCE_OWNER)


def cardinality_layers(logs):
    """All subset ranks, retaining the exact multiplicity and variance.

    For q-subsets, mean=q*mean(logs) and Var=q(c-q)/(c(c-1))*sum deviations².
    The nonnegative Jensen hinge defect has integral choose(c,q)*Var/2.
    The signed Riesz response includes this defect with sign (-1)^q.
    """
    xs = sorted(map(mp.mpf, logs))
    c = len(xs)
    mean = mp.fsum(xs)/c
    scatter = mp.fsum((x-mean)**2 for x in xs)
    result = []
    for q in range(c+1):
        variance = mp.mpf(q*(c-q))*scatter/(c*(c-1)) if c > 1 else mp.mpf(0)
        result.append(dict(rank=q, sign=(-1)**q, multiplicity=math.comb(c,q),
                           mean=q*mean, minimum=mp.fsum(xs[:q]),
                           maximum=mp.fsum(xs[c-q:]) if q else mp.mpf(0),
                           variance=variance, area=math.comb(c,q)*variance/2))
    return result


def central_riesz(c, mean, cutoffs):
    """The joined response of equal logs, using exact binomial incidences."""
    ds = np.asarray(cutoffs,dtype=np.longdouble)
    a = np.longdouble(str(mean))
    q = np.clip(np.floor(ds/a).astype(int),0,c-1)
    first = np.asarray([(-1)**int(k)*math.comb(c-1,int(k)) for k in q],dtype=np.longdouble)
    second = np.asarray([(-1)**int(k)*math.comb(c-2,int(k)-1) if k else 0
                         for k in q],dtype=np.longdouble)
    answer = first*ds-second*(c*a)
    return np.where((ds <= 0)|(ds >= c*a),np.longdouble(0),answer)


@lru_cache(maxsize=32)
def quota_layers(logs):
    """Apply the same cancellation to EVERY cluster-quota layer.

    Means and variances add across disjoint clusters. No parity class or
    quota is omitted, including empty/full clusters and boundary subsets.
    """
    groups = clusters(logs,mp.fsum(logs)/1000)
    if len(groups) == 1:
        return cardinality_layers(logs),len(groups)
    options = [cardinality_layers(g) for g in groups]
    states = math.prod(len(g)+1 for g in groups)
    if states > 200000:
        raise ValueError(f'quota state space {states} exceeds explicit complete-layer budget')
    result = []
    for selected in itertools.product(*options):
        mult = math.prod(z['multiplicity'] for z in selected)
        variance = mp.fsum(z['variance'] for z in selected)
        result.append(dict(rank=sum(z['rank'] for z in selected),
            quotas=[z['rank'] for z in selected],sign=math.prod(z['sign'] for z in selected),
            multiplicity=mult,mean=mp.fsum(z['mean'] for z in selected),
            minimum=mp.fsum(z['minimum'] for z in selected),
            maximum=mp.fsum(z['maximum'] for z in selected),
            variance=variance,area=mult*variance/2))
    assert sum(z['multiplicity'] for z in result) == 2**len(logs)
    return result,len(groups)


def central_quota_riesz(layers,cutoffs):
    """All centered quotas joined by exact integer cumulative incidences."""
    integer_knots,scale = common_binary_scale([z['mean'] for z in layers])
    knots = {}
    for z,knot in zip(layers,integer_knots):
        knots[knot] = knots.get(knot,0)+z['sign']*z['multiplicity']
    integers = sorted(knots)
    count = moment = 0
    cs,ms = [],[]
    for knot in integers:
        count += knots[knot]
        moment += knot*knots[knot]
        cs.append(np.longdouble(str(count)))
        ms.append(np.longdouble(str(mp.ldexp(mp.mpf(moment),scale))))
    values = np.asarray([np.longdouble(str(mp.ldexp(mp.mpf(k),scale))) for k in integers])
    ds = np.asarray(cutoffs,dtype=np.longdouble)
    indices = np.searchsorted(values,ds,side='left')-1
    safe = np.maximum(indices,0)
    result = ds*np.asarray(cs)[safe]-np.asarray(ms)[safe]
    return np.where(indices < 0,np.longdouble(0),result)


def weights(pars, base, totals, height, kind):
    """Original allocation and radial/phase weights, no countwise rescaling."""
    n, length = pars['N'], float(pars['length'])
    xs = np.asarray([float(x) for x in base])
    total = np.asarray(totals,dtype=float)
    A = float(mp.fsum(base))
    owner = total-A
    logs = np.column_stack((owner,np.tile(xs,(len(total),1))))
    orders = pars['orders']
    qs = np.clip(1-logs/total[:,None],0.,1.)
    eligible = (logs > 2*math.log(n))&(logs < length)
    theta = np.sum(eligible*(binom.cdf(int(orders[-1]),n+1,qs)
                           -binom.cdf(int(orders[0])-1,n+1,qs)),axis=1)
    assert np.min(theta) >= -1e-9 and np.max(theta) <= 1+1e-9
    radial = np.exp(-(total-2*n)/2+n*np.log(total/(2*n)))
    density_constant = math.exp(2*n*(1-REFERENCE_OWNER[kind])-A)
    positive = total/length/owner*radial*(1-theta)*density_constant
    return positive*np.cos(height*total)


def weight_bounds(pars, base, height, kind, lower, upper):
    """Analytic crude sup and Lipschitz bounds for the retained weight.

    This branch requires constant eligibility and literal model masks on
    the interval. Each binomial CDF derivative costs at most N+1; both
    endpoints and ALL eligible legs are retained in theta's derivative.
    """
    n, length = pars['N'], float(pars['length'])
    A = float(mp.fsum(base))
    minimum_owner = lower-A
    assert minimum_owner > max(map(float,base))
    assert 2*math.log(n) < minimum_owner <= upper-A < length
    for total in (lower+1e-7,(lower+upper)/2,upper):
        assert features([mp.mpf(total)-mp.fsum(base),*base],pars)['modelCoreAdmissible']
    constant = math.exp(2*n*(1-REFERENCE_OWNER[kind])-A)
    sup = upper/length/minimum_owner*constant  # radial<=1, 0<=1-theta<=1
    radial_log_derivative = max(abs(n/lower-.5),abs(n/upper-.5))
    theta_derivative = 4*(n+1)*A/lower**2
    derivative = sup*(abs(height)+1/lower+1/minimum_owner+
                      radial_log_derivative+theta_derivative)
    return sup, derivative


def probe(order, radius, count, kind, height, seed, nodes, cofactor_shift=0.):
    pars = parameters(order,radius)
    full = geometry(count,kind,2*order,random.Random(seed))
    full.remove(max(full))
    if cofactor_shift:
        # Preserve each cluster's internal deviations EXACTLY in real space.
        # Total cofactor log moves; the actual owner remains T-log(cofactor).
        step = mp.mpf(str(cofactor_shift))/len(full)
        full = [x+step for x in full]
    base, c = full, count-1
    A, length = mp.fsum(base), pars['length']
    assert A < length  # second hinge is EXACTLY an affine null
    lower, upper = 1.95*order, 2.03*order
    layers,cluster_count = quota_layers(tuple(base))
    sup, lip = weight_bounds(pars,base,height,kind,lower,upper)
    unit = 2*math.pi/height
    edges = [lower]+[k*unit for k in range(math.floor(lower/unit)+1,
                                         math.ceil(upper/unit))]+[upper]
    # Split every phase period at each CENTRAL hinge; no uncomputed nodes.
    centers = [float(length+A-z['mean']) for z in layers]
    points = sorted(set(edges+[v for v in centers if lower < v < upper]))
    gx, gw = np.polynomial.legendre.leggauss(nodes)
    left, right = np.asarray(points[:-1]),np.asarray(points[1:])
    ts = ((left+right)[:,None]/2+(right-left)[:,None]*gx/2).ravel()
    ds = float(length+A)-ts
    central = central_riesz(c,A/c,ds) if cluster_count == 1 else central_quota_riesz(layers,ds)
    phase_weight = weights(pars,base,ts,height,kind)
    scales = ((right-left)[:,None]/2*gw).ravel()
    central_integral = np.sum(central*phase_weight*scales,dtype=np.longdouble)
    absolute = np.sum(np.abs(central*phase_weight)*scales,dtype=np.longdouble)
    signed_moment, remainder, direct_width = mp.mpf(0),mp.mpf(0),mp.mpf(0)
    crossing_records = []
    for z in layers:
        if z['area'] == 0:
            continue
        center = length+A-z['mean']
        lo, hi = length+A-z['maximum'],length+A-z['minimum']
        if hi <= lower or upper <= lo:
            continue
        inside = lower <= lo and hi <= upper
        width = max(center-lo,hi-center)
        value = mp.mpf(float(weights(pars,base,[float(center)],height,kind)[0])) if inside else mp.mpf(0)
        signed_moment += z['sign']*z['area']*value
        err = mp.mpf(lip)*width*z['area'] if inside else mp.mpf(sup)*z['area']
        remainder += err
        # Previous unsigned width cost for this layer, same sup norm.
        old = mp.mpf(sup)*z['multiplicity']*(hi-lo)**2
        direct_width += old
        crossing_records.append(dict(rank=z['rank'],quotas=z.get('quotas'),multiplicity=z['multiplicity'],
            center=float(center),interval=[float(lo),float(hi)],
            signedVarianceCorrection=float(z['sign']*z['area']*value),
            lipschitzRemainder=float(err),completeLayerInsideCore=bool(inside)))
    joined = mp.mpf(str(central_integral))+signed_moment
    return dict(N=order,radius=radius,count=count,geometry=kind,height=height,
        seed=seed,nodes=nodes,cofactorLogShift=cofactor_shift,
        periods=len(edges)-1,centralSubintervals=len(points)-1,
        unresolvedNodes=0,centralModelReal=float(central_integral),
        joinedSignedVarianceCorrection=float(signed_moment),
        modelJoinedReal=float(joined),modelRealBounds=[float(joined-remainder),float(joined+remainder)],
        analyticCrossingRemainder=float(remainder),
        centralModelAbsoluteIntegral=float(absolute),
        remainderRelativeToAbsolute=float(remainder/abs(mp.mpf(str(absolute)))) if absolute else 0.,
        improvementOverUnsignedWidthAllowance=float(direct_width/remainder) if remainder else None,
        crossingLayers=crossing_records,clusterCount=cluster_count,quotaLayers=len(layers),
        representedCofactorSubsets=sum(z['multiplicity'] for z in layers),
        exactMultiplicityAndSubsetVariance=True,
        originalFactorialAllocationPhaseAndModelMasksRetained=True,
        sourceNormalized=False,primePopulationTransport=False,
        quadratureOrTranscendentalIntervalCertified=False,nativeFloorCredit=False)


def self_test():
    maximum = mp.mpf(0)
    cases = 0
    for c in range(2,10):
        xs = [mp.mpf(3*i+7)/11 for i in range(c)]
        for z in cardinality_layers(xs):
            values = [mp.fsum(s) for s in itertools.combinations(xs,z['rank'])]
            mean, lo, hi = z['mean'], z['minimum'], z['maximum']
            # Exact primitive at the two support endpoints.
            area = mp.fsum((hi-v)**2/2 for v in values)-len(values)*(hi-mean)**2/2
            maximum = max(maximum,abs(area-z['area']))
            assert abs(area-z['area']) < mp.mpf('1e-85')
            for point in (lo-1,lo,(lo+hi)/2,hi,hi+1):
                gap = mp.fsum(max(point-v,0) for v in values)-len(values)*max(point-mean,0)
                assert gap >= -mp.mpf('1e-85')
                if point <= lo or hi <= point:
                    assert abs(gap) < mp.mpf('1e-85')
            cases += 1
        for D in (mp.mpf('0.3'),mp.mpf('1.8'),mp.mpf('4.1')):
            joined = mp.fsum(z['sign']*mp.fsum(max(D-mp.fsum(s),0)
                             for s in itertools.combinations(xs,z['rank'])) for z in cardinality_layers(xs))
            truth = grouped_riesz(xs,D).value
            assert abs(joined-truth) < mp.mpf('1e-85')
    xs = tuple(map(mp.mpf,['1.01','1.010001','3.2','3.200003','7.1']))
    layers,groups = quota_layers(xs)
    assert groups == 3 and sum(z['multiplicity'] for z in layers) == 2**len(xs)
    for D in (mp.mpf('0.1'),mp.mpf('4.21'),mp.mpf('8.11'),mp.mpf('15.6')):
        truth = grouped_riesz(xs,D).value
        mean_response = central_quota_riesz(layers,[float(D)])[0]
        # Compare the centered quota evaluator against explicit centered factors.
        centered = []
        for g in clusters(xs,mp.fsum(xs)/1000):
            centered.extend([mp.fsum(g)/len(g)]*len(g))
        direct = grouped_riesz(centered,D).value
        assert abs(float(mean_response)-float(direct)) < 1e-12
        assert truth is not None
    return dict(passed=True,enumeratedLayerCases=cases,clusterQuotaRegression=True,
                maximumAreaResidual=float(maximum))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test',action='store_true')
    ap.add_argument('--orders',nargs='+',type=int,default=[3584])
    ap.add_argument('--counts',nargs='+',type=int,default=[20,40,55,56,63])
    ap.add_argument('--geometries',nargs='+',default=['owner_rectangle'],
                    choices=['owner_rectangle','two_reflected','small_cluster','two_clusters','multiscale'])
    ap.add_argument('--heights',nargs='+',type=float,default=[54,65,100])
    ap.add_argument('--nodes',nargs='+',type=int,default=[16,32])
    ap.add_argument('--seeds',nargs='+',type=int,default=[317,919])
    ap.add_argument('--output',type=Path,default=Path('.lake/riesz-crossing-moment/probe.json'))
    args = ap.parse_args()
    mp.mp.dps = 100
    if args.self_test:
        print(json.dumps(self_test(),indent=2))
        return
    rows = [probe(n,.50005,c,kind,y,seed,nodes)
            for n in args.orders for c in args.counts if c < parameters(n,.50005)['ceiling']
            for kind in args.geometries
            for y in args.heights for seed in args.seeds for nodes in args.nodes]
    report = dict(schemaVersion=1,head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        sourceSha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        kind='signed-cardinality-crossing-moment-model',selfTest=self_test(),rows=rows,
        nativeFloorProved=False,scope='Continuous fixed-cofactor owner models only; no prime population, cofinal or interval certificate.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2))
    print(json.dumps(dict(cases=len(rows),maximumRemainderRelativeToAbsolute=max(z['remainderRelativeToAbsolute'] for z in rows),
                         output=str(args.output),nativeFloorProved=False),indent=2))


if __name__ == '__main__':
    main()
