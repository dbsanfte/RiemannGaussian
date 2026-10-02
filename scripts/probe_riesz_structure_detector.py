#!/usr/bin/env python3
"""Optional signed structure search over the current Riesz floor geometry.

This is a research detector, NOT a floor certificate or a prime-count theorem.
Two separate backends are available: a broad continuous-log geometry scan,
and a regression on constructed actual (probable-)prime labels. The latter
keeps the original core masks; the former does not pretend to count primes.
Exact integer combinatorics collapse complete cardinality layers BEFORE
evaluation. Unresolved hinge layers have explicit interval bounds and are
reported rather than sampled or silently assigned a sign. All periods/counts
are joined before the diagnostic adverse cost. No cost is a native budget.

Run from formal/, e.g. ../.venv/bin/python scripts/probe_riesz_structure_detector.py
--self-test, then --orders 256 640 1536 3584 --output .lake/riesz-structure-detector/scan.json.
The optional --prime-regressions mode can take longer. Nothing runs in CI.
"""

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import subprocess
import time

import mpmath as mp
import numpy as np
from scipy.stats import binom

from probe_riesz_canonical_joint import core_mask
from probe_riesz_fixed_count_period import unpaid_orders


NATIVE = {256: 8, 640: 16, 1536: 32, 3584: 64, 8192: 128}
GEOMETRIES = ('balanced', 'owner_rectangle', 'two_reflected', 'three_reflected',
              'small_cluster', 'two_clusters', 'scale_spread', 'multiscale')
RADII = (0.5, 0.500025, 0.50005)
REFERENCE_OWNER = dict(balanced=1/3, owner_rectangle=.55, two_reflected=.44,
                       three_reflected=.34, small_cluster=.56, two_clusters=.54,
                       scale_spread=.545, multiscale=.555)


@dataclass
class LayerResult:
    value: object
    lower: object
    upper: object
    layers: int
    collapsed_subsets: int
    enumerated_subsets: int
    unresolved_subsets: int
    cutoff_prefix: int | None
    method: str = 'grouped_cardinality'
    whole_layer: int | None = None


@lru_cache(maxsize=None)
def parameters(order, radius):
    rational = {0.5: (1, 2), 0.500025: (20001, 40000),
                0.50005: (10001, 20000)}[radius]
    a, b = rational
    cutoff = b**order // (a**order * (order+1))
    physical = (cutoff+2)**2
    length = mp.log(physical)
    tilt = 1/(-2*mp.log(mp.mpf(a)/b))
    rate = (2-2*tilt)*mp.log(mp.mpf(a)/b)-mp.log(tilt)
    trial = min(int(mp.exp(-order*rate/(2*(tilt+mp.mpf('2.5'))))), cutoff+1)
    orders = unpaid_orders(order)
    assert len(orders) and np.all(np.diff(orders) == 1)
    return dict(N=order, radius=radius, physical=physical, length=length,
                trial=trial, orders=orders, ceiling=NATIVE[order])


def clusters(logs, width):
    """Disjoint consecutive clusters; leaves remain distinct, not repeated modes."""
    groups = []
    for x in sorted(logs):
        if not groups or x-groups[-1][0] > width:
            groups.append([x])
        else:
            groups[-1].append(x)
    return groups


def common_binary_scale(values):
    """Exact common integer scale for the finite MP input values."""
    raw=[x._mpf_ for x in values]
    exponent=min(t[2] for t in raw if t[1])
    integers=[(-1 if s else 1)*(m << (e-exponent)) if m else 0 for s,m,e,_ in raw]
    return integers,exponent


def grouped_riesz(logs, cutoff, *, width=None, leaf_budget=20000,
                  layer_budget=200000, subset_budget=262144, primes=None, integer_cutoff=None):
    """Evaluate the literal signed subset hinge, with certified combinatorics.

    A complete layer has C(m,k) subsets and each cluster member occurs in
    C(m-1,k-1) of them. Collapse these counts as INTEGERS; only then evaluate
    the resulting linear combination of logarithms. For actual primes all
    hinge membership tests compare INTEGER products with the integer cutoff.
    Floating/MP logarithms are not interval certificates.
    """
    logs = list(map(mp.mpf, logs))
    cutoff = mp.mpf(cutoff)
    if not logs or any(x <= 0 for x in logs):
        raise ValueError('at least one strictly positive factor log is required')
    if (primes is None) != (integer_cutoff is None):
        raise ValueError('supply both primes and integer_cutoff, or neither')
    if primes is not None and (len(primes) != len(logs) or len(set(primes)) != len(primes)
                               or integer_cutoff < 1):
        raise ValueError('actual labels need distinct factors, matching lengths and positive cutoff')
    if cutoff <= 0:
        return LayerResult(mp.mpf(0),mp.mpf(0),mp.mpf(0),1,2**len(logs),0,0,0,'empty_support')
    ordered = sorted(logs)
    if len(logs) >= 2:
        all_inside = (math.prod(primes) < integer_cutoff) if primes else mp.fsum(logs) < cutoff
        if all_inside:
            return LayerResult(mp.mpf(0),mp.mpf(0),mp.mpf(0),1,2**len(logs),0,0,0,'affine_null')
        # A quota between complete cardinality layers gives an exact closed
        # affine response. This is a detector feature, not a phase estimate.
        sorted_primes = sorted(primes) if primes is not None else None
        for q in range(len(logs)):
            lo = mp.fsum(ordered[len(logs)-q:]) if q else mp.mpf(0)
            hi = mp.fsum(ordered[:q+1])
            separated = (math.prod(sorted_primes[len(logs)-q:] if q else []) < integer_cutoff
                         <= math.prod(sorted_primes[:q+1])) if primes else lo < cutoff <= hi
            if separated:
                sign = (-1)**q
                a = sign*math.comb(len(logs)-1,q)
                b = sign*math.comb(len(logs)-2,q-1) if q else 0
                value = a*cutoff-b*mp.fsum(logs)
                return LayerResult(value,value,value,len(logs)+1,2**len(logs),0,0,a,'whole_layer',q)
    if 2**len(logs) <= subset_budget:
        # MP numbers have finite binary representations. Align these as
        # integers, so even near-hinge classification retains every bit of
        # the INPUT. Prime regressions instead use integer divisor products.
        # Neither operation certifies transcendental log-rounding error.
        if primes is not None:
            sums=[1]
            for p in primes:
                sums += [v*p for v in sums]
            included=np.asarray([v < integer_cutoff for v in sums])
        else:
            integers,_=common_binary_scale([*logs,cutoff])
            sums=[0]
            for x in integers[:-1]:
                sums += [v+x for v in sums]
            included=np.asarray([v < integers[-1] for v in sums])
        signs=np.asarray([1],dtype=np.int8)
        for _ in logs:
            signs=np.concatenate((signs,-signs))
        signed=signs*included
        a=int(signed.sum(dtype=np.int64))
        b=[int(signed.reshape(-1,2**(i+1))[:,2**i:].sum(dtype=np.int64)) for i in range(len(logs))]
        value=a*cutoff-mp.fsum(v*x for v,x in zip(b,logs))
        return LayerResult(value,value,value,2**len(logs),0,2**len(logs),0,a,'finite_subsets')
    if primes is not None:
        pairs = sorted(zip(logs, primes))
        if len(pairs) != len(logs) or len(set(primes)) != len(primes):
            raise ValueError('actual labels require distinct factors')
        grouped = []
        width = width if width is not None else mp.fsum(logs)/1000
        for x, p in pairs:
            if not grouped or x-grouped[-1][0][0] > width:
                grouped.append([(x, p)])
            else:
                grouped[-1].append((x, p))
        groups = [[x for x, _ in g] for g in grouped]
        pgroups = [[p for _, p in g] for g in grouped]
    else:
        width = width if width is not None else mp.fsum(logs)/1000
        groups = clusters(logs, width)
        pgroups = None
    layer_count = math.prod(len(g)+1 for g in groups)
    if layer_count > layer_budget:
        # No false sign: the general finite-difference Lipschitz majorant.
        bound = mp.mpf(2)**(len(logs)-1)*min(logs)
        return LayerResult(None, -bound, bound, layer_count, 0, 0,
                           2**len(logs), None)
    options = []
    integers,exponent=common_binary_scale([*logs,cutoff])
    integer_logs=dict(zip(logs,integers[:-1]))
    cutoff_integer=integers[-1]
    igroups=[[integer_logs[x] for x in g] for g in groups]
    for ig, g in enumerate(groups):
        opts = []
        for k in range(len(g)+1):
            opts.append((k, math.comb(len(g), k), sum(igroups[ig][:k]),
                         sum(igroups[ig][len(g)-k:]) if k else 0,
                         math.prod(pgroups[ig][:k]) if pgroups else None,
                         math.prod(pgroups[ig][len(g)-k:]) if pgroups and k else 1))
        options.append(opts)
    # A*cutoff - sum B_i*sum(cluster logs), all A/B_i exact integers.
    a, b = 0, [0]*len(groups)
    literal_sum=lower_sum=upper_sum=0
    collapsed = enumerated = unresolved = prefix = 0
    for choices in itertools.product(*options):
        count = math.prod(c[1] for c in choices)
        sign = -1 if sum(c[0] for c in choices) % 2 else 1
        lo, hi = sum(c[2] for c in choices), sum(c[3] for c in choices)
        if pgroups:
            lower_product, upper_product = math.prod(c[4] for c in choices), math.prod(c[5] for c in choices)
            inside, outside = upper_product < integer_cutoff, lower_product >= integer_cutoff
        else:
            inside, outside = hi < cutoff_integer, lo >= cutoff_integer
        if inside:
            collapsed += count
            prefix += sign*count
            a += sign*count
            for ig, c in enumerate(choices):
                # This ratio is an integer by elementary incidence counting.
                assert count*c[0] % len(groups[ig]) == 0
                b[ig] += sign*(count*c[0]//len(groups[ig]))
        elif outside:
            collapsed += count
        elif enumerated+count <= leaf_budget:
            enumerated += count
            selected_groups = [list(itertools.combinations(range(len(g)), c[0]))
                               for g, c in zip(groups, choices)]
            for selected in itertools.product(*selected_groups):
                x = sum(igroups[i][j] for i, indices in enumerate(selected) for j in indices)
                included = (math.prod(pgroups[i][j] for i, indices in enumerate(selected) for j in indices)
                            < integer_cutoff) if pgroups else x < cutoff_integer
                if included:
                    prefix += sign
                    literal_sum += sign*(cutoff_integer-x)
        else:
            unresolved += count
            low = count*max(cutoff_integer-hi, 0)
            high = count*max(cutoff_integer-lo, 0)
            lower_sum += low if sign > 0 else -high
            upper_sum += high if sign > 0 else -low
    exact_integer=a*cutoff_integer-sum(v*sum(g) for v,g in zip(b,igroups))+literal_sum
    exact=mp.ldexp(mp.mpf(exact_integer),exponent)
    lower=mp.ldexp(mp.mpf(exact_integer+lower_sum),exponent)
    upper=mp.ldexp(mp.mpf(exact_integer+upper_sum),exponent)
    assert collapsed+enumerated+unresolved == 2**len(logs)
    assert lower <= upper
    return LayerResult(exact if not unresolved else None, lower, upper,
                       layer_count, collapsed, enumerated, unresolved,
                       prefix if not unresolved else None)


def direct_riesz(logs, cutoff):
    return mp.fsum((-1)**len(s)*max(cutoff-mp.fsum(s), 0)
                   for k in range(len(logs)+1) for s in itertools.combinations(logs, k))


def geometry(count, kind, total, rng):
    """Log geometries; zero stochastic density or population claims."""
    if kind == 'balanced':
        shares = [1/count]*count
    elif kind == 'owner_rectangle':
        shares = [.55]+[.45/(count-1)]*(count-1)
    elif kind == 'two_reflected':
        shares = [.44, .36]+[.20/(count-2)]*(count-2)
    elif kind == 'three_reflected':
        if count == 3:
            shares = [.34, .33, .33]
        else:
            shares = [.325, .32, .315]+[.04/(count-3)]*(count-3)
    elif kind == 'small_cluster':
        shares = [.56, .40]+[.04/(count-2)]*(count-2)
    elif kind == 'two_clusters':
        a = max(1, (count-1)//2)
        shares = [.54]+[.30/a]*a+[.16/(count-1-a)]*(count-1-a)
    elif kind == 'scale_spread':
        raw = [2**(-6*i/max(1, count-2)) for i in range(count-1)]
        shares = [.545]+[.455*x/sum(raw) for x in raw]
    elif kind == 'multiscale':
        raw = [2**(-(i % 4)) for i in range(count-1)]
        shares = [.555]+[.445*x/sum(raw) for x in raw]
    else:
        raise ValueError(kind)
    # Distinct logs with deterministic small within-cluster perturbations.
    shares = [x*(1+rng.uniform(-2e-6, 2e-6)) for x in shares]
    return [mp.mpf(str(total*x/sum(shares))) for x in shares]


def allocation(order, orders, logs, total, length):
    xs = np.asarray([float(x) for x in logs])
    qs = np.clip(1-xs/float(total), 0., 1.)
    # The exact unpaidOrders set is contiguous; retain every order.
    values = binom.cdf(int(orders[-1]), order+1, qs)-binom.cdf(int(orders[0])-1, order+1, qs)
    weights = np.where((2*math.log(order) < xs) & (xs < float(length)),
                       np.maximum(values, 0.), 0.).tolist()
    assigned = math.fsum(weights)
    assert -1e-10 <= assigned <= 1+1e-8
    return assigned, weights


def features(logs, pars):
    total, length, n = mp.fsum(logs), pars['length'], pars['N']
    descending = sorted(logs, reverse=True)
    assigned, pieces = allocation(n, pars['orders'], logs, total, length)
    rough = [x for x in logs if x > 2*mp.log(n)]
    smooth_mass = mp.fsum(x for x in logs if x <= 2*mp.log(n))
    # Bins in log(p), not bins of p and not phase-period bins.
    bins = {int(mp.floor(mp.log(x, 2))) for x in logs}
    admissible = (mp.mpf('1.95')*n < total <= mp.mpf('2.03')*n
                  and length < total < 2*length
                  and max(logs) < length and len(rough) >= 2
                  and smooth_mass < length and max(logs) < mp.mpf('0.65')*total
                  and min(total-x for x in logs) > mp.log(pars['trial'])
                  and 3 <= len(logs) < pars['ceiling'])
    return dict(count=len(logs), parity=(-1)**len(logs), totalLogOverN=float(total/n),
                largestShare=float(descending[0]/total), secondShare=float(descending[1]/total),
                leastShare=float(descending[-1]/total), reflectedLargeCount=sum(x >= total-length for x in logs),
                roughCount=len(rough), smoothLogShare=float(smooth_mass/total),
                occupiedLogBins=len(bins), logBins=sorted(bins),
                originalAllocatedFraction=assigned, ownerAllocatedFraction=pieces[logs.index(max(logs))],
                modelCoreAdmissible=bool(admissible))


def serial_result(result):
    return dict(value=float(result.value) if result.value is not None else None,
                lower=float(result.lower), upper=float(result.upper), layers=result.layers,
                collapsedSubsets=result.collapsed_subsets, enumeratedSubsets=result.enumerated_subsets,
                unresolvedSubsets=result.unresolved_subsets, exactCombinatorialCoverage=result.value is not None,
                strictCutoffPrefix=result.cutoff_prefix,method=result.method,
                wholeLayerIndex=result.whole_layer)


def row(order, radius, count, kind, tau, seed, budget):
    pars = parameters(order, radius)
    logs = geometry(count, kind, tau*order, random.Random(seed))
    f = features(logs, pars)
    r = grouped_riesz(logs, pars['length'], leaf_budget=budget)
    total = mp.fsum(logs)
    # Relative radial saddle kernel. This is a smooth prime-density MODEL,
    # not the weight/multiplicity of any sampled actual prime population.
    radial = math.exp(-float(total)/2+order+order*math.log(float(total)/(2*order)))
    raw = -float(total)/float(pars['length'])*(1-f['originalAllocatedFraction'])*radial
    coefficient = raw*float(r.value) if r.value is not None else None
    return dict(N=order, radius=radius, geometry=kind, seed=seed, **f,
                response=serial_result(r), modelRadialSignedKernel=coefficient,
                modelRadialAbsoluteKernel=abs(coefficient) if coefficient is not None else None,
                logFactors=[float(x) for x in sorted(logs)],
                primePopulationWeightIncluded=False, intervalArithmetic=False)


def period_probe(order, radius, count, kind, height, seed, budget, nodes):
    """Freeze all cofactor logs; vary owner over complete literal core periods.

    Only the owner is a continuous prime-density model. All arithmetic Riesz
    signs, moving length, factorial radial shape and allocation stay joined.
    Different frozen cofactors are NOT put on a shared density measure.
    """
    pars = parameters(order, radius)
    base = geometry(count, kind, 2*order, random.Random(seed))
    base.remove(max(base))
    cofactor = mp.fsum(base)
    cofactor_scale = math.exp(2*order*(1-REFERENCE_OWNER[kind])-float(cofactor))
    lo, hi = 1.95*order, 2.03*order
    unit = 2*math.pi/height
    boundaries = [lo]+[k*unit for k in range(math.floor(lo/unit)+1, math.ceil(hi/unit))]+[hi]
    gx, gw = np.polynomial.legendre.leggauss(nodes)
    if count <= 12 or max(base)-min(base) < mp.fsum(base)/1000:
        return vector_period_probe(pars, base, boundaries, height, seed, kind, gx, gw)
    blocks, absolute = [], 0.
    unresolved = excluded = evaluations = 0
    for left, right in zip(boundaries, boundaries[1:]):
        value = price = 0.
        for x, w in zip(gx, gw):
            total = (left+right)/2+(right-left)*x/2
            owner = mp.mpf(total)-cofactor
            evaluations += 1
            if owner <= max(base):
                excluded += 1
                continue
            logs = [owner, *base]
            f = features(logs, pars)
            if not f['modelCoreAdmissible']:
                excluded += 1
                continue
            # Exact two-hinge prime deletion; owner cutoff varies with T.
            first = grouped_riesz(base, pars['length']-owner, leaf_budget=budget)
            second = grouped_riesz(base, pars['length'], leaf_budget=budget)
            if first.value is None or second.value is None:
                unresolved += 1
                continue
            response = first.value-second.value  # = -R_L(p*a)
            radial = math.exp(-(total-2*order)/2+order*math.log(total/(2*order)))
            scalar = (total/float(pars['length'])*radial*float(response)*cofactor_scale
                      *(1-f['originalAllocatedFraction'])/float(owner))
            signed = scalar*math.cos(height*total)
            scale = (right-left)*w/2
            value += signed*scale
            price += abs(signed)*scale
        blocks.append(value)
        absolute += price
    joined = math.fsum(blocks)
    adverse = math.fsum(max(-v, 0.) for v in blocks)
    return dict(N=order, radius=radius, count=count, geometry=kind, seed=seed,
                height=height, nodes=nodes, periods=len(blocks), evaluations=evaluations,
                excludedNodes=excluded, unresolvedNodes=unresolved,
                modelJoinedReal=joined, modelPeriodAdverseCost=adverse,
                modelPointwiseAbsoluteCost=absolute,
                modelPeriodCancellationFraction=1-adverse/absolute if absolute else None,
                modelSignedOverAbsolute=joined/absolute if absolute else None,
                periodSignedContributions=blocks,
                completeComputedModel=unresolved == 0,
                radialIntegrationFrozen=False, sourceNormalized=False,
                fullFactorialTotalLogFactorRetained=True,
                cofactorDensityConstantRetained=True,
                commonReferenceOwner=REFERENCE_OWNER[kind],
                allPeriodsJoinedBeforeClipping=True, primeCountOrMaskTransportProved=False)


def vector_period_probe(pars, base, boundaries, height, seed, kind, gx, gw):
    """Same two hinges and every subset; batch finite low-count arithmetic."""
    n, length = pars['N'], float(pars['length'])
    cofactor_scale = math.exp(2*n*(1-REFERENCE_OWNER[kind])-float(mp.fsum(base)))
    left, right = np.asarray(boundaries[:-1]), np.asarray(boundaries[1:])
    totals = ((left+right)[:,None]/2+(right-left)[:,None]*gx/2).ravel()
    owner = totals-float(mp.fsum(base))
    logs = np.column_stack((owner, np.tile(np.asarray([float(x) for x in base]), (len(totals),1))))
    if len(base) <= 11:
        divisor_logs, signs = [0.], [1.]
        for x in base:
            divisor_logs += [v+float(x) for v in list(divisor_logs)]
            signs += [-s for s in list(signs)]
        d, mu = np.asarray(divisor_logs), np.asarray(signs)
        # fsum each atom: no count clipping or termwise phase costs here.
        first = np.asarray([math.fsum(mu*np.maximum(length-x-d, 0.)) for x in owner])
        second = math.fsum(mu*np.maximum(length-d, 0.))
        valid = np.ones(len(totals),dtype=bool)
        validation_error = 0.
    else:
        first,valid = whole_layer_batch(base,length-owner)
        second_result = grouped_riesz(base,pars['length'])
        second = float(second_result.value) if second_result.value is not None else 0.
        if second_result.value is None:
            valid[:] = False
        check_indices = np.linspace(0,len(totals)-1,min(len(totals),80),dtype=int)
        errors = []
        for i in check_indices:
            if valid[i]:
                truth = grouped_riesz(base,mp.mpf(length)-mp.mpf(owner[i]))
                assert truth.value is not None
                errors.append(abs(first[i]-float(truth.value))/max(abs(float(truth.value)),1.))
        validation_error = max(errors,default=0.)
    orders = pars['orders']
    qs = np.clip(1-logs/totals[:,None],0.,1.)
    eligible = (2*math.log(n) < logs)&(logs < length)
    assigned = np.sum(eligible*(binom.cdf(int(orders[-1]),n+1,qs)
                                  -binom.cdf(int(orders[0])-1,n+1,qs)),axis=1)
    assert np.max(assigned) <= 1+1e-8 and np.min(assigned) >= -1e-8
    rough = logs > 2*math.log(n)
    admissible = ((owner > max(map(float,base))) & (length < totals)&(totals < 2*length)
                  & (np.max(logs,axis=1) < length)&(np.sum(rough,axis=1) >= 2)
                  & (np.sum(np.where(rough,0.,logs),axis=1) < length)
                  & (np.max(logs,axis=1) < .65*totals)
                  & (np.min(totals[:,None]-logs,axis=1) > float(mp.log(pars['trial']))))
    radial = np.exp(-(totals-2*n)/2+n*np.log(totals/(2*n)))
    safe_owner = np.where(owner > 0, owner, 1.)
    scalar = totals/length*radial*(first-second)*(1-assigned)*cofactor_scale/safe_owner
    scalar = np.where(admissible & valid, scalar, 0.)
    signed = scalar*np.cos(height*totals)
    scales = (right-left)[:,None]/2*gw
    blocks = (signed.reshape(len(left),len(gx))*scales).sum(axis=1)
    absolute = float((np.abs(signed).reshape(len(left),len(gx))*scales).sum())
    joined, adverse = math.fsum(blocks), math.fsum(np.maximum(-blocks,0.))
    return dict(N=n,radius=pars['radius'],count=len(base)+1,geometry=kind,seed=seed,
                height=height,nodes=len(gx),periods=len(blocks),evaluations=len(totals),
                excludedNodes=int((~admissible).sum()),unresolvedNodes=int((admissible & ~valid).sum()),
                modelJoinedReal=joined,modelPeriodAdverseCost=adverse,
                modelPointwiseAbsoluteCost=absolute,
                modelPeriodCancellationFraction=1-adverse/absolute if absolute else None,
                modelSignedOverAbsolute=joined/absolute if absolute else None,
                periodSignedContributions=blocks.tolist(),completeComputedModel=bool(np.all(valid | ~admissible)),
                radialIntegrationFrozen=False,sourceNormalized=False,
                fullFactorialTotalLogFactorRetained=True,
                cofactorDensityConstantRetained=True,
                commonReferenceOwner=REFERENCE_OWNER[kind],
                finiteSubsetOrWholeLayerEvaluationBatched=True,
                maximumHighCountPointCheckRelativeError=validation_error,
                allPeriodsJoinedBeforeClipping=True,primeCountOrMaskTransportProved=False)


def whole_layer_batch(logs, cutoffs):
    """Fast numerical version of the exact separated-layer formula.

    Nodes in a genuinely partial cardinality layer stay UNRESOLVED. The
    floating batching is regressed against MP evaluation in period_probe;
    it is neither an interval enclosure nor a coefficient-sign certificate.
    """
    xs = np.sort(np.asarray([float(x) for x in logs],dtype=np.longdouble))
    c = len(xs)
    minima = np.r_[np.longdouble(0),np.cumsum(xs)]
    maxima = np.r_[np.longdouble(0),np.cumsum(xs[::-1])]
    cut = np.asarray(cutoffs,dtype=np.longdouble)
    q = np.clip(np.searchsorted(minima,cut,side='left')-1,0,c-1)
    complete = (cut > 0)&(cut > maxima[q])&(cut <= minima[q+1])
    a = np.asarray([(-1)**int(k)*math.comb(c-1,int(k)) for k in q],dtype=np.longdouble)
    b = np.asarray([(-1)**int(k)*math.comb(c-2,int(k)-1) if k else 0 for k in q],dtype=np.longdouble)
    answer = np.where(complete,a*cut-b*minima[-1],0.)
    null = (cut <= 0)|(cut >= minima[-1])
    return np.asarray(answer,dtype=float),complete | null


def prime_regression(order, count, kind, seed, budget):
    from sympy import isprime, nextprime
    pars = parameters(order, .50005)
    logs = geometry(count, kind, 2*order, random.Random(seed))
    primes, used = [], set()
    for x in sorted(logs):
        p = int(nextprime(int(mp.exp(x))))
        while p in used:
            p = int(nextprime(p))
        used.add(p)
        primes.append(p)
    assert len(set(primes)) == count and all(isprime(p) for p in primes)
    true_logs = [mp.log(p) for p in primes]
    label = math.prod(primes)
    mask = core_mask(order, label, dict.fromkeys(primes, 1), pars, pars['ceiling'])
    r = grouped_riesz(true_logs, pars['length'], leaf_budget=budget,
                      primes=primes, integer_cutoff=pars['physical'])
    f = features(true_logs, pars)
    assert bool(mask == 'core') == f['modelCoreAdmissible']
    direct_error = None
    if count <= 12 and r.value is not None:
        direct_error = float(abs(r.value-direct_riesz(true_logs, pars['length'])))
        assert direct_error < 1e-60
    return dict(N=order, count=count, geometry=kind, seed=seed, literalCoreMask=mask,
                originalFiniteMasksRetained=True, phaseTransportNotAssumed=True,
                actualIntegerCutoffComparisons=True, primes=[str(p) for p in primes],
                response=serial_result(r), **{k:v for k,v in f.items() if k != 'count'},
                directEnumerationError=direct_error, primeCertificates=False,
                completeNativePopulation=False)


def literal_label_batch(records,heights,budget):
    """Evaluate any supplied factored labels with ONE common signed sum.

    This adapter permits new prime geometries without adding another named
    family. It is a finite-subset regression, not an estimate of missing
    integer labels. Complex phase and the FULL original factorial atom are
    evaluated before taking real parts; duplicate labels are not counted twice.
    """
    from sympy import isprime
    rows,groups,seen=[],defaultdict(list),set()
    duplicates=0
    for record in records:
        n=int(record['N']);u=float(record.get('radius',.50005))
        if n not in NATIVE or u not in RADII:
            raise ValueError('factored labels must use one of the supported native orders/radii')
        ps=sorted(map(int,record['primes']))
        if len(ps) < 3 or len(set(ps)) != len(ps) or not all(isprime(p) for p in ps):
            raise ValueError('factored labels need at least three distinct probable primes')
        label=math.prod(ps)
        key=(n,u,label)
        if key in seen:
            duplicates+=1
            continue
        seen.add(key)
        pars=parameters(n,u);xs=[mp.log(p) for p in ps];total=mp.fsum(xs)
        mask=core_mask(n,label,dict.fromkeys(ps,1),pars,pars['ceiling'])
        assigned,_=allocation(n,pars['orders'],xs,total,pars['length'])
        result=grouped_riesz(xs,pars['length'],primes=ps,integer_cutoff=pars['physical'],leaf_budget=budget)
        unassigned=max(0.,1-assigned)
        amplitude=(mp.exp((n+1)*mp.log(mp.mpf(str(u)))-mp.mpf('1.5')*total
                          +(n+1)*mp.log(total)-mp.loggamma(n+1)-mp.log(pars['length']))
                   *mp.mpf(str(unassigned)))
        # Check the original order-N kernel and full log(n)/L coefficient,
        # not a differently normalised proxy.
        direct=((mp.mpf(str(u))**(n+1))*unassigned*total/pars['length']
                *(total**n/mp.factorial(n))*mp.exp(-mp.mpf('1.5')*total))
        assert abs(amplitude-direct) < mp.mpf('1e-14')*max(abs(amplitude),mp.mpf('1e-100000'))
        index=len(rows)
        rows.append(dict(N=n,radius=u,count=len(ps),literalCoreMask=mask,
                         originalAllocatedFraction=assigned,
                         sourceNormalizedAmplitudeLog=str(mp.log(amplitude)) if amplitude else None,
                         response=serial_result(result),primes=[str(p) for p in ps]))
        groups[(n,u)].append((index,total,amplitude,result.value,mask))
    joined=[]
    for (n,u),labels in groups.items():
        for height in heights:
            included=[t for t in labels if t[4]=='core']
            unresolved=sum(t[3] is None for t in included)
            values=[-amp*r*mp.exp(-mp.j*mp.mpf(str(height))*t)
                    for _,t,amp,r,mask in included if r is not None]
            value=mp.fsum(values);absolute=mp.fsum(abs(v) for v in values)
            joined.append(dict(N=n,radius=u,height=height,selectedLabels=len(included),
                counts=sorted({rows[i]['count'] for i,_,_,_,_ in included}),
                unresolvedLabels=unresolved,sourceNormalized=True,
                originalFiniteMasksAndFullComplexPhase=True,
                allLabelsJoinedBeforeRealProjection=True,
                real=str(mp.re(value)) if not unresolved else None,
                imaginary=str(mp.im(value)) if not unresolved else None,
                absolute=str(absolute) if not unresolved else None,
                cancellationRatio=float(abs(value)/absolute) if absolute and not unresolved else None,
                completeSelectedLabelBatch=not unresolved,fullNativePopulation=False,
                floorCertificate=False))
    return dict(rows=rows,joined=joined,duplicateLabelsRemoved=duplicates,
                primeCertificates=False,intervalArithmetic=False)


def write_explorer(report, destination):
    """Local, self-contained view; leaves README and public explorers frozen."""
    selected = [{k:r[k] for k in ('N','radius','geometry','seed','count','totalLogOverN',
                    'largestShare','leastShare','reflectedLargeCount','roughCount','occupiedLogBins',
                    'originalAllocatedFraction','modelCoreAdmissible','modelRadialSignedKernel','response')}
                for r in report['rows']]
    for r in selected:
        r['response']={k:str(v) if isinstance(v,int) and abs(v)>2**53 else v
                       for k,v in r['response'].items()}
    data = json.dumps(selected, separators=(',', ':')).replace('</','<\\/')
    template = '''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Signed cancellation detector</title>
<style>body{font:16px system-ui;margin:2rem;background:#101923;color:#e4edf5}select,button{padding:.5rem;margin:.25rem;background:#243548;color:inherit;border:1px solid #698298}svg{width:100%;max-width:1200px;background:#17232f}a{color:#93d7ff}pre{white-space:pre-wrap;background:#17232f;padding:1rem}.muted{color:#aec2d4}rect{cursor:pointer}rect:hover{stroke:white;stroke-width:2}</style>
<h1>Signed structure / cancellation detector</h1>
<p>Continuous-log geometry scan, with original moving length and allocation. <b>This is not a native floor certificate.</b></p>
<p class="muted">Each tile retains its signed subset hinge. Grey means unresolved within the computation budget; dark means zero. Click for masks, geometry and exact combinatorial coverage. Red/green denote opposite signs; sizes are logarithmically coloured.</p>
<label>Order <select id="order"></select></label><label>Radius <select id="radius"></select></label>
<label>Seed <select id="seed"></select></label><label>Total log/N <select id="tau"></select></label>
<label>Quantity <select id="metric"><option value="response">Signed Riesz response</option><option value="kernel">Signed radial model kernel</option></select></label>
<div id="status"></div><svg id="plot" role="img" aria-label="Prime count versus log geometry coverage"></svg>
<pre id="detail">Select a tile.</pre>
<p>Counts and geometry cells are finite model probes. Actual-prime regression records and joined period tests are in the adjacent JSON report. Numerical cancellation between model counts supplies no prime-density transport or floor credit.</p>
<script>const rows=DATA;const controls=Object.fromEntries(['order','radius','seed','tau','metric','detail','status'].map(k=>[k,document.getElementById(k)]));
const names=[...new Set(rows.map(r=>r.geometry))];
function menu(id,key){let s=document.getElementById(id);[...new Set(rows.map(r=>r[key]))].sort((a,b)=>a-b).forEach(x=>{let o=document.createElement('option');o.textContent=x;o.value=x;s.append(o)});s.addEventListener('change',render)}
function svg(tag,attrs,parent){let e=document.createElementNS('http://www.w3.org/2000/svg',tag);Object.entries(attrs).forEach(([k,v])=>e.setAttribute(k,v));parent.append(e);return e}
function render(){const n=+controls.order.value,u=+controls.radius.value,s=+controls.seed.value,t=+controls.tau.value;let chosen=rows.filter(r=>r.N===n&&r.radius===u&&r.seed===s&&Math.abs(r.totalLogOverN-t)<1e-7);let max=Math.max(...chosen.map(r=>r.count),3), p=document.getElementById('plot');p.replaceChildren();p.setAttribute('viewBox',`0 0 ${200+(max-2)*17} 360`);for(let k=3;k<=max;k++){let label=svg('text',{x:200+(k-3)*17,y:25,fill:'#aec2d4','font-size':10},p);label.textContent=k}names.forEach((name,i)=>{let label=svg('text',{x:5,y:58+i*35,fill:'#e4edf5','font-size':14},p);label.textContent=name});let vals=chosen.map(r=>controls.metric.value==='kernel'?r.modelRadialSignedKernel:r.response.value), scale=Math.max(...vals.filter(v=>v!==null).map(v=>Math.log1p(Math.abs(v))),1e-30);chosen.forEach((r,i)=>{let v=vals[i],color='#77818d';if(v!==null){let a=Math.log1p(Math.abs(v))/scale;color=Math.abs(v)<1e-40?'#263442':v>0?`hsl(150 65% ${20+40*a}%)`:`hsl(10 75% ${20+40*a}%)`}let e=svg('rect',{x:198+(r.count-3)*17,y:37+names.indexOf(r.geometry)*35,width:15,height:28,fill:color,tabindex:0},p);let show=()=>controls.detail.textContent=JSON.stringify(r,null,2);e.addEventListener('click',show);e.addEventListener('keydown',event=>{if(event.key==='Enter'||event.key===' ')show()});let title=svg('title',{},e);title.textContent=`${r.geometry}, count ${r.count}: ${v===null?'unresolved':v}`});controls.status.textContent=`${chosen.length} models; ${chosen.filter(r=>r.response.value===null).length} unresolved; no native population coverage.`}
menu('order','N');menu('radius','radius');menu('seed','seed');rows.forEach(r=>r.totalLogOverN=Math.round(r.totalLogOverN*1e6)/1e6);menu('tau','totalLogOverN');controls.metric.addEventListener('change',render);render();</script></html>'''
    destination.write_text(template.replace('DATA',data))


def self_test():
    rng = random.Random(811)
    tests = []
    for count in range(2, 11):
        for repetition in range(3):
            logs = [mp.mpf(str(rng.uniform(.05, 2))) for _ in range(count)]
            cutoff = mp.fsum(logs)*mp.mpf(str(rng.uniform(.1, .9)))
            exact = direct_riesz(logs, cutoff)
            result = grouped_riesz(logs, cutoff, width=mp.mpf('0.6'), leaf_budget=10000)
            assert result.value is not None and abs(exact-result.value) < mp.mpf('1e-70')
            assert abs(exact-(-1)**count*direct_riesz(logs, mp.fsum(logs)-cutoff)) < mp.mpf('1e-70')
            bounded = grouped_riesz(logs, cutoff, width=mp.mpf('3'), leaf_budget=0,subset_budget=0)
            assert bounded.lower-mp.mpf('1e-70') <= exact <= bounded.upper+mp.mpf('1e-70')
            tests.append(dict(count=count, error=float(abs(exact-result.value))))
    primes = [3, 5, 7, 11, 13, 17, 19]
    logs = [mp.log(p) for p in primes]
    for x in [1, 3, 15, 105, 1000, math.prod(primes), math.prod(primes)+1]:
        result = grouped_riesz(logs, mp.log(x), width=1, primes=primes, integer_cutoff=x)
        assert result.value is not None
        assert abs(result.value-direct_riesz(logs, mp.log(x))) < mp.mpf('1e-70')
    # Large cardinality collapse, including parity and zero null moments.
    logs = [mp.mpf(1)+mp.mpf(i)/10**8 for i in range(63)]
    result = grouped_riesz(logs, mp.mpf('43.2'), width=1, leaf_budget=0)
    assert result.value is not None and result.collapsed_subsets == 2**63
    reflected = grouped_riesz(logs, mp.fsum(logs)-mp.mpf('43.2'), width=1, leaf_budget=0)
    assert abs(result.value+reflected.value) < mp.mpf('1e-50')
    incomplete = grouped_riesz([mp.mpf(2)**i for i in range(20)], 100,
                               width=mp.mpf('0.0001'), layer_budget=100)
    assert incomplete.value is None and incomplete.unresolved_subsets == 2**20
    xs=[mp.mpf(1)+mp.mpf(i)/10**8 for i in range(23)]
    values,valid=whole_layer_batch(xs,np.asarray([0.,1.5,5.2,11.7,23.1]))
    assert np.all(valid)
    for cut,value in zip([0.,1.5,5.2,11.7,23.1],values):
        truth=grouped_riesz(xs,mp.mpf(cut))
        assert truth.value is not None and abs(value-float(truth.value)) <= 1e-10*max(abs(value),1.)
    for order in NATIVE:
        orders=unpaid_orders(order)
        q=np.asarray([.01,.13,.4,.5,.8,.99])
        individual=np.sum(binom.pmf(orders[:,None],order+1,q[None,:]),axis=0)
        batch=binom.cdf(int(orders[-1]),order+1,q)-binom.cdf(int(orders[0])-1,order+1,q)
        assert np.allclose(individual,batch,atol=2e-13,rtol=2e-10)
    return dict(passed=True, independentSmallEnumerationCases=len(tests)+7,
                exactSixtyThreeFactorSubsetCoverage=2**63,
                reflectionAndUnresolvedEnclosuresChecked=True,
                batchedHighCountCoefficientsAndAllNativeAllocationOrdersChecked=True,
                maximumSmallError=max(t['error'] for t in tests))


def findings(rows, periods):
    solved = [r for r in rows if r['response']['value'] is not None and r['modelCoreAdmissible']]
    zeros = [r for r in solved if abs(r['response']['value']) < 1e-40]
    groups = defaultdict(list)
    for r in solved:
        groups[(r['N'], r['radius'], r['geometry'], r['seed'], round(r['totalLogOverN'], 5))].append(r)
    neighboring = []
    for key, block in groups.items():
        block.sort(key=lambda r:r['count'])
        for a, b in zip(block, block[1:]):
            if b['count'] != a['count']+1:
                continue
            x, y = a['modelRadialSignedKernel'], b['modelRadialSignedKernel']
            if x*y < 0:
                neighboring.append(dict(N=key[0], radius=key[1], geometry=key[2],
                    seed=key[3], totalLogOverN=key[4], counts=[a['count'], b['count']],
                    modelUnmatchedFraction=abs(x+y)/(abs(x)+abs(y)),
                    arithmeticMatchingOrDensityEstablished=False))
    neighboring.sort(key=lambda r:r['modelUnmatchedFraction'])
    comparable = defaultdict(list)
    joint_groups = defaultdict(list)
    for p in periods:
        comparable[(p['N'],p['radius'],p['count'],p['geometry'],p['height'],p['seed'])].append(p)
        joint_groups[(p['N'],p['radius'],p['geometry'],p['height'],p['seed'],p['nodes'])].append(p)
    joined_counts = []
    for key, values in joint_groups.items():
        blocks = np.asarray([p['periodSignedContributions'] for p in values])
        joined = blocks.sum(axis=0)
        separate = float(np.maximum(-blocks, 0.).sum())
        cost = float(np.maximum(-joined, 0.).sum())
        assert cost <= separate+1e-7*max(1., separate)
        complete = all(p['completeComputedModel'] for p in values)
        joined_counts.append(dict(N=key[0], radius=key[1], geometry=key[2],
            height=key[3], seed=key[4], nodes=key[5], counts=[p['count'] for p in values],
            modelJoinedReal=float(joined.sum()) if complete else None,
            modelJointAdverseCost=cost if complete else None,
            modelSeparateDiagnosticCost=separate if complete else None,
            modelCrossCountCancellation=1-cost/separate if separate and complete else None,
            completeComputedModel=complete, rankAsCancellationCandidate=complete,
            arithmeticPopulationWeightsEstablished=False, floorCredit=False))
    convergence = []
    for key, values in comparable.items():
        if len(values) < 2:
            continue
        values.sort(key=lambda r:r['nodes'])
        low, high = values[-2:]
        if not low['completeComputedModel'] or not high['completeComputedModel']:
            convergence.append(dict(N=key[0],radius=key[1],count=key[2],geometry=key[3],
                height=key[4],seed=key[5],nodes=[low['nodes'],high['nodes']],
                relativeToAbsoluteDifference=None,convergedDiagnostic=False,
                reason='unresolved hinge nodes',unresolvedNodes=[low['unresolvedNodes'],high['unresolvedNodes']]))
            continue
        difference = abs(low['modelJoinedReal']-high['modelJoinedReal'])
        denominator = max(high['modelPointwiseAbsoluteCost'], 1e-300)
        convergence.append(dict(N=key[0], radius=key[1], count=key[2], geometry=key[3],
            height=key[4], seed=key[5], nodes=[low['nodes'],high['nodes']],
            relativeToAbsoluteDifference=difference/denominator,
            convergedDiagnostic=difference/denominator < 1e-6 and high['completeComputedModel']))
    return dict(admissibleSolvedModels=len(solved), exactZeroModelCount=len(zeros),
                zeroResponseByGeometry=dict(Counter(r['geometry'] for r in zeros)),
                nearNeighborCountCandidates=neighboring[:24],
                joinedCountPeriodModels=joined_counts,
                periodQuadratureConvergence=convergence,
                noNativeCostOrFloorInferred=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[256, 640, 1536, 3584])
    parser.add_argument('--counts', nargs='+', type=int)
    parser.add_argument('--seeds', nargs='+', type=int, default=[317, 919])
    parser.add_argument('--radii', nargs='+', type=float, default=list(RADII))
    parser.add_argument('--taus', nargs='+', type=float, default=[1.9501, 1.99, 2.0299])
    parser.add_argument('--geometries', nargs='+', choices=GEOMETRIES, default=list(GEOMETRIES))
    parser.add_argument('--leaf-budget', type=int, default=20000)
    parser.add_argument('--periods', action='store_true')
    parser.add_argument('--period-counts', nargs='+', type=int, default=[3, 4, 5, 6, 10, 20, 40, 55, 56])
    parser.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    parser.add_argument('--nodes', nargs='+', type=int, default=[8, 16])
    parser.add_argument('--prime-regressions', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--render-report', type=Path, help='render an existing detector JSON without rerunning probes')
    parser.add_argument('--labels-json',type=Path,
                        help='arbitrary factored-label records: [{"N":256,"radius":0.50005,"primes":[...]}]')
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-structure-detector/scan.json'))
    args = parser.parse_args()
    if args.render_report:
        destination=args.render_report.with_suffix('.html')
        write_explorer(json.loads(args.render_report.read_text()),destination)
        print(json.dumps(dict(explorer=str(destination))))
        return
    if any(n not in NATIVE for n in args.orders):
        parser.error('use the original native schedules: '+str(sorted(NATIVE)))
    if any(u not in RADII for u in args.radii):
        parser.error('radii must be 0.5, 0.500025 or 0.50005')
    if any(not 1.95 < t <= 2.03 for t in args.taus):
        parser.error('all total-log slices must lie in the original strict core')
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error('phase heights must be finite and at least 54')
    if args.counts and any(k < 3 for k in args.counts):
        parser.error('prime counts must be at least three')
    if args.leaf_budget < 0 or any(n < 2 for n in args.nodes):
        parser.error('nonnegative leaf budget and at least two quadrature nodes required')
    if args.counts and any(not any(k < NATIVE[n] for k in args.counts) for n in args.orders):
        parser.error('each requested order needs at least one count below its native ceiling')
    mp.mp.dps = 100
    started = time.monotonic()
    report = dict(schemaVersion=1, kind='optional signed cancellation detector',
        head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        sourceSha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        helperSha256={name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                      for name in ['probe_riesz_canonical_joint.py','probe_riesz_fixed_count_period.py']},
        scope=dict(nativeFullPopulation=False, finiteGeometryScan=True,
                   intervalArithmetic=False, floorCertified=False, cofinalRateCertified=False,
                   countsSelectedWithinNativeCeilings=True,
                   fixedCountFitting=False, genericPNTTransportUsed=False,
                   originalMovingLengthAndOrderMask=True, logModelsNotPrimeDensityData=True),
        validation=self_test(), coverage=[], rows=[], periods=[], primeRegressions=[])
    if args.self_test:
        print(json.dumps(report['validation']), flush=True)
        return
    args.output.parent.mkdir(parents=True, exist_ok=True)
    snapshot=args.output.parent/('source-'+report['sourceSha256']+'.py')
    snapshot.write_bytes(Path(__file__).read_bytes())
    report['sourceSnapshotPath']=str(snapshot)
    if args.labels_json:
        records=json.loads(args.labels_json.read_text())
        if not isinstance(records,list):
            parser.error('labels-json must contain a list of factored-label records')
        report['literalLabelBatch']=literal_label_batch(records,args.heights,args.leaf_budget)
        report['seconds']=time.monotonic()-started
        args.output.write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(dict(output=str(args.output),literalLabels=len(report['literalLabelBatch']['rows']))))
        return
    for order in args.orders:
        counts = [k for k in (args.counts or range(3, NATIVE[order])) if k < NATIVE[order]]
        for radius in args.radii:
            for seed in args.seeds:
                batch = []
                for count, kind, tau in itertools.product(counts, args.geometries, args.taus):
                    batch.append(row(order, radius, count, kind, tau, seed, args.leaf_budget))
                report['rows'].extend(batch)
                report['coverage'].append(dict(N=order, radius=radius, seed=seed,
                    countRange=[min(counts), max(counts)] if counts else None,
                    counts=counts, geometries=args.geometries, totalLogSlices=args.taus,
                    tested=len(batch), coreAdmissible=sum(r['modelCoreAdmissible'] for r in batch),
                    unresolved=sum(r['response']['value'] is None for r in batch),
                    nativeIntegerPopulationCovered=False))
                args.output.write_text(json.dumps(report, indent=2)+'\n')
                print(json.dumps(report['coverage'][-1]), flush=True)
        if args.periods:
            for radius, seed, count, kind, height, nodes in itertools.product(
                    args.radii, args.seeds, args.period_counts, args.geometries, args.heights, args.nodes):
                if count < NATIVE[order]:
                    result=period_probe(order,radius,count,kind,height,seed,args.leaf_budget,nodes)
                    if not result['completeComputedModel']:
                        result['incompleteNodeDiagnostic']={k:result[k] for k in
                            ['modelJoinedReal','modelPeriodAdverseCost','modelPointwiseAbsoluteCost']}
                        for k in ['modelJoinedReal','modelPeriodAdverseCost','modelPointwiseAbsoluteCost',
                                  'modelSignedOverAbsolute','modelPeriodCancellationFraction']:
                            result[k]=None
                    report['periods'].append(result)
            print(json.dumps(dict(periodsDone=order, cases=len(report['periods']))), flush=True)
        if args.prime_regressions:
            for count, kind in [(3,'balanced'), (5,'owner_rectangle'), (min(12,NATIVE[order]-1),'two_clusters'),
                                (NATIVE[order]-1,'small_cluster'),(NATIVE[order]-1,'balanced')]:
                p = prime_regression(order, count, kind, args.seeds[0], args.leaf_budget)
                report['primeRegressions'].append(p)
                args.output.write_text(json.dumps(report, indent=2)+'\n')
                print(json.dumps(dict(primeRegressionDone=order, count=count, geometry=kind,
                                      mask=p['literalCoreMask'], unresolved=p['response']['unresolvedSubsets'])), flush=True)
    report['findings'] = findings(report['rows'], report['periods'])
    if report['primeRegressions']:
        report['literalLabelBatch']=literal_label_batch(report['primeRegressions'],args.heights,args.leaf_budget)
    report['seconds'] = time.monotonic()-started
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    write_explorer(report,args.output.with_suffix('.html'))
    print(json.dumps(dict(output=str(args.output), seconds=report['seconds'],
                          rows=len(report['rows']),periodCases=len(report['periods']),
                          unresolved=sum(r['response']['value'] is None for r in report['rows']),
                          primeRegressions=len(report['primeRegressions']))), flush=True)


if __name__ == '__main__':
    main()
