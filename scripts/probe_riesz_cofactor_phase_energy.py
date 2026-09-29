#!/usr/bin/env python3
"""Optional cofactor-phase diagnostic. Never imported by CI.

Actual primes, squarefree cofactors, original allocation and full phase are
retained on the 1.971N..2.029N test population. Earlier nested core deletions
are NOT applied. A signed cost of this enlarged population does not bound
its masked subsets. These floating values are NOT certificates or evidence
of an asymptotic rate. The previous joint cost omits sqrt(E); the new finite
cutoff-correlation cost has no such constant. Every coordinate is retained.
The new cost conservatively includes every cutoff up to the last possible
profile change, even when an individual coordinate is inactive.
At orders 6, 8 and 10 the entire test window is ABOVE the literal physical
annulus. The reported savings are diagnostics of the enlarged population,
not numerical bounds for a nonempty subset of the original core.
"""
import argparse
import json
import math
import time
import numpy as np
from probe_riesz_retained_discrepancy import coefficients
from probe_riesz_retained_factorial import unpaid_orders
from probe_riesz_sieve_mean import arithmetic

def probe(order, population, physical, height, radius, join_shells=False):
    upper = (math.floor(radius**(-order)/(order+1))+2)**2
    length = math.log(upper)
    mu, phi = arithmetic(max(population, upper))
    integers = np.arange(len(phi))
    primes = np.flatnonzero((phi == integers-1) & (integers >= 2))
    ps = primes[(primes > order**2) & (primes < upper)]
    lp = np.log(ps)
    all_increments = np.zeros((upper, len(ps))) if join_shells else None
    factors = [[] for _ in range(population+1)]
    for p in primes[primes <= population]:
        for n in range(int(p), population+1, int(p)):
            factors[n].append(int(p))
    totals, shells, labels, regressions = np.zeros(4), [], 0, []
    orders = unpaid_orders(order)
    for b in range(population.bit_length()):
        lower = 2**b
        if lower >= population:
            break
        end = min(2*lower, population)
        P = ps[(lp+math.log(2*lower) > 1.971*order)
               & (lp+math.log(lower) <= 2.029*order)]
        if not len(P):
            continue
        t, rows = np.log(P), []
        row_labels=[]
        powers = t[None, :]**np.arange(order+2)[:, None]
        for n in range(max(2, lower+1), end+1):
            fs = factors[n]
            if mu[n] == 0 or len(fs) < 2 or (physical and min(fs) <= order**2):
                continue
            logs, v = [math.log(p) for p in fs], math.log(n)
            total = t+v
            selected = ((total > 1.971*order) & (total <= 2.029*order)
                        & (t < .65*total) & (P > max(fs)))
            if not selected.any():
                continue
            eligible = [math.log(p) for p in fs if order**2 < p < upper]
            poly = coefficients(order, logs, eligible)@powers
            weight = (-poly*np.exp(-total/2)/(n*P)*np.cos(height*total)
                      *radius**(order+1)/(length*math.factorial(order)))
            rows.append(weight*selected)
            row_labels.append(n)
            labels += int(selected.sum())
            if len(regressions) < 256:
                inds = np.flatnonzero(selected)
                theta = np.zeros_like(t)
                for q in [t, *eligible]:
                    theta += sum(math.comb(order+1, k)
                                 *((total-q)/total)**k*(q/total)**(order+1-k)
                                 for k in orders)
                direct_poly = (1-theta)*total**(order+1)
                error = float(np.max(np.abs(poly[inds]-direct_poly[inds])
                                     /np.maximum(np.abs(poly[inds]), 1e-100)))
                ds = [1]
                for p in fs:
                    ds += [p*d for d in ds]
                ds = np.asarray(ds)
                # The actual original residual coefficient uses the divisor
                # sum of pn; splitting its divisors gives this same hinge.
                hinge = np.minimum(t[inds, None], np.maximum(0., length-np.log(ds))[None, :])
                response = hinge@mu[ds]
                atom = weight[inds]*response
                direct = (-(1-theta[inds])*total[inds]*response/length
                          *total[inds]**order/math.factorial(order)
                          *np.exp(-1.5*total[inds])*np.cos(height*total[inds])
                          *radius**(order+1))
                atom_error = float(np.max(np.abs(atom-direct))
                                   /max(1e-100, float(np.max(np.abs(atom)))))
                regressions.append(max(error, atom_error))
        if not rows:
            continue
        A = np.asarray(rows)
        stop = min(upper, end-1)
        k = np.arange(1, stop+1, dtype=float)
        hinge = np.maximum(0., length-np.log(np.arange(1, stop+2, dtype=float)))
        profile = np.minimum(t[:, None], hinge[None, :])
        D = (profile[:, :-1]-profile[:, 1:])*np.sqrt(k)
        logdir = np.sqrt(k)*np.log1p(1/k)
        cross = D@logdir
        kv = np.arange(1, end, dtype=float)
        lognorm = float(np.sum(kv*np.log1p(1/kv)**2))
        tailnorm = float(np.sum(kv[stop:]*np.log1p(1/kv[stop:])**2))
        gram = D@D.T-np.outer(cross, cross)/lognorm
        vals, Q = np.linalg.eigh((gram+gram.T)/2)
        # DO NOT discard small eigenvalues or their coordinate columns.
        assert vals.min() >= -1e-9*max(1., float(vals.max()))
        orthogonality = float(np.max(np.abs(Q.T@Q-np.eye(len(P)))))
        assert orthogonality < 1e-10
        rotated = Q.T@D
        slope = (Q.T@cross)/lognorm
        centered = rotated-slope[:, None]*logdir[None, :]
        energies = np.sum(centered**2, axis=1)+slope**2*tailnorm
        weight_energies = np.zeros(len(P))
        for start in range(0, len(A), 2048):
            weight_energies += np.sum((A[start:start+2048]@Q)**2, axis=0)
        joint = float(np.sqrt(weight_energies*energies).sum())*math.sqrt(end)
        slope0 = cross/lognorm
        centered0 = D-slope0[:, None]*logdir[None, :]
        energy0 = np.sum(centered0**2, axis=1)+slope0**2*tailnorm
        separate = float(np.sqrt(np.sum(A*A, axis=0)*energy0).sum())*math.sqrt(end)
        increments=np.zeros((stop,len(P)))
        for n,row in zip(row_labels,A):
            divisors=[1]
            for prime in factors[n]:
                divisors += [prime*d for d in divisors if prime*d<=stop]
            ds=np.asarray(divisors)
            increments[ds-1] += mu[ds,None]*row
        if join_shells:
            all_increments[:stop, np.searchsorted(ps, P)] += increments
        prefixes=np.cumsum(increments,axis=0)
        dual_rot=prefixes@Q
        dual_energy=np.sum(dual_rot**2/k[:,None],axis=0)
        raw_energy=np.sum(rotated**2,axis=1)
        dual_cost=float(np.sqrt(dual_energy*raw_energy).sum())
        signed=float(np.sum(prefixes*(profile[:,:-1]-profile[:,1:]).T))
        totals += [joint, separate,dual_cost,signed]
        shells.append(dict(lower=lower, upper=end, cofactors=len(A), primes=len(P),
                           coordinateColumns=Q.shape[1], allCoordinateColumnsRetained=True,
                           maximumOrthogonalityError=orthogonality,
                           smallestComputedGramEigenvalue=float(vals.min()),
                           cofactorPhaseCost=dual_cost, signedSum=signed, jointCostWithoutSqrtE=joint, separatePrimeCostWithoutSqrtE=separate))
    joined = None
    if join_shells:
        stop = min(upper, population-1)
        k = np.arange(1, stop+1, dtype=float)
        hinge = np.maximum(0., length-np.log(np.arange(1, stop+2, dtype=float)))
        profile = np.minimum(lp[:, None], hinge[None, :])
        delta = profile[:, :-1]-profile[:, 1:]
        D = delta*np.sqrt(k)
        logdir = np.sqrt(k)*np.log1p(1/k)
        cross = D@logdir
        kv = np.arange(1, population, dtype=float)
        lognorm = float(np.sum(kv*np.log1p(1/kv)**2))
        gram = D@D.T-np.outer(cross, cross)/lognorm
        vals, Q = np.linalg.eigh((gram+gram.T)/2)
        orthogonality = float(np.max(np.abs(Q.T@Q-np.eye(len(ps)))))
        assert orthogonality < 1e-10
        assert vals.min() >= -1e-9*max(1., float(vals.max()))
        prefixes = np.cumsum(all_increments[:stop], axis=0)
        dual_energy = np.sum((prefixes@Q)**2/k[:, None], axis=0)
        raw_energy = np.sum((Q.T@D)**2, axis=1)
        joined_cost = float(np.sqrt(dual_energy*raw_energy).sum())
        joined_signed = float(np.sum(prefixes*delta.T))
        assert abs(joined_signed-float(totals[3])) < 1e-12
        assert abs(joined_signed) <= joined_cost+1e-12
        joined = dict(cost=joined_cost, signedSum=joined_signed,
                      primeColumns=len(ps), allCoordinateColumnsRetained=True,
                      maximumOrthogonalityError=orthogonality,
                      physicalCutoff=stop, meanConstantRequired=False)
    assert max(regressions, default=0.) < 2e-8
    return dict(order=order, population=population, radius=radius, height=height,
                allCofactorPrimesAboveNSquared=physical, length=length, physicalUpper=upper,
                selectedLabels=labels, jointCost=float(totals[0]), separatePrimeCost=float(totals[1]),
                cofactorPhaseCost=float(totals[2]),signedSum=float(totals[3]),sourceCostsOmitSqrtE=True, constantEvaluated=False, wholeCarrierCovered=False,
                allCoordinateColumnsRetained=True, regressionRows=len(regressions),
                maximumAtomRelativeError=max(regressions, default=0.), shells=shells,
                joinedCofactorShells=joined)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-order',type=int,choices=[6,8,10],default=8)
    parser.add_argument('--heights',type=float,nargs='+',default=[0.,54.,108.])
    parser.add_argument('--join-cofactor-shells', action='store_true',
                        help='Also sum all cofactor shells before the cutoff square.')
    args=parser.parse_args()
    rows=[]
    for order in [6,8,10]:
        if order>args.max_order:
            continue
        population=math.floor(math.exp(2.029*order)/(order**2+1))
        for height in args.heights:
            started=time.monotonic()
            result=probe(order,population,False,height,10001/20000,args.join_cofactor_shells)
            assert abs(result['signedSum']) <= result['cofactorPhaseCost']+1e-12
            result['elapsedSeconds']=time.monotonic()-started
            result['coreWindow']=[1.971,2.029]
            result['physicalAnnulusUpperLogOverOrder']=2*result['length']/order
            result['testWindowDisjointFromPhysicalAnnulus']=(
                result['physicalAnnulusUpperLogOverOrder'] <= 1.971)
            result['cofactorPhaseCostOmitsNoMeanConstant']=True
            rows.append(result)
    print(json.dumps(dict(scope=__doc__.strip(),rows=rows),indent=2))

if __name__=='__main__':
    main()
