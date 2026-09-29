#!/usr/bin/env python3
"""Optional coupled quadratic-moment diagnostic; never a CI certificate.

Keep all prime counts together. The quadratic correction is explicit and
signed, and is supported on two-prime cofactors. Quadratic costs omit the
UNEVALUATED sqrt(E); optional conditioned costs use an explicitly UNCERTIFIED
constant and depend nonlinearly on it. Actual primes, allocation and phase are
used on truncated test sets;
no source-scale or eventual threshold is proved by floating calculations.
"""
import argparse
import json
import math
import numpy as np
from probe_riesz_retained_discrepancy import coefficients
from probe_riesz_retained_factorial import unpaid_orders
from probe_riesz_sieve_mean import arithmetic

def probe(order, population, physical, height, radius, arithmetic_constant=None,
          coordinate_audit=None, log_moment_order=2):
    upper = (math.floor(radius**(-order)/(order+1))+2)**2
    length = math.log(upper)
    mu, phi = arithmetic(max(population, upper))
    integers = np.arange(len(phi))
    primes = np.flatnonzero((phi == integers-1) & (integers >= 2))
    ps = primes[(primes > order**2) & (primes < upper)]
    lp = np.log(ps)
    factors = [[] for _ in range(population+1)]
    for p in primes[primes <= population]:
        for n in range(int(p), population+1, int(p)):
            factors[n].append(int(p))
    shells, labels, regressions = [], 0, []
    orders = unpaid_orders(order)
    for b in range(population.bit_length()):
        lower = 2**b
        if lower >= population:
            break
        end = min(2*lower, population)
        P = ps[(lp+math.log(2*lower) > 1.95*order)
               & (lp+math.log(lower) <= 2.03*order)]
        if not len(P):
            continue
        t, rows, moments, counts, log_moments = np.log(P), [], [], [], []
        powers = t[None, :]**np.arange(order+2)[:, None]
        for n in range(max(2, lower+1), end+1):
            fs = factors[n]
            if mu[n] == 0 or len(fs) < 2 or (physical and min(fs) <= order**2):
                continue
            logs, v = [math.log(p) for p in fs], math.log(n)
            total = t+v
            selected = ((total > 1.95*order) & (total <= 2.03*order)
                        & (t < .65*total) & (P > max(fs)))
            if not selected.any():
                continue
            eligible = [math.log(p) for p in fs if order**2 < p < upper]
            poly = coefficients(order, logs, eligible)@powers
            weight = (-poly*np.exp(-total/2)/(n*P)*np.cos(height*total)
                      *radius**(order+1)/(length*math.factorial(order)))
            rows.append(weight*selected)
            moments.append(2*logs[0]*logs[1] if len(fs)==2 else 0.)
            counts.append(len(fs))
            if log_moment_order > 2:
                moment_polynomial = np.array([1.]+[0.]*log_moment_order)
                for logp in logs:
                    moment_polynomial = np.convolve(moment_polynomial, np.array(
                        [0.]+[-logp**j/math.factorial(j) for j in range(1, log_moment_order+1)]))[:log_moment_order+1]
                log_moments.append([moment_polynomial[j]*math.factorial(j)
                                    for j in range(1, log_moment_order+1)])
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
                predicted = 2*logs[0]*logs[1] if len(fs)==2 else 0.
                moment_error = abs(float(mu[ds]@(np.log(ds)**2))-predicted)/max(1.,float(np.sum(np.log(ds)**2)))
                regressions.append(max(error, atom_error, moment_error))
                if log_moment_order > 2:
                    for j in range(1, log_moment_order+1):
                        check = abs(float(mu[ds]@(np.log(ds)**j))-log_moments[-1][j-1])
                        assert check/max(1., float(np.sum(np.log(ds)**j))) < 1e-12
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
        v1=np.sqrt(kv)*np.log1p(1/kv)
        v2=np.sqrt(kv)*(np.log(kv)**2-np.log(kv+1)**2)/math.log(end)**2
        beta=float(v2@v1)/lognorm
        v2-=beta*v1
        norm2=float(v2@v2)
        cross2=D@v2[:stop]
        projection_coefficients=cross2/norm2
        center=float(np.asarray(moments)@(A@projection_coefficients))/math.log(end)**2
        vals,Q=np.linalg.eigh((gram+gram.T)/2)
        orthogonality=float(np.max(np.abs(Q@Q.T-np.eye(len(P)))))
        assert orthogonality<1e-10
        transformed=A@Q; e=np.sum(transformed**2,axis=0)
        rd=Q.T@D; slope=(Q.T@cross)/lognorm
        residual=rd-slope[:,None]*logdir[None,:]
        a=(Q.T@cross2)/norm2
        after=residual-a[:,None]*v2[None,:stop]
        oldenergy=np.sum(residual**2,axis=1)+slope**2*tailnorm
        # In the exterior, D is zero; retain the signed cross term of both removed moments.
        tail2=float(v2[stop:]@v2[stop:]); mixed=float(v1[stop:]@v2[stop:])
        newenergy=np.sum(after**2,axis=1)+slope**2*tailnorm+a*a*tail2+2*slope*a*mixed
        assert min(newenergy)>-1e-10
        c0=math.sqrt(end)*np.sqrt(e*np.maximum(oldenergy,0.)).sum()
        c1=math.sqrt(end)*np.sqrt(e*np.maximum(newenergy,0.)).sum()
        assert c1<=c0+1e-8
        entry=dict(lower=lower,upper=end,old=c0,new=c1,center=center,
                   semiprimeRows=sum(v!=0 for v in moments),coordinateColumns=Q.shape[1],
                   maximumOrthogonalityError=orthogonality,allCoordinateColumnsRetained=True)
        if coordinate_audit is not None:
            extra = {'log_moments': np.asarray(log_moments)} if log_moment_order > 2 else {}
            entry['coordinateAudit']=coordinate_audit(
                A=A, D=D, Q=Q, cross=cross, cross2=cross2, lognorm=lognorm,
                logdir=logdir, v2=v2, norm2=norm2, tailnorm=tailnorm,
                tail2=tail2, mixed=mixed, gram=gram, end=end,
                moments=np.asarray(moments), counts=np.asarray(counts), **extra)
        if arithmetic_constant is not None:
            moment_pair=np.asarray(moments)@transformed
            remainder=arithmetic_constant*end*e-moment_pair**2/(norm2*math.log(end)**4)
            assert float(np.min(remainder))>=-1e-14
            conditioned=float(np.sqrt(np.maximum(remainder,0.)*np.maximum(newenergy,0.)).sum())
            entry['conditionedCostAtAssumedConstant']=conditioned
            assert conditioned<=math.sqrt(arithmetic_constant)*c1+1e-10
        shells.append(entry)
    assert max(regressions, default=0.) < 2e-8
    result=dict(order=order, population=population, radius=radius, height=height,
                allCofactorPrimesAboveNSquared=physical, length=length, physicalUpper=upper,
                selectedLabels=labels, jointCost=sum(r["old"] for r in shells), quadraticCost=sum(r["new"] for r in shells), center=sum(r["center"] for r in shells),
                sourceCostsOmitSqrtE=True, constantEvaluated=False, wholeCarrierCovered=False,
                allCoordinateColumnsRetained=True, regressionRows=len(regressions),
                maximumRegressionRelativeError=max(regressions, default=0.), shells=shells)
    if arithmetic_constant is not None:
        result['conditionedDiagnostic']={
            'assumedArithmeticConstant':arithmetic_constant,
            'arithmeticConstantCertified':False,
            'quadraticCostAtAssumedConstant':math.sqrt(arithmetic_constant)*result['quadraticCost'],
            'conditionedCostAtAssumedConstant':sum(r['conditionedCostAtAssumedConstant'] for r in shells),
            'warning':'This saving depends nonlinearly on E. The chosen E is NOT proved to satisfy the arithmetic mean theorem.'}
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-order',type=int,default=10,choices=[6,8,10])
    parser.add_argument('--expand-population',action='store_true')
    parser.add_argument('--conditioned-constant',type=float,help='Exploratory E only; never a certified arithmetic constant')
    args=parser.parse_args()
    if args.conditioned_constant is not None and args.conditioned_constant<=0:
        parser.error('--conditioned-constant must be positive')
    rows=[]
    for n,x in [(6,4096),(8,65536),(10,1048576)]:
        if n>args.max_order: continue
        if args.expand_population: x=math.floor(math.exp(2.03*n)/(n*n+1))
        for physical in [False,True]: rows.append(probe(n,x,physical,54.,10001/20000,args.conditioned_constant))
    print(json.dumps(dict(scope=__doc__.strip(),expandedPopulation=args.expand_population,rows=rows),indent=2))

if __name__=='__main__':
    main()
