#!/usr/bin/env python3
"""Optional actual-prime sampling in the unpaid balanced-pair rectangle.

This is NOT a floor certificate or Lean theorem. Optional finite-box
population estimates use the explicit stopped-sampling count correction;
they do not replace the prime population by a continuous density.
Samples are independent uniform odd-integer rejection samples. Every
accepted integer is checked by FLINT's proven-prime routine. Retain the
literal moving length, actual factorial weight and complete phase.
Report marginal/bootstrap uncertainty: the Cartesian pairs share primes
and must never be counted as m*m independent observations.

Optional analysis dependency: python-flint==0.9.0. No default CI changes.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import time

import gmpy2
import numpy as np
from flint import arb, ctx, fmpz
import flint


U_NUM = 10001
U_DEN = 20000


def exact_floor_exp(n):
    v = arb(n).exp().floor().unique_fmpz()
    if v is None:
        raise ArithmeticError('Exp endpoint floor was not uniquely enclosed')
    return int(v)


def sample_primes(n, size, seed):
    lo, hi = exact_floor_exp(n)+1, exact_floor_exp(n+1)
    first = lo if lo % 2 else lo+1
    count = (hi-first)//2+1
    rng = random.Random(seed)
    accepted = []
    trials = 0
    start = time.monotonic()
    while len(accepted) < size:
        p = first+2*rng.randrange(count)
        trials += 1
        if not gmpy2.is_prime(p, 32):
            continue
        # A probable-prime result is only a filter. The final check is proven.
        if not fmpz(p).is_prime():
            continue
        accepted.append(p)
        if len(accepted) % 16 == 0:
            print(json.dumps(dict(logLower=n,accepted=len(accepted),size=size,
                elapsedSeconds=time.monotonic()-start)), flush=True)
    return dict(logLower=n,seed=seed,size=size,trialCount=trials,
                elapsedSeconds=time.monotonic()-start,
                provedByFLINT=True,provedInLean=False,
                samplingWithReplacement=True,primes=[str(p) for p in accepted])


def stopped_count(data):
    """Count diagnostic, never a PNT replacement or certified count.

    For ideal independent uniform draws, T is negative binomial and
    E[(r-1)/(T-1)]=theta. Using r/T would introduce a stopping bias.
    Accepted marks are independent of T in that ideal model. The
    reproducible pseudorandom generator is not a Lean probability proof.
    """
    n = data['logLower']
    lo, hi = exact_floor_exp(n)+1, exact_floor_exp(n+1)
    first = lo if lo % 2 else lo+1
    population = (hi-first)//2+1
    r, trials = data['size'], data['trialCount']
    rate = (r-1)/(trials-1)
    return dict(oddCandidatePopulation=str(population),
        acceptedPrimeCount=r,totalOddTrials=trials,
        stoppedSamplingSuccessRateEstimate=rate,
        logPrimeCountEstimate=math.log(population)+math.log(rate),
        successRateEstimator='(accepted-1)/(trials-1)',
        countCertified=False,continuousPrimeDensityUsed=False)


def phase(logs, y):
    values = []
    radius = 0.0
    for x in logs:
        v = -y*x
        re, im = v.cos(), v.sin()
        radius = max(radius, float(re.rad()), float(im.rad()))
        values.append(complex(float(re.mid()), float(im.mid())))
    assert radius < 1e-30, radius
    return np.array(values), radius


def literal_weights(N, left, right):
    D = U_DEN**N//((N+1)*U_NUM**N)
    Lball = arb((D+2)**2).log()
    L = float(Lball.mid())
    x = np.array([float(v.mid()) for v in left])[:, None]
    z = np.array([float(v.mid()) for v in right])[None, :]
    T = x+z
    assert np.all(T > 1.971*N+1) and np.all(T <= 2.029*N-1)
    assert np.all(z < 1.02*N) # Both original owner masks are false.
    assert np.all(x <= L) and np.all(z <= L) and np.all(T > L)
    response = L-np.maximum(L-x, 0)-np.maximum(L-z, 0)+np.maximum(L-T, 0)
    joined = -T*response/L
    selberg = -2*x*z/T
    defect = joined-selberg
    assert np.min(defect) > 0
    # Remove a single COMMON positive kernel factor. Relative signed sums
    # retain exactly the literal factorial/radial weight, not a saddle freeze.
    ref = 2*N+2
    weights = (defect/N)*np.exp(N*np.log1p((T-ref)/ref)-1.5*(T-ref))
    direct = 1.5*T-T*T/L-(x-z)**2/(2*T)
    assert np.max(np.abs(direct-defect))/N < 1e-12
    return weights, dict(movingLength=L,exactDampedFloorDigits=len(str(D)),
        normalizedByCommonPositiveFactor=True,
        rectangularOrderMaskIntroduced=False,
        ownerHeadMaskRemoved=False,ownerCorrectionMaskRemoved=False,
        ownerHeadMaskFalseOnAllSamples=True,ownerCorrectionMaskFalseOnAllSamples=True,
        strictInteriorCompletePeriodGeometry=True,
        minimumLiteralDefectOverN=float(defect.min()/N),
        factorialKernelFrozen=False)


def summaries(weights, pl, qr, seed, bootstraps, N, counts):
    atoms = weights*pl[:, None]*qr[None, :]
    denominator = float(weights.sum())
    value = complex(atoms.sum()/denominator)
    # Quantify a signed rank-one diagnostic, not an independent carrier bound.
    left, vals, right = np.linalg.svd(weights, full_matrices=False)
    rank_one = vals[0]*left[:, 0, None]*right[None, 0, :]
    first = complex((rank_one*pl[:, None]*qr[None, :]).sum()/denominator)
    residual = float(np.abs(weights-rank_one).sum()/denominator)
    assert abs(value-first) <= residual+1e-12
    rng = np.random.default_rng(seed)
    means = []
    population_means = []
    ref = 2*N+2
    # Restore the EXACT common positive factorial normalization used above.
    # These are floating diagnostics, not certified interval arithmetic.
    log_scale = ((N+1)*math.log(U_NUM/U_DEN)+math.log(N)-1.5*ref+
                 N*math.log(ref)-math.lgamma(N+1)+
                 sum(c['logPrimeCountEstimate'] for c in counts))
    scale = math.exp(log_scale) if -700 < log_scale < 700 else None
    for _ in range(bootstraps):
        i = rng.integers(0, len(pl), len(pl))
        j = rng.integers(0, len(qr), len(qr))
        q = np.ix_(i,j)
        means.append(float(atoms[q].real.sum()/weights[q].sum()))
        # Parametric stopping-time bootstrap plus two separately sampled
        # marginals. The Cartesian products are NOT independent draws.
        count_ratio = 1.
        for c in counts:
            r = c['acceptedPrimeCount']
            trials = r+rng.negative_binomial(r,
                c['stoppedSamplingSuccessRateEstimate'])
            count_ratio *= (c['totalOddTrials']-1)/(trials-1)
        if scale is not None:
            population_means.append(scale*count_ratio*float(atoms[q].real.mean()))
    interval = np.quantile(means, [0.025,0.975]).tolist()
    population_interval = (np.quantile(population_means,[0.025,0.975]).tolist()
                           if scale is not None else None)
    return dict(relativeSignedReal=value.real,relativeSignedImag=value.imag,
        relativeSignedModulus=abs(value),
        marginalPrimePhaseMagnitudes=[float(abs(pl.mean())),float(abs(qr.mean()))],
        rankOneSignedReal=first.real,rankOneRemainderL1Ratio=residual,
        floatingSampleUpperDiagnostic=first.real+residual,
        empiricalTwoMarginalBootstrap95=interval,
        logSourcePopulationCommonScale=log_scale,
        sourceScaledFiniteBoxRealEstimate=(scale*float(atoms.real.mean())
                                           if scale is not None else None),
        sourceScaledFiniteBoxModulusEstimate=(scale*abs(complex(atoms.mean()))
                                              if scale is not None else None),
        sourceScaledFiniteBoxAbsolutePriceEstimate=(scale*float(weights.mean())
                                                    if scale is not None else None),
        empiricalFiniteBoxPopulationBootstrap95=population_interval,
        estimatedPopulationIsOnlyTheTwoFinitePrimeBoxes=True,
        bootstrapIsCertifiedConfidenceBound=False,
        primeSamples=len(pl)+len(qr),cartesianPairs=len(pl)*len(qr),
        cartesianPairsAreIndependentObservations=False,
        cancellationCreditedToPopulation=0,independentFloorBound=False)


def run(args):
    ctx.prec = max(1024,math.ceil((args.huge_height_digits+80)*math.log2(10)),
                   math.ceil((max(args.orders)+2)/math.log(2))+256)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    sample_path = args.output.with_suffix('.primes.json')
    if args.reuse_samples and sample_path.exists():
        samples = json.loads(sample_path.read_text())
        assert samples['orders'] == args.orders and samples['seeds'] == args.seeds
        assert samples['sizes'] == args.sizes
    else:
        samples = dict(orders=args.orders,seeds=args.seeds,sizes=args.sizes,rows=[])
        for N,size in zip(args.orders,args.sizes):
            for seed in args.seeds:
                left = sample_primes(N,size,seed+10000*N)
                right = sample_primes(N+1,size,seed+10000*N+5000)
                assert all(int(q) > N**16 for q in left['primes']+right['primes'])
                samples['rows'].append(dict(N=N,seed=seed,left=left,right=right))
                sample_path.write_text(json.dumps(samples,sort_keys=True,indent=2)+'\n')
    heights = [('54',arb(54)),('100',arb(100)),
               (f'10^{args.huge_height_digits}',arb(10)**args.huge_height_digits)]
    results = []
    for row in samples['rows']:
        N,seed = row['N'],row['seed']
        left = [arb(int(v)).log() for v in row['left']['primes']]
        right = [arb(int(v)).log() for v in row['right']['primes']]
        assert all(arb(N)<v and v<=arb(N+1) for v in left)
        assert all(arb(N+1)<v and v<=arb(N+2) for v in right)
        weights, masks = literal_weights(N,left,right)
        counts = [stopped_count(row[side]) for side in ['left','right']]
        for label,y in heights:
            pl, er1 = phase(left,y)
            qr, er2 = phase(right,y)
            result = dict(N=N,seed=seed,height=label,**masks,
                **summaries(weights,pl,qr,seed,args.bootstraps,N,counts),
                phaseBallRadiusUpper=max(er1,er2),
                countDiagnostics=counts,
                entirelyAbovePolynomialCofactorPayment=True,
                boundForAllRetainedLabels=False)
            results.append(result)
            print(json.dumps({k:result[k] for k in
                ['N','seed','height','relativeSignedReal','relativeSignedModulus',
                 'empiricalTwoMarginalBootstrap95','rankOneRemainderL1Ratio']}),flush=True)
    report = dict(schemaVersion=2,
        classification='Actual-prime sampling diagnostic; no deterministic population saving',
        sampleFile=str(sample_path),sampleFileSha256=hashlib.sha256(sample_path.read_bytes()).hexdigest(),
        scriptSha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        pythonFlintVersion=flint.__version__,gmpy2Version=gmpy2.version(),
        arbPrecisionBits=ctx.prec,phaseHeightsAreNotAssertedZeroOrdinates=True,
        atomicMasksRetained=True,rectangleIsOnlyOneSubblock=True,
        sourceScaledFiniteBoxPopulationEstimated=True,
        sourceScaledWholeRetainedAggregateEstimated=False,
        idealRandomStoppedCountEstimatorUsed=True,
        pseudorandomSamplingIsNotAProbabilityCertificate=True,
        allPrimeCountsEstimated=False,cofinalInference=False,
        target='399/5000 + o(1)',milestoneAchieved=False,
        savingCreditedAgainstTarget=0,rows=results)
    args.output.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',type=int,nargs='+',default=[256,640])
    parser.add_argument('--sizes',type=int,nargs='+',default=[128,32])
    parser.add_argument('--seeds',type=int,nargs='+',default=[731,732])
    parser.add_argument('--huge-height-digits',type=int,default=1800)
    parser.add_argument('--bootstraps',type=int,default=200)
    parser.add_argument('--output',type=Path,
        default=Path('.lake/riesz-balanced-prime-sampling/result.json'))
    parser.add_argument('--reuse-samples',action='store_true')
    ns=parser.parse_args()
    if len(ns.orders)!=len(ns.sizes) or min(ns.sizes)<8 or min(ns.orders)<256:
        parser.error('Use one size>=8 per order>=256')
    run(ns)
