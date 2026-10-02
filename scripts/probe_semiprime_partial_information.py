#!/usr/bin/env python3
"""Optional semiprime side investigation; never an ordinary build/CI job.

The extractor sees N, a small-prime cutoff and a local integer window.
It never receives the factors. Known local (Lambda*Lambda) coefficients
are subtracted from an actual numerical zeta integral. No prime-pair
coefficient table is used in that integral. Reference factorisations are
computed only after measurement, for validation/baselines.

Analytic leakage, alias and truncation envelopes do NOT certify FFT,
frequency-rounding or floating-point error. Candidate recovery is therefore
experimental; any returned factors are checked by exact division.
"""

import argparse
import json
import math
import random
import statistics
import time
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy import fft, optimize
from sympy import bernoulli, integer_nthroot, isprime, primerange

SIGMA = 2.0
EM_ORDER = 20
FFT_ORDER = 24
BERNOULLI = [float(bernoulli(2*r)/math.factorial(2*r))
             for r in range(1, EM_ORDER+1)]
MODULI = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)


def z_bound(sigma):
    return 1.0 + 1.0/(sigma-1.0)**2


def prime_power(n):
    """No factoring: exact integer roots followed by primality tests.

    All measured inputs/aliases are below 2^64, where SymPy's primality
    test is deterministic. Returns (prime, exponent) or None.
    """
    if n < 2:
        return None
    if isprime(n):
        return n, 1
    for exponent in range(2, n.bit_length()):
        root, exact = integer_nthroot(n, exponent)
        if exact and isprime(root):
            return int(root), exponent
    return None


def coefficient_from_one_factor(n, p):
    """Exact formula given ONE prime divisor, even if the rest is composite.

    n=p^a: (a-1) log(p)^2; n=p^a*q^b: 2 log(p) log(q).
    If the residual is not a prime power, three distinct primes occur and
    Lambda*Lambda is exactly zero. Formula values use floating logarithms.
    """
    assert n % p == 0 and isprime(p)
    remainder, exponent = n, 0
    while remainder % p == 0:
        remainder //= p
        exponent += 1
    if remainder == 1:
        return (exponent-1)*math.log(p)**2
    power = prime_power(remainder)
    return 0.0 if power is None else 2*math.log(p)*math.log(power[0])


def local_information(N, cutoff, window):
    """Segmented SMALL-factor sieve; no full neighbouring factorisation."""
    assert N+window < 2**64
    started = time.perf_counter()
    primes = tuple(map(int, primerange(2, cutoff+1)))
    direct = next((p for p in primes if N % p == 0), None)
    lower, upper = max(2, N-window), N+window
    first_factor = [0]*(upper-lower+1)
    for p in primes:
        for n in range(lower + (-lower % p), upper+1, p):
            if not first_factor[n-lower]:
                first_factor[n-lower] = p
    entries = []
    for n in range(lower, upper+1):
        if n == N:
            continue  # the target's coefficient is NEVER calculated here
        p = first_factor[n-lower]
        if p:
            value = coefficient_from_one_factor(n, p)
            reason = 'one-small-factor'
        else:
            power = prime_power(n)
            if power is None:
                value, reason = None, 'unknown-rough-composite'
            else:
                value = (power[1]-1)*math.log(power[0])**2
                reason = 'prime-or-prime-power'
        entries.append((n, value, reason, p))
    return dict(N=N, cutoff=cutoff, window=window, entries=entries,
                directFactor=direct, seconds=time.perf_counter()-started,
                known=sum(v is not None for _, v, _, _ in entries),
                unknown=sum(v is None for _, v, _, _ in entries),
                knownNonzero=sum(v is not None and v > 0 for _, v, _, _ in entries))


def leakage_data(info, mode):
    N = info['N']
    active = []
    for n, value, reason, p in info['entries']:
        if mode == 'local-subtraction' and value is not None:
            continue
        if mode == 'rough-euler' and (p or value == 0):
            continue
        delta = n-N
        relative_log = math.log1p(delta/N)
        # Global M(n)<=log(n)^2/2 for n>=2. The coefficient has at
        # most two prime-power legs; all other support is zero.
        bound = 0.5*math.log(n)**2
        active.append((N*relative_log, bound*math.exp(-SIGMA*relative_log)))
    return np.array(active, dtype=float).reshape((-1, 2))


def leakage(info, H_over_N, data):
    N, D = info['N'], info['window']
    near = float(np.sum(data[:, 1]*np.exp(-0.5*(H_over_N*data[:, 0])**2)))
    far_log_gap = N*math.log1p((D+1)/N)
    far_log = SIGMA*math.log(N)+2*math.log(z_bound(SIGMA)) - \
              0.5*(H_over_N*far_log_gap)**2
    far = math.exp(far_log) if far_log > -745 else 0.0
    return near+far


def parameters(info, error, mode):
    started = time.perf_counter()
    data = leakage_data(info, mode)
    budget = error/4
    H_over_N = optimize.brentq(lambda h: leakage(info, h, data)-budget,
                              1e-6, 100.0, xtol=1e-12)
    N = info['N']
    H = N*H_over_N
    options = []
    for a in (0.125, 0.25, 0.5, 0.75):
        numerator = (N**(SIGMA-a)*z_bound(SIGMA-a)**2 +
                     N**(SIGMA+a)*z_bound(SIGMA+a)**2)*math.exp(a*a/(2*H*H))
        h = 2*math.pi*a/math.log1p(numerator/(error/16))
        options.append((h, a))
    h, a = max(options)
    target_T = H*math.sqrt(2*math.log(16*N**SIGMA*z_bound(SIGMA)**2/error))
    K = math.ceil(target_T/h)+1
    T = (K-1)*h
    return dict(H=H, H_over_N=H_over_N, step=h, samples=K,
                T=T, strip=a, leakage=leakage(info,H_over_N,data),
                analyticAliasBudget=error/16,
                analyticTailBound=N**SIGMA*z_bound(SIGMA)**2*
                    math.erfc(T/(math.sqrt(2)*H)),
                unknownNearestOffset=min((abs(n-N) for n,v,_,_ in info['entries']
                                          if v is None), default=None),
                parameterSeconds=time.perf_counter()-started)


def finite_zeta_fft(sigma, step, K, m):
    """NUFFT by real gridding and a fixed Taylor expansion; no primes."""
    L = fft.next_fast_len(2*K, real=True)
    numbers = np.arange(1, m, dtype=float)
    logs = np.log(numbers)
    angles = step*logs
    bins = np.rint(L*angles/(2*math.pi)).astype(np.int64)
    delta = angles-2*math.pi*bins/L
    bins %= L
    base = numbers**(-sigma)
    zeta = np.zeros(K, dtype=complex)
    derivative = np.zeros(K, dtype=complex)
    multiplier = np.ones(K, dtype=complex)
    scaled = K*delta
    coefficients = np.ones(m-1)
    output_order = -1j*np.arange(K)/K
    for r in range(FFT_ORDER+1):
        weighted = base*coefficients
        bins_z = np.bincount(bins, weights=weighted, minlength=L)
        bins_d = np.bincount(bins, weights=-logs*weighted, minlength=L)
        zeta += multiplier*fft.rfft(bins_z, workers=1)[:K]
        derivative += multiplier*fft.rfft(bins_d, workers=1)[:K]
        coefficients *= scaled/(r+1)
        multiplier *= output_order
    return zeta, derivative, L


def zeta_grid(par):
    K, step, T = par['samples'], par['step'], par['T']
    m = max(64, math.ceil(T/2))
    zeta, derivative, fft_length = finite_zeta_fft(SIGMA, step, K, m)
    s = SIGMA+1j*step*np.arange(K)
    log_m = math.log(m)
    m_to_minus_s = np.exp(-s*log_m)
    first = m*m_to_minus_s/(s-1)
    second = 0.5*m_to_minus_s
    zeta += first+second
    derivative += first*(-log_m-1/(s-1))-log_m*second
    rising, inverse_sum = s.copy(), 1/s
    # Scale the rising factorial as it grows, avoiding giant intermediates.
    scaled_rising = rising/m
    for r, bern in enumerate(BERNOULLI, start=1):
        # scaled_rising already includes m^(-(2*r-1)).
        term = bern*m_to_minus_s*scaled_rising
        zeta += term
        derivative += term*(inverse_sum-log_m)
        scaled_rising *= (s+2*r-1)*(s+2*r)/m**2
        inverse_sum += 1/(s+2*r-1)+1/(s+2*r)
    return zeta, derivative, dict(integerEndpoint=m, fftLength=fft_length)


def extract(info, error, mode='local-subtraction', max_nodes=1500000):
    started = time.perf_counter()
    par = parameters(info, error, mode)
    if par['samples'] > max_nodes:
        return dict(skipped=True, reason='explicit-node-cap', parameters=par)
    zeta, derivative, details = zeta_grid(par)
    t = par['step']*np.arange(par['samples'])
    response = (-derivative/zeta)**2
    if mode == 'rough-euler':
        # Comparator only: this is the older per-frequency Euler deletion.
        Z = -derivative/zeta
        for p in primerange(2, info['cutoff']+1):
            Z -= math.log(int(p))/np.expm1((SIGMA+1j*t)*math.log(int(p)))
        response = Z**2
    weights = np.exp(1j*t*math.log(info['N'])-0.5*(t/par['H'])**2)
    real = (response*weights).real
    measured = info['N']**SIGMA*par['step']/(math.sqrt(2*math.pi)*par['H'])*\
               (real[0]+2*float(np.sum(real[1:])))
    known_subtraction = 0.0
    if mode == 'local-subtraction':
        for n,value,_,_ in info['entries']:
            if value is not None and value != 0:
                relative = math.log1p((n-info['N'])/info['N'])
                known_subtraction += value*math.exp(-SIGMA*relative-
                                                   0.5*(par['H']*relative)**2)
    corrected = measured-known_subtraction
    measurement_seconds = time.perf_counter()-started
    # Independent point checks use neither target nor neighbouring factors.
    mp.mp.dps = 45
    point_errors = []
    for index in sorted(set((0,1,par['samples']//3,par['samples']-1))):
        ss = mp.mpc(SIGMA, float(t[index]))
        zz = mp.zeta(ss)
        dz = mp.diff(mp.zeta, ss)
        point_errors.append(dict(index=index,
                                 zeta=float(abs(complex(zz)-zeta[index])),
                                 derivative=float(abs(complex(dz)-derivative[index]))))
    return dict(skipped=False, mode=mode, error=error, parameters=par, **details,
                rawCoefficient=measured, knownSubtraction=known_subtraction,
                measuredCoefficient=corrected, measurementSeconds=measurement_seconds,
                independentPointErrors=point_errors,
                floatingRoundoffCertified=False, factorOracleUsed=False)


def factor_sum_interval(N, measured, error):
    """The sum coordinate stays well conditioned even near equal factors.

    x=sqrt(N)*cosh(eta), eta^2=log(N)^2/4-M/2.
    Pad integer endpoints against ordinary floating evaluation error;
    this is an experimental interval, not a rigorous rounding certificate.
    """
    total = math.log(N)
    lo, hi = max(0,measured-error), min(total*total/2,measured+error)
    if lo > hi:
        return None
    xlo = math.sqrt(N)*math.cosh(math.sqrt(max(0,total*total/4-hi/2)))
    xhi = math.sqrt(N)*math.cosh(math.sqrt(max(0,total*total/4-lo/2)))
    lower = max(math.isqrt(N)+(math.isqrt(N)**2<N), math.ceil(xlo)-2)
    upper = min((N+1)//2, math.floor(xhi)+2)
    return lower, upper


def modular_candidates(N, lower, upper):
    """CRT wheel generation, followed by further exact small-modulus masks."""
    residues, modulus = [0], 1
    for ell in MODULI[:5]:
        if N % ell == 0:
            return [], ell
        squares = {(a*a)%ell for a in range(ell)}
        allowed = [a for a in range(ell) if (a*a-N)%ell in squares]
        inverse = pow(modulus, -1, ell)
        residues = [v+modulus*((a-v)*inverse % ell)
                    for v in residues for a in allowed]
        modulus *= ell
    extra = [(ell, {(a*a)%ell for a in range(ell)}) for ell in MODULI[5:]]
    candidates = []
    for v in residues:
        first = lower+(v-lower)%modulus
        for x in range(first, upper+1, modulus):
            if all((x*x-N)%ell in squares for ell,squares in extra):
                candidates.append(x)
    return sorted(candidates), None


def recover(N, measured, error):
    started = time.perf_counter()
    interval = factor_sum_interval(N, measured, error)
    if interval is None:
        return dict(success=False, reason='empty-observable-interval')
    lower, upper = interval
    if upper-lower > 2000000:
        return dict(success=False, reason='explicit-candidate-window-cap',
                    interval=[lower,upper])
    candidates, direct = modular_candidates(N, lower, upper)
    found = None
    if direct:
        found = (direct,N//direct)
    else:
        for x in candidates:
            difference = x*x-N
            root = math.isqrt(difference)
            if root*root == difference:
                p, q = x-root, x+root
                if 1<p<N and p*q==N and N%p==0:
                    found=(p,q)
                    break
    return dict(success=found is not None, factors=found,
                exactDivisionVerified=found is not None and N%found[0]==0,
                interval=[lower,upper], rawCandidates=upper-lower+1,
                modularCandidates=len(candidates),
                recoverySeconds=time.perf_counter()-started)


def reference(N):
    """Post-measurement validation/baseline. Never called by extractor."""
    from sympy import factorint
    from sympy.ntheory.factor_ import factor_cache
    times=[]
    for _ in range(15):
        factor_cache.cache_clear()
        start=time.perf_counter(); factors=factorint(N); times.append(time.perf_counter()-start)
    if len(factors)!=2 or any(e!=1 for e in factors.values()):
        raise ValueError('Reference input is not a distinct-prime semiprime')
    p,q=sorted(map(int,factors))
    return dict(factors=[p,q], coefficient=2*math.log(p)*math.log(q),
                freshSympyMedianSeconds=statistics.median(times))


def generated_inputs(bits, count, seed):
    rng=random.Random(seed)
    result=[]
    while len(result)<count:
        lo,hi=2**(bits-1),2**bits-1
        p=int(rng.randrange(max(11,math.isqrt(lo)//2),math.isqrt(hi)))|1
        q=int(rng.randrange(max(p+2,(lo+p-1)//p),hi//p+1))|1
        if p*q<lo or p*q>hi or not isprime(p) or not isprime(q):
            continue
        if not 1.3<q/p<3.0 or p*q in result:
            continue
        result.append(p*q)
    return result


def forecast():
    rows=[]
    for bits in (16,24,32,40):
        for N in generated_inputs(bits,4,20261002+bits):
            for cutoff,window in ((7,128),(31,512),(127,1024)):
                info=local_information(N,cutoff,window)
                if info['directFactor']:
                    rows.append(dict(N=N,bits=bits,cutoff=cutoff,window=window,
                                     directFactorFound=True,preprocessingSeconds=info['seconds']))
                    continue
                for precision in ('single-candidate-scale','coarse-budget'):
                    eps=(0.25 if precision=='single-candidate-scale' else 64)/math.sqrt(N)
                    base=parameters(info,eps,'unfiltered')
                    partial=parameters(info,eps,'local-subtraction')
                    rough=parameters(info,eps,'rough-euler')
                    rows.append(dict(N=N,bits=bits,cutoff=cutoff,window=window,
                                     precision=precision,error=eps,
                                     preprocessingSeconds=info['seconds'],knownAliases=info['known'],
                                     knownNonzeroAliases=info['knownNonzero'],unknownAliases=info['unknown'],
                                     unfiltered=base,localSubtraction=partial,roughEuler=rough,
                                     predictedGridReduction=base['samples']/partial['samples'],
                                     largeGridExecuted=False))
    return rows


def validate_local_classifier():
    from sympy import factorint
    checked=0
    for n in range(2,8193):
        p=next((p for p in (2,3,5,7,11,13,17,19,23,29,31) if n%p==0),None)
        if p is None:
            continue
        actual=coefficient_from_one_factor(n,p)
        fs=factorint(n)
        if len(fs)==1:
            q,e=next(iter(fs.items())); expected=(e-1)*math.log(int(q))**2
        elif len(fs)==2:
            q,r=fs;expected=2*math.log(int(q))*math.log(int(r))
        else:
            expected=0.0
        assert abs(actual-expected)<1e-10
        checked+=1
    return dict(independentSmallIntegerChecks=checked,allPassed=True,
                referenceFactorisationOnlyInValidation=True)


def experiment():
    inputs=[323,899,2021,*generated_inputs(12,3,20261002)]
    rows=[]
    for N in inputs:
        info=local_information(N,7,256)
        assert info['directFactor'] is None
        for eps in (0.0002,0.02,0.2):
            result=extract(info,eps)
            if not result['skipped']:
                result['recovery']=recover(N,result['measuredCoefficient'],eps)
            rows.append(dict(N=N,preprocessingSeconds=info['seconds'],knownAliases=info['known'],
                             knownNonzeroAliases=info['knownNonzero'],unknownAliases=info['unknown'],
                             **result))
    # Measurement is now complete. Only now request labels for validation.
    refs={N:reference(N) for N in inputs}
    for row in rows:
        ref=refs[row['N']]
        row['reference']=ref
        if not row['skipped']:
            row['observedCoefficientError']=abs(row['measuredCoefficient']-ref['coefficient'])
            row['withinWorkingAllowance']=row['observedCoefficientError']<=row['error']
            row['totalSeconds']=row['preprocessingSeconds']+row['measurementSeconds']+\
                                row['recovery'].get('recoverySeconds',0)
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--forecast-only',action='store_true')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    report=dict(schemaVersion=1,seed=20261002,sideInvestigation=True,
                numericalCertificate=False,newFactoringComplexityProved=False,
                ordinaryBuildOrCIIntegration=False,constantThreadCount=1,
                localClassifierValidation=validate_local_classifier(),
                forecast=forecast(),
                measurements=[] if args.forecast_only else experiment(),
                evidenceLimits=[
                    'Large-input bandwidths are parameter forecasts, not executed zeta grids.',
                    'Analytic envelopes do not certify accumulated floating-point/FFT error.',
                    'Modular rejection is classical hyperbolic/Fermat sieving, not claimed novel.',
                    'Factoring references are used only after measurement or inside explicit validation.',
                    'No arbitrary-neighbour factorisations are assumed free.',
                ])
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
    print(json.dumps(dict(output=str(args.output),forecastRows=len(report['forecast']),
                         measurements=len(report['measurements']),
                         recovered=sum(r.get('recovery',{}).get('success',False)
                                       for r in report['measurements']))))


if __name__=='__main__':
    main()
