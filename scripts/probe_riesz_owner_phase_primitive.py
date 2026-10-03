#!/usr/bin/env python3
"""Optional finite-primitive regression for the complete-window phase bound.

Integer rows are toys, not native core rows. Continuous cases use the exact
old factorial selector and literal core endpoints; they do not include the
arithmetic counting measure or density scalar. No result is certified by
this floating probe, and this script is outside builds/CI.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import numpy as np
from scipy.stats import binom


def finite_tail(order, damping, value):
    total = term = mp.mpc(1)
    for h in range(1, order+1):
        term *= (order-h+1)/(damping*value)
        total += term
    return total


def boundary(N, c, height, u, T, terms=40):
    """Full signed old-owner primitive, summing slots before taking norms.

    The stated tail bound controls only the omitted finite primitive series;
    floating-roundoff/underflow is not interval-certified.
    """
    n = N+1
    z = complex(.5, -float(height))
    v = float(T-c)
    k = np.arange(N//5+2, 13*N//32+1, dtype=np.float64)
    weights = binom.pmf(k, n, float((T-c)/T))
    term = np.ones(k.size, dtype=np.complex128)
    slots = term.copy()
    full = full_term = 1.+0j
    for h in range(1, terms):
        full_term *= (n-h+1)/(z*float(T)) if h <= n else 0.
        full += full_term
        term *= np.maximum(k-h+1, 0.)/(z*v)
        slots += term
    joined = full-complex(np.dot(weights, slots))
    radial = mp.exp(n*mp.log(u)+n*mp.log(T)-T/2-mp.loggamma(N+1))
    result = radial*mp.exp(1j*height*T)*mp.mpc(joined)/mp.mpc(z)
    r0, r1 = n/abs(z*float(T)), (13*N//32)/abs(z*v)
    assert r0 < .1 and r1 < .1
    tail = (r0**terms/(1-r0) if n >= terms else 0.) + \
           (r1**terms/(1-r1) if 13*N//32 >= terms else 0.)
    return result, radial*tail/abs(z)


def continuous_cases():
    mp.mp.dps = 80
    u, y = mp.mpf(10001)/20000, mp.mpf(54)
    cases = []
    for N in (256, 4096, 65536, 262144, 1048576):
        for slope in ('1.025', '1.10', '1.25', '1.30'):
            c = mp.mpf(slope)*N
            a, b = mp.mpf(39)/20*N, mp.mpf(203)/100*N
            lo, elo = boundary(N, c, y, u, a)
            hi, ehi = boundary(N, c, y, u, b)
            value = lo-hi
            endpoint_bound = mp.mpf(2)/27*(N+1)*u*mp.mpf(199)/50*mp.exp(-mp.mpf(N)/200000)
            sample_bound = endpoint_bound+2*u*(N+1)*(2*(N+1)+3+abs(y))*mp.exp(-mp.mpf(N)/4)
            assert abs(value) <= endpoint_bound+elo+ehi
            cases.append(dict(N=N, ownerLogSlope=slope, height=54,
                sourceScaledSignedIntegralReal=float(mp.re(value)),
                sourceScaledSignedIntegralNorm=float(abs(value)),
                analyticEndpointUpperBound=float(endpoint_bound),
                analyticIntegerSamplingUpperBound=float(sample_bound),
                omittedPrimitiveSeriesTailOnly=float(elo+ehi),
                floatingNotIntervalCertified=True, densityScalarIncluded=False,
                literalArithmeticCountingMasksIncluded=False, wholeFloorCertified=False))
    return cases


def integer_toys():
    mp.mp.dps = 80
    N, M, X, p = 32, 5000, 10000, 100003
    c, u = mp.log(p), mp.mpf(10001)/20000
    axis = np.arange(M+1, X+1)
    logs = np.log(axis)
    total = float(c)+logs
    k = np.arange(N//5+2, 13*N//32+1)
    owner = 1-binom.pmf(k[:, None], N+1, (logs/total)[None, :]).sum(axis=0)
    radial = np.exp(-total/2)*total**(N+1)/math.factorial(N)
    cases = []
    for height in (54., 65., 100.):
        sampled = float(u**(N+1))*float(np.sum(owner*radial*np.cos(height*total)/axis))
        z = mp.mpc(.5, -height)
        def exact_endpoint(T):
            v = T-c
            allocation = sum(mp.binomial(N+1, int(j))*(c/T)**(N+1-int(j))*(v/T)**int(j)*
                             finite_tail(int(j), z, v) for j in k)
            return u**(N+1)*mp.exp(-z*T)*T**(N+1)/mp.factorial(N)/z*\
                (finite_tail(N+1, z, T)-allocation)
        integral = exact_endpoint(c+mp.log(M))-exact_endpoint(c+mp.log(X))
        error = abs(sampled-float(mp.re(integral)))
        cap = u**(N+1)*(N+1)*2**(N+1)
        bound = (X-M)*(2*(N+1)+2+height)*cap/M**2
        assert error <= bound
        cases.append(dict(N=N, M=M, X=X, owner=p, height=height,
            sourceScaledSignedIntegerWeight=sampled,
            sourceScaledSignedIntegralReal=float(mp.re(integral)),
            samplingError=error, provedSamplingErrorUpperBound=float(bound),
            finitePrimitiveOrdersAllRetained=True, originalCoreWindow=False,
            nativeFloorCertificate=False, fullWindowGeometricTheoremApplied=False))
    return cases


def least_tag_regression():
    """Exact finite incidence check, including several small primes.

    This is a combinatorial toy only. It does not instantiate the core,
    physical N² cutoff, counting geometry, or a native floor theorem.
    """
    small, retained = (2, 3, 5, 7), (3, 5, 7)
    selected = multiple = 0
    counts = {}
    exact_one_value = label_value = 0
    for a in range(81, 2001):
        value, factors, squarefree = a, [], True
        divisor = 2
        while divisor*divisor <= value:
            if value % divisor == 0:
                exponent = 0
                while value % divisor == 0:
                    exponent += 1
                    value //= divisor
                factors.append(divisor)
                squarefree &= exponent == 1
            divisor += 1
        if value > 1:
            factors.append(value)
        if not squarefree or len(factors) < 2:
            continue
        active = [r for r in retained if a % r == 0 and
                  all(a % q != 0 for q in small if q < r)]
        eligible = [q for q in small if a % q == 0]
        expected = [min(eligible)] if eligible and min(eligible) in retained else []
        assert active == expected and len(active) <= 1
        # Exact integer regression for the entire joined weighted partition.
        weight = a*a+3*a+1
        exact_one_value += sum(weight for _ in active)
        label_value += weight if expected else 0
        if active:
            selected += 1
            multiple += len(eligible) > 1
            omega = len(factors)+1  # include the distinct large owner
            counts[omega] = counts.get(omega, 0)+1
    assert exact_one_value == label_value and multiple > 0
    return dict(smallPrimeSet=list(small), retainedTags=list(retained),
        cofactorLower=80, cofactorUpper=2000, selectedLabels=selected,
        selectedWithSeveralSmallPrimes=multiple, wholePrimeCountHistogram=counts,
        repeatedLabelCount=0, exactJoinedIntegerWeightedPartition=True,
        nativeOrCoreGeometryApplied=False, wholeFloorCertified=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-owner-phase/probe.json'))
    args = parser.parse_args()
    report = dict(schemaVersion=1, continuousCases=continuous_cases(), integerToys=integer_toys(),
        leastTagRegression=least_tag_regression(),
        source=dict(path=str(Path(__file__).resolve()),
            sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),
        scope=dict(optionalOutsideBuildsAndCI=True, floatingNotIntervalCertified=True,
            exactOldOwnerOrdersRetained=True, fullRadialVariableAndPhaseRetained=True,
            positiveInteriorEnvelopeAvoided=True, originalWholeCarrierCertified=False,
            cofinalFloorCertifiedByProbe=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    for case in report['continuousCases']+report['integerToys']:
        print(json.dumps(case), flush=True)
    print(json.dumps(report['leastTagRegression']), flush=True)


if __name__ == '__main__':
    main()
