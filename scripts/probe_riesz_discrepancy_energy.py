#!/usr/bin/env python3
"""Optional actual-prime diagnostics for the coupled Riesz discrepancy.

This checks finite identities and measures signed discrepancy energy. The
prime logarithms here are BELOW the proved but unevaluated eventual start.
Quadrature and floating point are exploratory, never certificates or CI.
The signed smooth Riesz response is measured separately, not assumed paid.
"""
import json
import math

import numpy as np

from probe_riesz_prime_tail_energy import primes_to


def mu_divisors(prime_factors):
    result = [(1, 1)]
    for p in prime_factors:
        result += [(d*p, -sign) for d, sign in result]
    return result


def run(primes, periods, order, phase, length):
    a, y = 10., 54.
    b = a+periods*2*math.pi/y
    ps = primes[(primes > math.exp(a)) & (primes <= math.exp(b))]
    logs = np.log(ps)
    cs = np.exp(-logs/2)*logs**order*np.cos(y*(logs+phase))/ps
    prefix0 = np.r_[0., np.cumsum(cs)]
    prefix1 = np.r_[0., np.cumsum(cs*logs)]
    nodes, weights = np.polynomial.legendre.leggauss(32)

    def integrate(lo, hi, power):
        if hi <= lo:
            return 0.
        pieces = max(1, math.ceil((hi-lo)*y/(2*math.pi)))
        widths = (hi-lo)/pieces
        xs = lo+np.arange(pieces)[:, None]*widths+(nodes[None, :]+1)*widths/2
        values = np.exp(-xs/2)*xs**power*np.cos(y*(xs+phase))
        return float(widths/2*np.sum(values @ weights))

    smooth0 = integrate(a, b, order-1)
    smooth1 = integrate(a, b, order)

    def profiles(ds):
        ds = np.maximum(ds, 0.)
        idx = np.searchsorted(logs, ds, side='right')
        actual = prefix1[idx]+ds*(prefix0[-1]-prefix0[idx])
        smooth = ds*smooth0
        smooth[ds >= b] = smooth1
        for i in np.flatnonzero((ds > a) & (ds < b)):
            d = ds[i]
            smooth[i] = integrate(a, d, order)+d*integrate(d, b, order-1)
        return actual, smooth

    r = math.floor(math.exp(length))
    ks = np.arange(1, r+2, dtype=float)
    actual, smooth = profiles(length-np.log(ks))
    err = actual-smooth
    energy = float(np.arange(1, r+1) @ np.diff(err)**2)
    pairs = []
    for factors in [[2, 3], [2, 3, 5], [3, 5, 7], [2, 3, 5, 7]]:
        n = math.prod(factors)
        divisors = mu_divisors(factors)
        prime_value = math.fsum(sign*actual[d-1] for d, sign in divisors if d <= r)
        smooth_value = math.fsum(sign*smooth[d-1] for d, sign in divisors if d <= r)
        # Finite Abel identity, with all boundary jumps included.
        jumps = np.zeros(r+1)
        for d, sign in divisors:
            if d <= r:
                jumps[d-1] += sign
        partial = np.cumsum(jumps)[:r]
        via_increment = float(-np.diff(err) @ partial)
        assert math.isclose(prime_value-smooth_value, via_increment,
                            rel_tol=2e-8, abs_tol=2e-9)
        pairs.append(dict(n=n, count=len(factors), literalPrimeResponse=prime_value,
                          signedSmoothResponse=smooth_value,
                          discrepancy=prime_value-smooth_value,
                          exactAbelResidual=prime_value-smooth_value-via_increment))
    w = min(math.exp(-a/2)*b**order, math.exp(-order)*(2*order)**order)
    score = abs(order/a-.5)+order*(b-a)/a**2
    cap = 5*w*(2+(score+abs(y)+2)*(b-a))/a**3
    return dict(periods=periods, order=order, phase=phase, rieszLength=length,
                primeCount=len(ps), retainedDivisorCutoffs=r,
                signedFullMomentError=float(prefix0[-1]-smooth0),
                exactDiscreteDiscrepancyEnergy=energy,
                eventualEnergyFormula=b*cap**2,
                formulaIsCertifiedAtThisHeight=False, cofactorResponses=pairs)


if __name__ == '__main__':
    primes = primes_to(math.ceil(math.exp(12.)))
    result = dict(scope=__doc__.strip(),
                  cases=[run(primes, periods, order, phase, length)
                         for periods, order, phase, length in
                         [(1, 0, 0., 12.), (4, 1, .37, 12.),
                          (16, 5, 0., 11.5), (16, 5, 0., 12.),
                          (16, 5, 0., 13.), (16, 5, .37, 12.)]])
    print(json.dumps(result, indent=2))
