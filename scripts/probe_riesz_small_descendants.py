#!/usr/bin/env python3
"""Optional insertion-mass diagnostic; no prime-density replacement.

The inserted primes are enumerated exactly. The base triple has model
logarithms 2N/3, not asserted to be logarithms of actual distinct primes.
Floating arithmetic and this special base preclude a certified bound.
Composite insertions cancel algebraically once all pair cutoffs saturate.
"""
import json
import math
from pathlib import Path

import numpy as np
from scipy.stats import binom

from probe_riesz_joint_core import length


def primes_to(x):
    sieve = np.ones(x + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, math.isqrt(x) + 1):
        if sieve[p]:
            sieve[p*p::p] = False
    return np.flatnonzero(sieve)


def allocation(N, shares):
    return sum(binom.cdf(13*N//32, N+1, 1-x)
               - binom.cdf((N+5)//5, N+1, 1-x) for x in shares)


def row(N, primes):
    a = primes[primes <= N*N]
    d = np.log(a)
    T, L = 2.*N, length(N)
    margin = L - 4*N/3 - 2*math.log(N)
    assert margin > 0
    old = 1-allocation(N, [1/3]*3)
    # The appended prime is <=N^2 and is not an intermediate owner.
    new = 1-allocation(N, [T/3/(T+d)]*3)
    base_coefficient = T/L*(T-L)
    # Exact factorial/feature modulus ratio, without density compensation.
    ratio = ((T+d)/L*d / base_coefficient * new/old
             * np.exp(N*np.log1p(d/T)-1.5*d))
    # Any literal total-log selection can only reduce this absolute budget.
    allowed = T+d <= 2.03*N
    assert np.all(allowed)
    observations = {}
    for y in (0., 54., 100.):
        signed = -np.sum(ratio * np.exp(-1j*y*d))
        observations[str(y)] = [float(signed.real), float(signed.imag)]
    return dict(N=N, inserted_primes=len(a), pair_saturation_margin=margin,
                maximal_relative_compensation=float(np.sum(ratio)),
                signed_correction_relative_to_base=observations,
                remaining_fraction_even_with_optimal_phases=float(1-np.sum(ratio)))


def main():
    orders = [640, 1536, 4096]
    primes = primes_to(max(orders)**2)
    rows = [row(N, primes) for N in orders]
    payload = dict(scope="floating actual-prime insertion probe on model base logarithms",
                   rows=rows, limitations=[
                       "The three equal base logarithms are a model, not actual prime labels.",
                       "No roundoff enclosure, no cofinal conclusion from these samples.",
                       "No population or phase transport between different base triples.",
                       "Only descendants formed by appending factors are tested; splitting or replacing large primes is not tested.",
                       "The whole signed core complement remains unpaid."])
    out = Path(__file__).resolve().parents[1]/"docs/riesz-small-descendants-probe.json"
    out.write_text(json.dumps(payload, indent=2)+"\n")
    for entry in rows:
        print(entry, flush=True)


if __name__ == "__main__":
    main()
