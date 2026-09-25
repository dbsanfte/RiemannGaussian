#!/usr/bin/env python3
"""Optional numerical audit of the literal joint least-order boundary.

The finite-prime regression is deliberately sparse, and all reported
transcendental values are floating point. It verifies neither the full
prime sum nor asymptotic cancellation. Do not run this in ordinary CI.
The uniform arithmetic overflow estimate is proved separately in Lean.
"""
import argparse
import itertools
import json
import math
from pathlib import Path

import numpy as np
from scipy.special import gammaln
from scipy.stats import binom

from probe_riesz_joint_masked import rectangle_values


def lucas_lehmer(exponent):
    if exponent == 2:
        return True
    modulus = 2**exponent - 1
    value = 4
    for _ in range(exponent - 2):
        value = (value * value - 2) % modulus
    return value == 0


def lower_and_overflow(n, largest, least):
    """Sum the exact binomial marginals; no normal approximation."""
    orders = np.arange((21*n+39)//40, 23*n//40+1)
    marginal = binom.pmf(orders, n+1, largest)
    remaining = n+1-orders
    lower = max(0, (n+99)//100-1)
    upper = n//25-1
    conditional = least/(1-largest)
    return (float(np.sum(marginal*binom.sf(lower-1, remaining, conditional))),
            float(np.sum(marginal*binom.sf(upper, remaining, conditional))))


def encode(value):
    return [float(value.real), float(value.imag)]


def finite_regression(n=328, height=60):
    exponents = [17, 19, 31, 61, 89, 107, 127, 521]
    assert all(lucas_lehmer(e) for e in exponents)
    primes = [2**e-1 for e in exponents]
    logs = [math.log(p) for p in primes]
    u = 10001/20000
    physical = 20000**n//(10001**n*(n+1))+2
    length = 2*math.log(physical)
    labels = []
    for flags in itertools.product((0, 1), repeat=len(primes)):
        indices = [i for i, flag in enumerate(flags) if flag]
        if not 3 <= len(indices) <= 55:
            continue
        total = math.fsum(logs[i] for i in indices)
        if not 1.95*n < total <= 2.03*n:
            continue
        if not all(n*n < primes[i] and logs[i] < length for i in indices):
            continue
        if not .5 < logs[max(indices)]/total < .6:
            continue
        if not .005 < logs[min(indices)]/total < .06:
            continue
        riesz = math.fsum((-1)**sum(bits)*max(0, length-math.fsum(
            logs[i]*bit for i, bit in zip(indices, bits)))
            for bits in itertools.product((0, 1), repeat=len(indices)))
        exponent = (n+1)*math.log(u)+n*math.log(total)-gammaln(n+1)-1.5*total
        labels.append((indices, total, riesz, exponent))
    assert labels
    scale = max(row[3] for row in labels)
    direct = lower = short = long = 0j
    mass_error = 0.0
    by_count = {}
    for indices, total, riesz, exponent in labels:
        scalar = -total/length*riesz*np.exp(exponent-scale-1j*height*total)
        minimum = min(indices)
        rectangle_mass = lower_mass = overflow_mass = 0.0
        for index in indices:
            if index == minimum:
                continue  # Exact same-prime exclusion, not a floating zero.
            p, r = logs[index]/total, logs[minimum]/total
            rect = float(rectangle_values(n, np.array([p]), np.array([r]))[0])
            low, over = lower_and_overflow(n, p, r)
            mass_error = max(mass_error, abs(rect-low+over))
            rectangle_mass += rect
            lower_mass += low
            overflow_mass += over
        contribution = scalar*rectangle_mass
        direct += contribution
        lower += scalar*lower_mass
        if len(indices) < 14:
            short += scalar*overflow_mass
        else:
            long += scalar*overflow_mass
        by_count[len(indices)] = by_count.get(len(indices), 0j)+contribution
    assert mass_error < 2e-13
    error = abs(direct-lower+short+long)
    assert error < 2e-12*max(1, abs(direct), abs(lower))
    return dict(scope="Sparse finite actual-prime regression, NOT a full prime-sum bound",
                N=n, height=height, labels=len(labels), prime_exponents=exponents,
                common_log_scale_removed=scale,
                retained_masks=["squarefree", "physical", "core window", "nondominant",
                                "share interior", "count", "finite factorial rectangle",
                                "full product phase", "distinct marked slots"],
                direct_scaled=encode(direct), lower_threshold_scaled=encode(lower),
                overflow_3_to_13_scaled=encode(short), overflow_14_to_55_scaled=encode(long),
                allocation_identity_error=mass_error, signed_identity_error_scaled=error,
                counts_present={str(k): encode(v) for k, v in by_count.items()})


def rate_probe():
    u = 10001/20000
    rows = []
    for count in range(12, 21):
        m = count-1
        tilt = max(0, (.04*m-.475)/(m*(.475-.04)))
        exponent = .475*math.log1p(tilt)-.04*math.log1p(m*tilt)
        rows.append(dict(count=count, optimal_tilt=tilt, factorial_exponent=exponent,
                         ideal_source_exponent=math.log(2*u)+exponent))
    return dict(scope="Exploration of this one joint tilt, not an impossibility result",
                optimized=rows,
                proved_rational_tilt_exponent=.475*math.log(126/125)-.04*math.log(138/125),
                lean_overflow_rate=u*(262144/131071)*math.exp(-1/6000))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = dict(scope="Uncertified optional diagnostic; Lean supplies the arithmetic estimate",
                  rates=rate_probe(), finite_primes=finite_regression())
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
