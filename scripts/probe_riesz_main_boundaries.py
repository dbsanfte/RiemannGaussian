#!/usr/bin/env python3
"""Optional diagnostic of the signed cofactor main; never run by ordinary CI.

Keep actual marked primes and the exact owner factorial polynomial. Replace
only the ordinary-integer cofactor sum in the DENSITY term by its elementary
integral, evaluated by an exact antiderivative formula in floating arithmetic.
Keep both radial endpoints and the p > cofactor sector boundary separately.
The latter is an artificial boundary of this diagnostic sector, not the
largest-prime boundary of the whole literal carrier.

The virtual ordinary-prime subtraction in the composite model is read from
the separately enumerated joint probe. It is NOT replaced by a prime-density
integral or asserted to be an original eligible cofactor. The resulting numbers
are not certificates, whole-core bounds, or evidence of an asymptotic rate.
All nested carrier masks and nonowner allocation are not included. In these
small-order tests the divisor cutoff only reaches 1, 2, or 3.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import time

import mpmath as mp
import numpy as np

from probe_riesz_cofactor_main import arithmetic, density
from probe_riesz_retained_factorial import unpaid_orders


ROOT = Path(__file__).resolve().parents[1]
REFERENCE = ROOT / "docs/riesz-joint-main-probe.json"


def owner_primitive(t, v, order, height):
    """Primitive in v of exp(-(1/2+iy)v) * the owner polynomial.

    I_0=-exp(-lambda*v)/lambda,
    I_k=-exp(-lambda*v)*v^k/lambda+(k/lambda)*I_(k-1).
    Hence I'_k=exp(-lambda*v)*v^k. No phase or factorial order is dropped.
    """
    lam = 0.5 + 1j * height
    exponential = np.exp(-lam * v)
    monomial_primitive = -exponential / lam
    power = np.ones(len(v))
    answer = np.zeros(len(v), dtype=complex)
    allowed = set(range(order + 2)) - set(unpaid_orders(order))
    for k in range(order + 2):
        if k:
            power *= v
            monomial_primitive = (
                -exponential * power / lam + k / lam * monomial_primitive
            )
        if k in allowed:
            answer += (
                math.comb(order + 1, k)
                * t ** (order + 1 - k)
                * monomial_primitive
            )
    return answer


def check_primitive():
    """High-precision numerical check against quadrature, not a Lean proof."""
    mp.mp.dps = 70
    checks = []
    for order, left, right in [(14, "13.7", "13.9"), (16, "15.9", "16.2")]:
        t = mp.mpf(order)
        a, b = mp.mpf(left), mp.mpf(right)
        lam = mp.mpc(mp.mpf("0.5"), 54)
        allowed = set(range(order + 2)) - set(unpaid_orders(order))

        def polynomial(v):
            return mp.fsum(
                math.comb(order + 1, k) * t ** (order + 1 - k) * v**k
                for k in allowed
            )

        def primitive(v):
            exponential = mp.exp(-lam * v)
            term = -exponential / lam
            result = 0
            for k in range(order + 2):
                if k:
                    term = -exponential * v**k / lam + k / lam * term
                if k in allowed:
                    result += math.comb(order + 1, k) * t ** (order + 1 - k) * term
            return result

        direct = mp.quad(lambda v: mp.exp(-lam * v) * polynomial(v), [a, b])
        endpoint = primitive(b) - primitive(a)
        error = abs(endpoint - direct) / max(1, abs(direct))
        if not error < mp.mpf("1e-50"):
            raise RuntimeError("Antiderivative/quadrature check failed")
        checks.append({"order": order, "relativeError": str(error)})
    return checks


def complex_record(z):
    return {"re": float(z.real), "im": float(z.imag), "abs": float(abs(z))}


def run(order, height, reference):
    started = time.monotonic()
    u = 10001 / 20000
    physical = (math.floor(u ** (-order) / (order + 1)) + 2) ** 2
    length = math.log(physical)
    lower_product = max(physical, math.floor(math.exp(1.971 * order)))
    upper_product = min(physical**2 - 1, math.floor(math.exp(2.029 * order)))
    prime, mu = arithmetic(physical)
    first_prime = math.isqrt(lower_product) + 1
    primes = np.flatnonzero(prime[first_prime:physical]) + first_prime
    lower = np.maximum(lower_product // primes, 1)
    upper = np.minimum(upper_product // primes, primes - 1)
    nonempty = lower < upper
    primes, lower, upper = primes[nonempty], lower[nonempty], upper[nonempty]
    t = np.log(primes)
    remainder_length = length - t
    cutoff = int(math.exp(float(remainder_length.max())))
    signed_density = sum(
        int(mu[d]) * density(d) * np.maximum(0.0, remainder_length - math.log(d))
        for d in range(1, cutoff + 1)
    )
    factor = (
        u ** (order + 1)
        / length
        / math.factorial(order)
        * np.exp((-1.5 - 1j * height) * t)
        * signed_density
    )
    upper_terms = factor * owner_primitive(t, np.log(upper), order, height)
    lower_terms = -factor * owner_primitive(t, np.log(lower), order, height)
    owner = upper == primes - 1
    components = {
        "lowerRadial": lower_terms.sum(),
        "upperRadial": upper_terms[~owner].sum(),
        "ownerBoundary": upper_terms[owner].sum(),
    }
    combined = sum(components.values())
    if (
        reference["markedPrimes"] != len(primes)
        or reference["shortCutoff"] != cutoff
        or reference["physicalUpper"] != physical
        or reference["y"] != height
    ):
        raise ValueError("The reference joint probe uses a different population")
    prime_subtraction = reference["sourceNormalizedPrimePart"]
    return {
        "order": order,
        "height": height,
        "physicalUpper": physical,
        "length": length,
        "markedPrimes": len(primes),
        "shortCutoff": cutoff,
        "sourceNormalizedDensityBoundaries": {
            key: complex_record(value) for key, value in components.items()
        },
        "sourceNormalizedIntegratedDensity": complex_record(combined),
        "sourceNormalizedDiscreteDensity": reference["sourceNormalizedDensityPart"],
        "discreteMinusIntegratedDensityReal": (
            reference["sourceNormalizedDensityPart"] - combined.real
        ),
        "sourceNormalizedExactPrimeSubtractionReal": prime_subtraction,
        "ownerBoundaryPlusPrimeSubtractionReal": (
            components["ownerBoundary"].real + prime_subtraction
        ),
        "sourceNormalizedIntegratedJointMainReal": combined.real + prime_subtraction,
        "sourceNormalizedDiscreteJointMainReal": reference["sourceNormalizedSignedMain"],
        "allOriginalMasksVerified": False,
        "nonownerAllocationIncluded": False,
        "asymptoticBoundProved": False,
        "certified": False,
        "seconds": time.monotonic() - started,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-order", type=int, choices=[14, 16, 18], default=16)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    checks = check_primitive()
    if args.check_only:
        print(json.dumps(checks, indent=2))
        return
    reference_bytes = REFERENCE.read_bytes()
    references = {row["N"]: row for row in json.loads(reference_bytes)["rows"]}
    print(json.dumps({
        "scope": __doc__.strip(),
        "reference": str(REFERENCE.relative_to(ROOT)),
        "referenceSha256": hashlib.sha256(reference_bytes).hexdigest(),
        "quadratureChecks": checks,
        "rows": [run(n, 54.0, references[n]) for n in [14, 16, 18] if n <= args.max_order],
    }, indent=2))


if __name__ == "__main__":
    main()
