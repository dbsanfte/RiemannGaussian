#!/usr/bin/env python3
"""Floating finite-field preflight; never an input to a Lean proof.

The prime-field character models test the coupled identities in
QuasiRHCoupledResidueAudit.lean. They do not approximate the complete low
probe, its physical masks, Eisenstein angular phases, or a zeta-zero signal.
"""

import cmath
import json
import math
from pathlib import Path


def prime_factors(n):
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(q):
    factors = prime_factors(q - 1)
    return next(g for g in range(2, q) if all(pow(g, (q - 1) // r, q) != 1 for r in factors))


def run(q):
    assert q % 6 == 1 and all(q % d for d in range(2, math.isqrt(q) + 1))
    g = primitive_root(q)
    chi = [0j] * q
    x = 1
    for k in range(q - 1):
        chi[x] = cmath.exp(2j * math.pi * (k % 6) / 6)
        x = x * g % q
    additive = [
        sum(chi[z] * cmath.exp(-2j * math.pi * ((m * z) % q) / q) for z in range(q))
        for m in range(q)
    ]
    base_gauss = sum(chi[z] * cmath.exp(2j * math.pi * z / q) for z in range(q))
    rows = []
    for e in range(12):
        # Even the principal multiplicative character is zero at the nonunit.
        phi = [0j] + [chi[m] ** e for m in range(1, q)]
        joined = sum(phi[m] * additive[m] for m in range(q)) / (q * math.sqrt(q))
        expected = ((q - 1) / q) * chi[q - 1] * base_gauss / math.sqrt(q) if e % 6 == 1 else 0j
        error = abs(joined - expected)
        assert error < 1e-10, (q, e, error)
        rows.append({"completedValuation": e, "matching": e % 6 == 1,
                     "normalizedJoinedNorm": abs(joined), "identityError": error})
    # A nonsymmetric mask and complex phase are kept inside the joined sum.
    weights = [cmath.exp(-54j * math.log(1 + m)) * (1 - m / q) for m in range(q)]
    literal = sum(weights[m] * chi[m] * additive[m] for m in range(q))
    expected = chi[q - 1] * base_gauss * sum(weights[1:])
    weighted_error = abs(literal - expected)
    assert weighted_error < 1e-9
    return {"q": q, "primitiveRoot": g, "separateResidueMeanNorm": abs(sum(chi)) / q,
            "separateAdditiveMeanNorm": abs(sum(additive)) / (q * math.sqrt(q)),
            "matchingNormExact": 1 - 1 / q, "valuationRows": rows,
            "complexMaskedIdentityError": weighted_error}


def main():
    rows = [run(q) for q in [7, 13, 19, 31, 37, 73, 109, 193]]
    payload = {"proofInput": False, "scope": "finite-field model only; not a full-probe estimate",
               "rows": rows}
    output = Path(".lake/quasi-rh-coupled-residue/probe.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2) + "\n")
    print("q  separate-row means (norms)  matching joined norm")
    for row in rows:
        print(f"{row['q']:3}  {row['separateResidueMeanNorm']:.2e}, "
              f"{row['separateAdditiveMeanNorm']:.2e}  {row['matchingNormExact']:.8f}")
    print("All 96 valuation identities and eight masked identities agree numerically.")
    print("These floating checks are not proof inputs.")


if __name__ == "__main__":
    main()
