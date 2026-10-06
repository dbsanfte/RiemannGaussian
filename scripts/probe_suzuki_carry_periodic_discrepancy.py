#!/usr/bin/env python3
"""Optional literal carry/Fejer discrepancy replay; not a certificate.

Rational rows are evaluated both by the original integer carry and by the
proved closed form. Complex phase tests join all three modulations and both
lag orientations before taking a norm. This does not prove any asymptotic
statement about a signed prime sum.
"""

import argparse
import cmath
import json
from fractions import Fraction
from pathlib import Path


def incidence(n, d):
    return ((2*(n+1)//d) % 2)-((2*n//d) % 2)


def amplitude(h_size, n):
    v = Fraction(n+1, h_size)
    return max(Fraction(0), min(v-1, 3-v))


def closed_discrepancy(h_size, lag):
    r = 2*h_size-lag
    return (Fraction(r*(r*r-1), 6*h_size*h_size*(2*lag+1))
            -amplitude(h_size, lag)*amplitude(h_size, 2*lag))


def direct_discrepancy(h_size, lag):
    d = 2*lag+1
    return sum((amplitude(h_size, n)*amplitude(h_size, n+lag)
                *(incidence(n, d)*incidence(n+lag, d)+Fraction(1, d))
                for n in range(3*h_size)), Fraction(0))


def rational_replay():
    rows = 0
    max_prefix = Fraction(0)
    for h_size in range(1, 33):
        for lag in range(h_size, (3*h_size-1)//2+1):
            assert direct_discrepancy(h_size, lag) == closed_discrepancy(h_size, lag)
            rows += 1
        lag, d = h_size, 2*h_size+1
        prefix = Fraction(0)
        for n in range(4*d):
            prefix += incidence(n, d)*incidence(n+lag, d)+Fraction(1, d)
            max_prefix = max(max_prefix, abs(prefix))
            assert abs(prefix) <= 1
            if (n+1) % d == 0:
                assert prefix == 0
    uniform_rows = 0
    for h_size in [100, 101, 256, 640]:
        for lag in range(h_size, 101*h_size//100+1):
            e = closed_discrepancy(h_size, lag)
            assert e == direct_discrepancy(h_size, lag)
            assert e >= Fraction(1, 20)
            uniform_rows += 1
    return {
        "exactRationalClosedFormReplays": rows,
        "uniformBandReplays": uniform_rows,
        "maximumPrefixMagnitude": str(max_prefix),
        "allPrefixAndPeriodChecksPassed": True,
    }


def joined_phase_replay():
    # A nonzero, diagonal-cancelling vector, not the canonical Mellin code.
    code = [1+2j, -3+0.5j, 2-2.5j]
    h_size, tau, lag = 17, 0.7, 18
    d = 2*lag+1
    joined = 0j
    for n in range(3*h_size):
        overlap = float(amplitude(h_size, n)*amplitude(h_size, n+lag))
        zero_mean = float(incidence(n, d)*incidence(n+lag, d)+Fraction(1, d))
        for j, c in enumerate(code):
            theta = j*tau/h_size
            joined += c*overlap*(cmath.exp(-1j*theta*lag)
                                +cmath.exp(1j*theta*lag))*zero_mean
    symbol = sum(c*cmath.cos(j*tau*lag/h_size) for j, c in enumerate(code))
    predicted = 2*symbol*float(closed_discrepancy(h_size, lag))
    residual = abs(joined-predicted)
    assert residual < 1e-12
    return {
        "allThreeModulationsAndBothOrientationsJoined": True,
        "genericVectorNotClaimedCanonicalPoleCode": True,
        "floatingJoinedIdentityResidual": residual,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/suzuki-carry-periodic-discrepancy/probe.json"))
    args = parser.parse_args()
    report = {
        "scope": "Optional literal finite regression, not an asymptotic certificate",
        "rationalReplay": rational_replay(),
        "joinedPhaseReplay": joined_phase_replay(),
        "diagonalScale": [
            {"H": h_size, "exactDiscrepancy": str(closed_discrepancy(h_size, h_size)),
             "discrepancy": float(closed_discrepancy(h_size, h_size)),
             "H_times_discrepancy": h_size*float(closed_discrepancy(h_size, h_size))}
            for h_size in [16, 100, 256, 640, 4096, 65536, 1048576]
        ],
        "provedLimitInLean": "1/12",
        "cofinalDeterminantNonvanishingCertified": False,
        "signedPrimeSumSmallnessCertified": False,
        "numericalCertificate": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
