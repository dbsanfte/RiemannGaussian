#!/usr/bin/env python3
"""Optional ceiling regression: join algebra BEFORE numerical inspection.

Exact rational coefficient checks, finite genuine-prime identity replays,
and labelled constant-array source tests. No population estimate, cofinal
certificate, independent 42/25 ceiling, or zero exclusion is inferred.
The moving length retains its literal integer floor and added two.
"""
import argparse
from fractions import Fraction as F
import itertools
import json
from pathlib import Path

from flint import fmpz
import mpmath as mp


def encode(z):
    return {"re": mp.nstr(mp.re(z), 65), "im": mp.nstr(mp.im(z), 65)}


def literal_length(N, num, den):
    D = fmpz(den)**N // ((N+1)*fmpz(num)**N)
    return 2*mp.log(mp.mpf(int(D+2)))


def exact_coefficients():
    cases = []
    for N in (*range(8, 129), 256, 640, 1536, 8192, 65536):
        K = 13*N//32
        central = set(range(K+1, N-K+1))
        prefix = set(range(1, N+2-K))
        exterior = prefix-central
        assert central <= prefix
        assert exterior == set(range(1, K+1)) | {N+1-K}
        for lam in (F(1), F(4, 3), F(13, 9)):
            for k in central:
                d = N+1-k
                assert d >= 3
                old, new = 1/F(d), lam/F(d+1)
                assert abs(new-old) <= F(2, 11)*(new+old)
                # Formal collection uses a_next=a_old+step; never identify
                # different orders without retaining the difference term.
                assert (new-old)+new == 2*new-old
            cases.append({"N": N, "lambda": str(lam),
                "commonOrders": len(central), "outerOrders": len(exterior),
                "loggedZeroOrderRetained": 1 in exterior,
                "upperEndpointRetained": N+1-K in exterior})
    # A wrong shift, removed upper endpoint or ignored adjacent difference
    # must be distinguishable by the exact regression.
    N, K, lam = 32, 13*32//32, F(13, 9)
    assert lam/F(N+2-(K+1)) != lam/F(N+1-(K+1))
    assert (N+1-K) not in range(K+1, N-K+1)
    x, next_x, low = F(3, 7), F(-5, 11), F(2, 5)
    k, d = K+1, N-K
    raw = -low*x/d + lam*low*next_x/(d+1)
    joined = (lam/(d+1)-1/F(d))*low*x + lam*low*(next_x-x)/(d+1)
    assert raw == joined
    assert raw != (lam/(d+1)-1/F(d))*low*x
    return {"exactRationalArithmetic": True, "cases": cases,
        "wrongOrderShiftRejected": True, "lostEndpointRejected": True,
        "unpaidAdjacentDifferenceRejected": True}


def finite_prime_replays():
    primes = [2, 3, 5, 7, 11, 97, 257, 1009, 5003, 9973]
    assert all(fmpz(p).is_prime() for p in primes)
    rows = []
    for N, num, den, y in itertools.product((4, 16, 64, 256), (10001,), (20000,), (0, 54, 142)):
        u, L, K = mp.mpf(num)/den, literal_length(N, num, den), 13*N//32
        lam = (N+1)/(u*L)
        s = mp.mpf(3)/2+1j*y
        weights = [(mp.log(p), mp.exp(-s*mp.log(p))) for p in primes]
        a = [u**(k+1)*sum(x**(k+1)/mp.factorial(k)*v for x, v in weights)
             for k in range(N+2)]
        central = range(K+1, N-K+1)
        exterior = (*range(1, K+1), N+1-K)
        C = sum(a[k-1]*a[N-k]/(N+1-k) for k in central)
        P = sum(a[k-1]*a[N+1-k]/(N+2-k) for k in range(1, N+2-K))
        joined_central = sum((lam/(N+2-k)-1/mp.mpf(N+1-k))*
                            a[k-1]*a[N-k] for k in central)
        outer = sum(a[k-1]*a[N+1-k]/(N+2-k) for k in exterior)
        step = sum(a[k-1]*(a[N+1-k]-a[N-k])/(N+2-k) for k in central)
        step_mass = sum(abs(a[k-1])*abs(a[N+1-k]-a[N-k])/(N+2-k) for k in central)
        price = sum((lam/(N+2-k)+1/mp.mpf(N+1-k))*
                    abs(a[k-1]*a[N-k]) for k in central)
        # Exact finite Selberg+pair join, including the ONE square diagonal.
        f = sum(mp.binomial(N+1, k)*mp.mpf('0.5')**(N+1) for k in range(K+1))
        square = [sum(x*(2*x)**k/mp.factorial(k)*mp.exp(-2*s*x)
                      for x, _ in weights) for k in (N, N+1)]
        combined_square = u**(N+1)*((2*f-1)*square[0]+(N+1)/L*(1-f)*square[1])
        direct = -u**(N+1)*sum(x**(N+1)/mp.factorial(N)*v for x, v in weights)
        for p, q in itertools.combinations(primes, 2):
            x, z, T = mp.log(p), mp.log(q), mp.log(p*q)
            Fz = sum(mp.binomial(N+1, k)*(z/T)**k*(x/T)**(N+1-k) for k in range(K+1))
            Fx = sum(mp.binomial(N+1, k)*(x/T)**k*(z/T)**(N+1-k) for k in range(K+1))
            coefficient = T*(1-T/L)-T/L*((L-x)*Fz+(L-z)*Fx)
            direct += u**(N+1)*coefficient*T**N/mp.factorial(N)*mp.exp(-s*T)
        scale = max(abs(direct), abs(a[N]), abs(C), abs(lam*P), mp.mpf('1e-1000'))
        residual = abs(direct-(-a[N]+C-lam*P+combined_square))/scale
        adj_residual = abs((-C+lam*P)-(joined_central+lam*outer+lam*step))/scale
        assert max(residual, adj_residual) < mp.mpf('1e-70')
        contracted = 1 <= lam <= mp.mpf(13)/9 and N >= 8
        if contracted:
            upper = mp.re(a[N])+mp.mpf(2)/11*price+lam*mp.re(outer)+lam*step_mass
            assert mp.re(a[N]-C+lam*P) <= upper+scale*mp.mpf('1e-70')
        rows.append({"N": N, "height": y, "primeUniverse": primes,
            "literalMovingLength": mp.nstr(L, 65), "lambda": mp.nstr(lam, 65),
            "fullCombinedFiniteSum": encode(-direct),
            "normalizedMomentMain": encode(a[N]-C+lam*P),
            "oneJoinedSquare": encode(combined_square),
            "adjacentStep": encode(step), "adjacentStepMass": mp.nstr(step_mass, 65),
            "coefficientContractionApplicable": contracted,
            "relativeAlgebraError": mp.nstr(max(residual, adj_residual), 12),
            "belowFormalThreshold": True, "cofinalCeilingCredit": 0})
    return rows


def source_regressions():
    rows = []
    for N, m, num, den in itertools.product((256, 1536, 65536, 262144),
                                           (1, 2, 3), (10001,), (20000,)):
        u, K, L = mp.mpf(num)/den, 13*N//32, literal_length(N, num, den)
        lam = (N+1)/(u*L)
        C = m*m*(mp.harmonic(N-K)-mp.harmonic(K))
        D = m*m*(mp.harmonic(N+1-K)-mp.harmonic(K+1))
        outer = m*m*(mp.harmonic(N+1)-mp.harmonic(K))-D
        old_price, joined_price = C+lam*D, lam*D-C
        exact = -m-C+lam*(D+outer)
        coarse = -m+mp.mpf(2)/11*old_price+lam*outer
        source = -m+m*m*(mp.log(mp.mpf(32)/13)/(-2*u*mp.log(u))-mp.log(mp.mpf(19)/13))
        assert 0 <= joined_price
        applicable = lam <= mp.mpf(13)/9
        if applicable:
            assert joined_price <= mp.mpf(2)/11*old_price
        assert abs((old_price-joined_price)-2*C) < mp.mpf('1e-70')
        if applicable:
            assert exact <= coarse
        if m >= 2:
            assert source > mp.mpf(42)/25
        rows.append({"classification": "Synthetic selected constant array; NOT independent arithmetic",
            "N": N, "multiplicity": m, "literalMovingLength": mp.nstr(L, 65),
            "oldSeparateCentralPrice": mp.nstr(old_price, 65),
            "exactJoinedCentralPrice": mp.nstr(joined_price, 65),
            "centralPriceRemoved": mp.nstr(2*C, 65),
            "priceFractionRemaining": mp.nstr(joined_price/old_price, 65),
            "exactJointSourceEvaluation": mp.nstr(exact, 65),
            "coefficientContractionApplicable": applicable,
            "contractedUpperEvaluation": mp.nstr(coarse, 65) if applicable else None,
            "sourceLimit": mp.nstr(source, 65),
            "belowFormalThreshold": N < 65536, "independentCeilingProved": False})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    mp.mp.dps = 100
    output = {"classification": "Exact algebra and numerical regression only",
        "exactChecks": exact_coefficients(), "finitePrimeReplays": finite_prime_replays(),
        "sourceRegressions": source_regressions(), "ceilingProved": False,
        "zeroExclusion": False, "finitePrimeRowsAreNotPopulationCounts": True,
        "noSelectedModeNormPayment": True}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({"exactRationalCases": len(output['exactChecks']['cases']),
        "finiteGenuinePrimeReplays": len(output['finitePrimeReplays']),
        "syntheticSourceRows": len(output['sourceRegressions']),
        "centralCoefficientFraction": "2/11", "ceilingProved": False}))


if __name__ == '__main__':
    main()
