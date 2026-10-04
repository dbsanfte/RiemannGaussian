#!/usr/bin/env python3
"""Optional, NON-ARITHMETIC ceiling gate.

Evaluate the common-phase continuous density proved in
ZetaRieszCeilingDensityAudit. It has the usual leading e^T/T density,
not literal primes. Keep every logged order and the literal moving-length
floor (or its explicit enclosing interval at very large orders).

The output is a numerical regression of a Lean-proved generic no-go.
It supplies zero ceiling credit and is not a certificate of an entry order.
"""
import argparse
import json
from pathlib import Path

from flint import fmpz
import mpmath as mp
import numpy as np
from scipy.signal import lfilter
from scipy.special import gammaincc, gammaln


NUM, DEN, B, J = 10001, 20000, 40000, 65536


def length(N):
    logX = -N*mp.log(mp.mpf(NUM)/DEN)-mp.log(N+1)
    if N <= 65536:
        D = fmpz(DEN)**N//((N+1)*fmpz(NUM)**N)
        L = 2*mp.log(mp.mpf(int(D+2)))
        return L, {"floorEvaluatedExactly": True,
                   "length": mp.nstr(L, 55)}
    # X=u^-N/(N+1), floor(X)+2 in (X+1,X+2].
    # Therefore 2log(X)<L<=2log(X)+4/X. Do not silently set L=-2Nlog u.
    L = 2*logX
    return L, {"floorEvaluatedExactly": False,
        "enclosureLower": mp.nstr(L, 55),
        "enclosureUpperAddend": "4*exp(-("+mp.nstr(logX, 55)+"))",
        "retainsFloorPlusTwoThroughInterval": True,
        "retainsMinusTwoLogNPlusOne": True}


def array(max_order, height):
    u, x = NUM/DEN, (NUM/DEN)*B
    k = np.arange(max_order+1, dtype=float)
    pmf = np.exp(-x+k*np.log(x)-gammaln(k+1))
    selected = gammaincc(k+1, x)
    r0, r2 = u/complex(.5, height), u/complex(u, 2*height)
    c0 = mp.exp((mp.mpf(NUM)/DEN-mp.mpc(.5, height))*B)
    c2 = mp.exp(-2j*mp.mpf(height)*B)
    unshifted = complex(c0)*lfilter([r0], [1, -r0], pmf)
    opposite = complex(c2)*lfilter([r2], [1, -r2], pmf)
    return unshifted-2*selected-2*opposite


def tail_log_bound(height):
    """Numerical evaluation of a stated Chernoff/recurrence majorant.

    All claims of eventual failure come from the Lean theorem, not this
    floating tail enclosure. It only validates the long-order regression.
    """
    u, x = mp.mpf(NUM)/DEN, mp.mpf(NUM)/DEN*B
    r0, r2 = abs(u/mp.mpc(.5, height)), abs(u/mp.mpc(u, 2*height))

    def tail(v):
        return mp.exp(-v*mp.log(v/x)+v-x)

    e = 2*tail(J)
    for r, c in ((r0, mp.exp((u-.5)*B)), (r2, mp.mpf(2))):
        e += c*r*(r**(J//4)+tail(3*J//4))
    return mp.nstr(mp.log(e), 40)


def direct(N, a, lam):
    K = 13*N//32
    k = np.arange(K+1, N-K+1)
    C = np.sum(a[k-1]*a[N-k]/(N+1-k))
    k = np.arange(1, N+2-K)
    P = np.sum(a[k-1]*a[N+1-k]/(N+2-k))
    trace = np.sum(a[:N]*a[N-1::-1])/N
    # Reconstruct the existing two APIs independently of the reduced main.
    selberg = -a[N]-trace
    pair = trace+C-lam*P
    raw = -selberg-pair
    main = a[N]-C+lam*P
    assert abs(raw-main) < 2e-12
    return main, {"allFiniteArrayOrdersEvaluated": True,
        "rawTraceJoinAbsoluteError": float(abs(raw-main)),
        "selectedPrimeTerm": [float(a[N].real), float(a[N].imag)],
        "signedCentral": [float((-C).real), float((-C).imag)],
        "signedPrefix": [float((lam*P).real), float((lam*P).imag)]}


def long_order(N, a, lam):
    K = 13*N//32
    assert K > J and N > 2*J+2
    # Every low order up to J is literal. Only the already tiny tails
    # beyond J are replaced by their -2 value in this NUMERICAL MODEL.
    Hc = mp.harmonic(N-K)-mp.harmonic(K)
    Hp = mp.harmonic(N+1)-mp.harmonic(K)
    e = a+2
    i = np.arange(len(a), dtype=float)
    correction = np.sum(e/(N+1-i))
    main = -2-4*Hc+lam*(4*Hp-2*mp.mpc(complex(correction)))
    return complex(main), {"allFiniteArrayOrdersEvaluated": False,
        "exactLowOrdersRetainedThrough": J,
        "highOrderTailReplacementIsNumericalRegressionOnly": True,
        "selectedPrimeTerm": [-2., 0.],
        "signedCentral": [float(-4*Hc), 0.],
        "signedPrefix": [float(mp.re(lam*(4*Hp-2*mp.mpc(complex(correction))))),
                         float(mp.im(lam*(4*Hp-2*mp.mpc(complex(correction)))))]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    mp.mp.dps = 80
    u = mp.mpf(NUM)/DEN
    c = mp.log(mp.mpf(32)/13)/(-2*u*mp.log(u))-mp.log(mp.mpf(19)/13)
    source = -2+4*c
    rows = []
    for height in (54, 142):
        a = array(262145, height)
        for N in (256, 1536, 8192, 16384, 32768, 65536, 262144,
                  1048576, 16777216, 134217728, 268435456, 1073741824):
            L, metadata = length(N)
            lam = mp.mpf(N+1)/(u*L)
            if N <= 262144:
                value, parts = direct(N, a, float(lam))
            else:
                value, parts = long_order(N, a[:J+1], lam)
            rows.append({"N": N, "height": height, "movingLength": metadata,
                "joinedReal": float(value.real), "joinedImaginary": float(value.imag),
                "distanceToCeiling": float(value.real-1.68),
                "displayedZeroIsNotExactVanishing": bool(value == 0), **parts})
    gaps = (mp.mpf(0), mp.mpf(1)/20000)
    ivic = []
    for gap in gaps:
        for H in (1800, 1000000, 1000000000):
            # Corollary 1 of arXiv:1706.08268v1, evaluated as an asymptotic
            # expression. The paper's gamma_1 is unspecified, so none of
            # these evaluations is a certified finite-height theorem.
            bound = 4*mp.log(H)+20*gap**mp.mpf('1.5')*H
            ivic.append({"logHeight": H, "horizontalGap": mp.nstr(gap, 30),
                "displayedAsymptoticUpperExpression": mp.nstr(bound, 40),
                "lessThanTwo": bound < 2,
                "finiteHeightApplicabilityCertified": False})
    output = {"classification": "Continuous-density countertest; NOT ordinary primes",
        "literalPrimeDataUsed": False, "independentCeilingProved": False,
        "zeroExclusion": False, "ceilingCredit": 0,
        "density": "(exp(T)-4exp((3/2-u)T)cos(yT))/T, T>40000",
        "commonPhase": "exp(-(3/2+iy)T)",
        "u": "10001/20000", "positiveThreshold": B,
        "leadingDensityCoefficient": 1,
        "noAdditionalRealExponentialChannel": True,
        "allLoggedOrdersIncludingZeroRetained": True,
        "source": mp.nstr(source, 65),
        "sourceAboveCeiling": mp.nstr(source-mp.mpf(42)/25, 65),
        "highOrderTailLogMajorant": {str(y): tail_log_bound(y) for y in (54, 142)},
        "regressionRows": rows,
        "ivicSource": "https://arxiv.org/pdf/1706.08268v1#page=10",
        "ivicAsymptoticExpressionRows": ivic,
        "entryOrderCertified": False}
    # Only a regression sign change, not a finite/cofinal certificate.
    assert all(r['joinedReal'] < 1.68 for r in rows if r['N'] == 65536)
    assert all(r['joinedReal'] > 1.68 for r in rows if r['N'] == 1073741824)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({"continuousModelRows": len(rows),
        "source": output['source'], "early65536": [r['joinedReal'] for r in rows if r['N']==65536],
        "late1073741824": [r['joinedReal'] for r in rows if r['N']==1073741824],
        "independentCeilingProved": False, "ceilingCredit": 0}))


if __name__ == '__main__':
    main()
