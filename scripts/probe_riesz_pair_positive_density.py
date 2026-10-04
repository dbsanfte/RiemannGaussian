#!/usr/bin/env python3
"""Optional phase-consistent positive-density null test of the signed main.

This is NOT the arithmetic prime measure and never supplies floor credit.
It tests whether factorial coupling, phase consistency, positivity and an
exponentially small relative density ripple alone rule out the retained
selected source. Every singular channel is integrated above the same lower
log threshold, not replaced by a separate complete-leg limiting value.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.signal import lfilter
from scipy.special import gammainc
from scipy.stats import poisson


def digest(path):
    return dict(path=str(path), sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest())


def error_orders(u, beta, y, lower, cap):
    """B_k=-1+E_k for the SAME positive density and complex phase.

    nu(T)=[exp(T)-2 exp(beta*T)cos(y*T)]/T, T>=lower.
    B_k=k*u^k/k! integral T^k exp(-(3/2+i*y)*T)nu(T)dT.
    The incomplete Gamma identity gives
      W_k(z)=(u/z)^k exp(-z*lower) sum_(j<k)(z*lower)^j/j!,
    and W_k(z)=(u/z)[W_(k-1)(z)+exp(-z*lower)(u*lower)^(k-1)/(k-1)!].
    Computing that recurrence jointly avoids enormous cancelling powers.
    """
    lam = u*lower
    orders = np.arange(1, cap+1)
    atom = poisson.pmf(orders-1, lam)
    z_pole, z_conjugate = .5+1j*y, u+2j*y
    wp = lfilter([u/z_pole], [1, -u/z_pole],
                 complex(mp.exp((mp.mpf(u)-mp.mpc(z_pole))*lower))*atom)
    wc = lfilter([u/z_conjugate], [1, -u/z_conjugate],
                 complex(mp.exp((mp.mpf(u)-mp.mpc(z_conjugate))*lower))*atom)
    error = gammainc(orders, lam)+wp-wc
    # Check consistency with the full lower-threshold recurrence, not
    # merely with the limiting source B_k=-1.
    source = poisson.cdf(orders-1, lam)
    B = wp-source-wc
    assert np.max(np.abs(B+1-error)) < 2e-15
    return np.concatenate(([0j], error)), wp, wc


def moving_length(N, num=10001, den=20000):
    # D=floor(u^(-N)/(N+1)).  The literal length is in
    # [L0,L0+4*(N+1)*u^N], by floor bounds and log(1+x)<=x.
    # Keep this enclosure, rather than constructing hundred-million-order
    # integers or silently substituting an asymptotic cutoff.
    u = mp.mpf(num)/den
    L0 = -2*N*mp.log(u)-2*mp.log(N+1)
    log_width = mp.log(4)+mp.log(N+1)+N*mp.log(u)
    if N <= 425984:
        D = den**N//((N+1)*num**N)
        assert abs(L0-2*mp.log(D+2)) < mp.mpf('1e-70')
    return L0, log_width


def pure_source(N, u, L):
    M, K = N+1, 13*N//32
    return (1+mp.harmonic(M-K-1)-mp.harmonic(K)-
            M/(L*u)*(mp.harmonic(M)-mp.harmonic(K)))


def direct_quadratic(N, u, L, E):
    """Full FOUR-term signed quadratic, without completing selected legs."""
    M, K = N+1, 13*N//32
    B = -np.ones(N+3, dtype=complex)
    B[1:] += E[1:N+3]
    a = np.arange(K+1, M-K)
    b = np.arange(K+1, M+1-K)
    c = np.arange(1, K+1)
    d = np.arange(1, N+1)
    parts = dict(central=M/2*np.sum(B[a]*B[M-a]/(a*(M-a))),
        successor=-M*(M+1)/(2*float(L)*u)*np.sum(B[b]*B[M+1-b]/(b*(M+1-b))),
        logged=-M/(float(L)*u)*np.sum(B[c]*B[M+1-c]/(M+1-c)),
        selbergTrace=np.sum(B[d]*B[M-d])/N)
    return sum(parts.values()), parts


def sparse_quadratic(N, u, L, E):
    """Keep the correlated low-order perturbation; account for its tails.

    For central/partner orders above cap the perturbation is omitted here,
    with a separate explicit numerical tail majorant. This is model-only
    coefficient evaluation, not a physical mask or prime completion proof.
    """
    cap, M, K = len(E)-1, N+1, 13*N//32
    assert cap < K and 2*cap < M
    orders = np.arange(1, cap+1)
    correction = -2/N*np.sum(E[1:])
    correction += M/(float(L)*u)*np.sum(E[1:]/(M+1-orders))
    return complex(pure_source(N, mp.mpf(10001)/20000, L))+correction


def encode(value):
    return dict(re=float(np.real(value)), im=float(np.imag(value)))


def forcing_log(lam, cutoff):
    tilt = mp.log(mp.mpf(cutoff)/lam)
    return lam*(mp.exp(tilt)-1)-tilt*cutoff


def full_error_tail(u, y, lower, cap):
    """An explicit L1 bound on ALL omitted E_k, including channel memory.

    At k=cap split the forcing at H=floor(cap/2). For W_k=q W_(k-1)
    +c q pi_(k-1), |W_cap|<=|c|[|q|^(cap-H)+|q|P(Poi>=H+1)].
    Summing its homogeneous tail and all subsequent forcing gives
    sum_(k>cap)|W_k|<=|c| |q|/(1-|q|)
      [|q|^(cap-H)+|q|P(Poi>=H+1)+P(Poi>=cap)].
    The selected real head contributes the geometric Chernoff sum.
    This is a model estimate, NOT a prime-sum or physical-cutoff payment.
    """
    lam, half = u*lower, cap//2
    forcing = forcing_log(lam, cap)
    half_forcing = forcing_log(lam, half+1)
    tilt = mp.log(mp.mpf(cap)/lam)
    head = mp.exp(forcing)/(mp.exp(tilt)-1)
    bounds = []
    for z in (mp.mpf(1)/2+1j*y, u+2j*y):
        q = abs(u/z)
        c = mp.exp((u-mp.re(z))*lower)
        memory = q**(cap-half)+q*mp.exp(half_forcing)
        bounds.append(c*q/(1-q)*(memory+mp.exp(forcing)))
    total = head+sum(bounds)
    assert mp.log(total) < -1000
    return dict(cap=cap, half=half, poissonForcingTailLog=mp.nstr(forcing, 50),
        halfwayForcingTailLog=mp.nstr(half_forcing, 50),
        fullOmittedL1TailLog=mp.nstr(mp.log(total), 50),
        homogeneousChannelMemoryIncluded=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-positive-density/probe.json'))
    args = ap.parse_args()
    mp.mp.dps = 90
    u, beta, lower, cap = .50005, .99995, 20000, 30003
    rows = []
    for y in (55, 101, 10000):
        E, wp, wc = error_orders(u, beta, y, lower, cap)
        # Positivity is a genuine pointwise model fact: exp((1-beta)T)>2
        # for T>=lower. It concerns this continuous density, not primes.
        lower_exact = mp.mpf(lower)
        beta_exact = mp.mpf(99995)/100000
        lower_margin = 1-2*mp.exp(-(1-beta_exact)*lower_exact)
        assert lower_margin > 0
        moment_error_sum = np.sum(E[1:])
        z_pole, z_conjugate = mp.mpf(1)/2+1j*y, mp.mpf(10001)/20000+2j*y
        u_exact = mp.mpf(10001)/20000
        exact_error_sum = u_exact*lower_exact
        exact_error_sum += u_exact/(z_pole-u_exact)*mp.exp((u_exact-z_pole)*lower_exact)
        exact_error_sum -= u_exact/(z_conjugate-u_exact)*mp.exp((u_exact-z_conjugate)*lower_exact)
        assert abs(moment_error_sum-complex(exact_error_sum)) < 2e-8
        # Keep the complete tail, not just the much smaller forcing tail.
        # The latter alone would omit the recurrence's homogeneous memory.
        tail = full_error_tail(u_exact, y, lower_exact, cap)
        assert abs(u_exact/z_pole) < mp.mpf(1)/50
        assert abs(u_exact/z_conjugate) < mp.mpf(1)/100
        for j in (7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17):
            N = 8*(j+4)*2**(j+3)
            L, log_length_width = moving_length(N)
            value = sparse_quadratic(N, u, L, E)
            regression_error = None
            if N <= 425984:
                fullE, _, _ = error_orders(u, beta, y, lower, N+2)
                direct, _ = direct_quadratic(N, u, L, fullE)
                regression_error = abs(direct-value)
                assert regression_error < 2e-12
            rows.append(dict(N=N, y=y, sourceScaledModelQuadratic=encode(value),
                pureSelectedFiniteValue=mp.nstr(pure_source(N, u_exact, L), 50),
                movingLength=mp.nstr(L, 50), momentPerturbationSum=encode(moment_error_sum),
                exactInfinitePerturbationSum=dict(re=mp.nstr(mp.re(exact_error_sum), 50),
                    im=mp.nstr(mp.im(exact_error_sum), 50)),
                fullFourTermReplayError=regression_error,
                above399Over5000=bool(value.real >399/5000),
                sourceLimit=mp.nstr(1+mp.log(mp.mpf(19)/13)-
                    mp.log(mp.mpf(32)/13)/(-2*u_exact*mp.log(u_exact)), 50),
                literalMovingLengthEnclosure=True,
                logLengthEnclosureWidth=mp.nstr(log_length_width, 50),
                pointwiseDensityMarginAtThreshold=mp.nstr(lower_margin, 50),
                omittedMomentTail=tail,
                # Very loose finite-quadratic propagation of the tail.
                # Central/logged/trace weights <=(N+2)^2, with bounded
                # moments; this still leaves enormous model-only margin.
                logSparseTailErrorBound=mp.nstr(mp.mpf(tail['fullOmittedL1TailLog'])+
                    mp.log(100)+3*mp.log(N+2), 50),
                modelIsActualPrimeMeasure=False, cofinalFloorCredit=0))
    assert any(row['above399Over5000'] for row in rows)
    result = dict(classification='Positive continuous-density null model; no arithmetic prime estimate',
        sources=[digest('scripts/probe_riesz_pair_positive_density.py'),
            digest('RiemannGaussian/ZetaRieszPositiveDensityAudit.lean')],
        density='[exp(T)-2 exp(beta*T)cos(y*T)]/T on T>=20000',
        beta='99995/100000', u='10001/20000', fullComplexPhaseRetained=True,
        adjacentFactorialCouplingExact=True, everyLoggedAndTraceSlotRetained=True,
        completeCurrentFourTermQuadraticUsed=True, actualPrimeDensityTransportAttempted=False,
        coefficientEvaluationPrecision='binary64 recurrence; independent 110-digit replay required',
        fullOmittedTailIncludesHomogeneousMemory=True,
        rows=rows, optionalOutsideCI=True, arithmeticFloorBound=False, cofinalFloorCredit=0)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
    print(json.dumps(dict(modelCases=len(rows), sourceTarget=399/5000,
        firstAboveTarget=min(row['N'] for row in rows if row['above399Over5000']),
        maxDirectReplayError=max(row['fullFourTermReplayError'] or 0 for row in rows),
        actualPrimeMeasure=False, arithmeticFloorBound=False)))


if __name__ == '__main__':
    main()
