#!/usr/bin/env python3
"""Optional diagnostic for the unpaid joined tagged-owner main.

The integer cases exhaust a TOY row with the exact finite owner selector,
squarefree/one-small-prime masks, original phase and both Riesz hinges.
Their exp(N/2)<=M and native core hypotheses FAIL. The continuous phase
cases inspect the signed smooth main on the actual total-log window, but
are not a proof of its discrete transport or a cofinal arithmetic floor.
This script is not part of builds or CI.
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
from probe_riesz_rough_owner_comparison import arithmetic


def toy_cases():
    N, p, M, X, b = 32, 100003, 5000, 10000, 4.
    mu, count, marks, prime = arithmetic(X+1)
    axis = np.arange(X+2)
    sf = mu != 0
    active = (M < axis) & (axis <= X)
    logs = np.log(np.maximum(axis, 1))
    c = math.log(p)
    total_log = c+logs
    orders = np.arange(N//5+2, 13*N//32+1)
    owner = 1-binom.pmf(orders[:, None], N+1, (logs/total_log)[None, :]).sum(axis=0)
    amplitude = owner*np.exp(-total_log/2)*total_log**(N+1)/math.factorial(N)
    R = math.floor(math.exp(b))
    riesz = np.zeros(X+2)
    for d in range(1, R+1):
        riesz[d::d] += int(mu[d])*max(b-math.log(d), 0.)
    T = [2, 3, 5, 7]
    small_count = sum((axis % r == 0).astype(int) for r in T)
    cases = []
    for height in (54., 65., 100.):
        w = np.where(active, amplitude*np.cos(height*total_log)/np.maximum(axis, 1), 0.)
        norm = .50005**(N+1)/(p*(c+b))
        for r in T:
            forbidden = [q for q in T if q != r]
            rough = np.ones(X+2, dtype=bool)
            for q in forbidden:
                rough[q::q] = False
            rough[0] = False
            tagged = sf & rough & (axis % r == 0)
            assert not (tagged & prime & active).any()
            untagged = sf & rough
            exclude_tag = untagged & (axis % r != 0)
            assert np.array_equal(untagged.astype(int)-exclude_tag.astype(int), tagged.astype(int))
            assert np.array_equal(tagged & active, sf & active & (small_count == 1) & (axis % r == 0))
            rho0 = 6/math.pi**2*math.prod(q/(q+1) for q in forbidden)
            rho1 = rho0*r/(r+1)
            rough_density0 = rho0*sum(int(mu[d])*marks[d]*max(b-math.log(d), 0.)
                                     for d in range(1, R+1) if rough[d])
            rough_density1 = rho1*sum(int(mu[d])*marks[d]*max(b-math.log(d), 0.)
                                     for d in range(1, R+1) if rough[d] and d % r != 0)
            scalar = rough_density0-rough_density1
            # Independent density expansion of the two translated hinges.
            # After dividing the label by r, the cofactor measure excludes r.
            excluded_two_hinges = rho1/r*sum(
                int(mu[d])*marks[d]*(max(b-math.log(d), 0.)-
                    max(b-math.log(r)-math.log(d), 0.))
                for d in range(1, R+1) if rough[d] and d % r != 0)
            assert abs(scalar-excluded_two_hinges) < 1e-13
            literal = float((w*tagged*riesz).sum())
            main = scalar*float(w.sum())
            prime0 = float((w*prime*untagged).sum())
            prime1 = float((w*prime*exclude_tag).sum())
            assert prime0 == prime1
            hinge_residual = 0.
            for a in axis[tagged & active]:
                cofactor = int(a)//r
                def response(cut):
                    return sum(int(mu[d])*max(cut-math.log(d), 0.)
                               for d in range(1, cofactor+1) if cofactor % d == 0)
                hinge_residual = max(hinge_residual,
                    abs(riesz[a]-(response(b)-response(b-math.log(r)))))
            assert hinge_residual < 1e-13
            by_count = {str(k+1): norm*float((w*tagged*riesz*(count == k)).sum())
                        for k in sorted(set(count[tagged & active].tolist()))}
            assert abs(sum(by_count.values())-norm*literal) < 1e-15
            cases.append(dict(N=N, owner=p, M=M, X=X, cutoff=b, tag=r,
                otherSmallPrimes=forbidden, height=height,
                labels=int((tagged & active).sum()), densityScalar=scalar,
                sourceScaledLiteral=norm*literal, sourceScaledSignedMain=norm*main,
                sourceScaledSignedError=norm*(literal-main),
                primeHeadDifference=prime0-prime1, twoHingeResidual=hinge_residual,
                joinedCountDiagnostic=by_count,
                support=dict(nativePoint=False, originalCoreWindow=False,
                    largeCofactorHypothesis=False, geometricTheoremApplied=False)))
    return cases


def primitive_factor(k, damping, value, terms=40):
    """Finite polynomial antiderivative; omitted tail has an explicit bound."""
    term = mp.mpc(1)
    total = term
    for h in range(1, min(k, terms-1)+1):
        term *= (k-h+1)/(damping*value)
        total += term
    if k < terms:
        return total, mp.mpf(0)
    ratio = mp.mpf(k)/abs(damping*value)
    assert ratio < mp.mpf('0.07')
    tail = abs(term)*ratio/(1-ratio)
    return total, tail


def continuous_cases():
    mp.mp.dps = 70
    cases = []
    u, height = mp.mpf(10001)/20000, mp.mpf(54)
    damping = mp.mpc(mp.mpf('0.5'), -height)
    for N in (256, 640, 1536, 4096, 8192, 65536):
        for c_share in ('1.025', '1.10', '1.15'):
            c = mp.mpf(c_share)*N
            n = N+1
            def boundary(T):
                v = T-c
                assert v > 0
                radial_scale = mp.exp(n*mp.log(u)+n*mp.log(T)-T/2-mp.loggamma(N+1))
                full, tail = primitive_factor(n, damping, T)
                result = full
                error = tail
                for k in range(N//5+2, 13*N//32+1):
                    mass = mp.exp(mp.loggamma(n+1)-mp.loggamma(k+1)-mp.loggamma(n-k+1)+
                                  k*mp.log(v/T)+(n-k)*mp.log(c/T))
                    poly, omitted = primitive_factor(k, damping, v)
                    result -= mass*poly
                    error += mass*omitted
                return radial_scale*mp.exp(1j*height*T)*result/damping, \
                    radial_scale*error/abs(damping)
            lo, elo = boundary(mp.mpf(39)/20*N)
            hi, ehi = boundary(mp.mpf(203)/100*N)
            value = lo-hi
            cases.append(dict(N=N, ownerLogSlope=c_share, phaseHeight=54,
                sourceScaledSignedIntegralReal=float(mp.re(value)),
                sourceScaledSignedIntegralNorm=float(abs(value)),
                antiderivativeSeriesTailBound=float(elo+ehi),
                discreteTransportProved=False, densityScalarIncluded=False,
                originalCoreMasksProved=False, cofinalFloorProved=False))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path('.lake/riesz-tagged-owner-comparison/probe.json'))
    args = parser.parse_args()
    report = dict(schemaVersion=1, toyCases=toy_cases(), continuousCases=continuous_cases(),
        source=dict(path=str(Path(__file__).resolve()),
            sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),
        scope=dict(optionalOutsideBuildsAndCI=True, exactIntegerMasksAndFactorialOrders=True,
            toyRowsExhausted=True, floatingArithmetic=True, geometricTheoremApplied=False,
            nativeOrCofinalFloorProved=False, continuousSignedMainDiagnosticOnly=True))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    for case in report['toyCases']:
        print(json.dumps({k: case[k] for k in ('tag', 'height', 'sourceScaledLiteral',
            'sourceScaledSignedMain', 'sourceScaledSignedError', 'primeHeadDifference')}), flush=True)
    for case in report['continuousCases']:
        print(json.dumps(case), flush=True)


if __name__ == '__main__':
    main()
