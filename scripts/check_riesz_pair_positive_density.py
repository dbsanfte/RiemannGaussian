#!/usr/bin/env python3
"""Independent high-precision replay of the positive-density null model.

Imports no producer and uses no NumPy/SciPy recurrence. These are model
values, not an arithmetic prime estimate, interval certificate or floor.
"""

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def decode(row):
    return mp.mpc(row['re'], row['im'])


def moments(u, y, lower, cap):
    lam = u*lower
    zp, zc = mp.mpf(1)/2+1j*y, u+2j*y
    qp, qc = u/zp, u/zc
    cp, cc = mp.exp((u-zp)*lower), mp.exp((u-zc)*lower)
    probability = mp.exp(-lam)
    wp = wc = cumulative = mp.mpf(0)
    errors = []
    for k in range(1, cap+1):
        wp = qp*(wp+cp*probability)
        wc = qc*(wc+cc*probability)
        cumulative += probability
        errors.append(1-cumulative+wp-wc)
        probability *= lam/k
    exact_sum = lam+u/(zp-u)*cp-u/(zc-u)*cc
    assert abs(sum(errors)-exact_sum) < mp.mpf('1e-90')
    return errors


def poisson_bound(lam, threshold):
    # Markov applied to exp(t*K), with t=log(threshold/lam).
    t = mp.log(mp.mpf(threshold)/lam)
    return mp.exp(lam*(mp.exp(t)-1)-t*threshold)


def tail_bound(u, y, lower, cap):
    lam, half = u*lower, cap//2
    full, middle = poisson_bound(lam, cap), poisson_bound(lam, half+1)
    total = full/(mp.mpf(cap)/lam-1)
    for z in (mp.mpf(1)/2+1j*y, u+2j*y):
        ratio, amplitude = abs(u/z), mp.exp((u-mp.re(z))*lower)
        # The first term pays old forcing memory; it cannot be replaced
        # by the much smaller post-cap forcing probability.
        total += amplitude*ratio/(1-ratio)*(
            ratio**(cap-half)+ratio*middle+full)
    return total


def quadratic(N, u, L, errors):
    """Independent coefficient replay, all four original components.

    Higher errors have an explicit L1 tail bound. With cap<K and 2cap<M,
    the central two bands contain no retained low-order error; the logged
    low slots and both Selberg endpoints are retained exactly.
    """
    M, K = N+1, 13*N//32
    assert len(errors)<K and 2*len(errors)<M
    central = mp.harmonic(M-K-1)-mp.harmonic(K)
    successor = -M/(L*u)*(mp.harmonic(M-K)-mp.harmonic(K))
    logged = -M/(L*u)*(mp.harmonic(M)-mp.harmonic(M-K))
    trace = mp.mpf(1)
    for k, e in enumerate(errors, start=1):
        logged += M/(L*u)*e/(M+1-k)
        trace -= 2*e/N
    return central+successor+logged+trace


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input', type=Path, default=Path('.lake/riesz-pair-positive-density/probe.json'))
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-positive-density/validation.json'))
    args = ap.parse_args()
    data = json.loads(args.input.read_text())
    for pin in data['sources']:
        assert digest(pin['path']) == pin['sha256']
    mp.mp.dps = 110
    u, lower, cap = mp.mpf(10001)/20000, mp.mpf(20000), 30003
    beta = mp.mpf(3)/2-u
    margin = 1-2*mp.exp(-(1-beta)*lower)
    assert margin>mp.mpf(1)/4
    errors_by_height = {y:moments(u, y, lower, cap) for y in (55, 101, 10000)}
    tails = {y:tail_bound(u, y, lower, cap) for y in errors_by_height}
    errors, crossings = [], []
    source = 1+mp.log(mp.mpf(19)/13)-mp.log(mp.mpf(32)/13)/(-2*u*mp.log(u))
    assert source>mp.mpf(399)/5000
    for row in data['rows']:
        N, y = row['N'], row['y']
        L0 = -2*N*mp.log(u)-2*mp.log(N+1)
        log_width = mp.log(4)+mp.log(N+1)+N*mp.log(u)
        assert abs(L0-mp.mpf(row['movingLength']))<mp.mpf('1e-40')
        assert abs(log_width-mp.mpf(row['logLengthEnclosureWidth']))<mp.mpf('1e-39')
        # All sampled orders are after the formal estimate threshold.
        # That does not make the continuous density an arithmetic model.
        assert N>=65536 and L0>N
        value = quadratic(N, u, L0, errors_by_height[y])
        replay_error = abs(value-decode(row['sourceScaledModelQuadratic']))
        assert replay_error<mp.mpf('2e-12')
        errors.append(replay_error)
        tail = tails[y]
        assert mp.log(tail)<-1000
        info = row['omittedMomentTail']
        assert info['homogeneousChannelMemoryIncluded']
        assert abs(mp.log(tail)-mp.mpf(info['fullOmittedL1TailLog']))<mp.mpf('1e-44')
        sparse_log = mp.log(tail)+mp.log(100)+3*mp.log(N+2)
        assert abs(sparse_log-mp.mpf(row['logSparseTailErrorBound']))<mp.mpf('1e-44')
        assert sparse_log<-900
        assert abs(source-mp.mpf(row['sourceLimit']))<mp.mpf('1e-49')
        above = mp.re(value)>mp.mpf(399)/5000
        assert above == row['above399Over5000']
        if above:
            crossings.append(N)
        assert row['literalMovingLengthEnclosure']
        assert not row['modelIsActualPrimeMeasure'] and row['cofinalFloorCredit']==0
    assert min(crossings)==83886080
    assert not data['arithmeticFloorBound'] and data['cofinalFloorCredit']==0
    result = dict(inputSha256=digest(args.input), checkerSha256=digest(__file__),
        sourcePinsPassed=True, modelCases=len(errors), phaseHeights=list(errors_by_height),
        modelRecurrencesReplayedAtDecimalDigits=110, producerImported=False,
        maxIndependentReplayError=float(max(errors)),
        fullOmittedTailIncludesHomogeneousMemory=True,
        worstLogL1TailBound=float(max(mp.log(t) for t in tails.values())),
        firstSampledAboveTarget=min(crossings),
        actualPrimeMeasure=False, formalQuadraticAsymptoticProved=False,
        arithmeticFloorBound=False, floorCredit=0, optionalOutsideCI=True, passed=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
    print(json.dumps(result))


if __name__=='__main__':
    main()
