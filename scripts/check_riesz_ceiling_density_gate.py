#!/usr/bin/env python3
"""Independent high-precision replay of the continuous ceiling countertest.

No producer imports or floating Poisson/CDF routines are used. Retain every
logged order through the finite tail cutoff, all complex phases, and the
literal moving-length floor. This validates a diagnostic model, NOT primes
or a certified finite entry order for the eventual Lean inequality.
"""
import argparse
import json
from pathlib import Path

from flint import fmpz
import mpmath as mp


def length(N):
    u = mp.mpf(10001)/20000
    if N <= 65536:
        d = fmpz(20000)**N//((N+1)*fmpz(10001)**N)
        return 2*mp.log(mp.mpf(int(d+2)))
    return -2*N*mp.log(u)-2*mp.log(N+1)


def moments(y):
    # The EXACT integration-by-parts recurrence, not scipy lfilter or CDF.
    u, B = mp.mpf(10001)/20000, 40000
    x = u*B
    pmf = mp.exp(-x)
    cdf, t0, t2 = mp.mpf(0), mp.mpc(0), mp.mpc(0)
    z0, z2 = mp.mpc(mp.mpf('.5'), y), mp.mpc(u, 2*y)
    r0, r2 = u/z0, u/z2
    e0, e2 = mp.exp((u-z0)*B), mp.exp((u-z2)*B)
    out = []
    for k in range(65537):
        if k:
            pmf *= x/k
        cdf += pmf
        t0 = r0*(t0+e0*pmf)
        t2 = r2*(t2+e2*pmf)
        out.append(t0-2*cdf-2*t2)
    return out


def joined(N, a):
    u, K = mp.mpf(10001)/20000, 13*N//32
    lam = (N+1)/(u*length(N))
    if N <= 65536:
        c = mp.fsum(a[k-1]*a[N-k]/(N+1-k) for k in range(K+1, N-K+1))
        p = mp.fsum(a[k-1]*a[N+1-k]/(N+2-k) for k in range(1, N+2-K))
        trace = mp.fsum(a[k]*a[N-1-k] for k in range(N))/N
        selberg, pair = -a[N]-trace, trace+c-lam*p
        # Evaluate the two ORIGINAL joined objects before their trace cancels.
        return -selberg-pair
    assert K > 65536
    # Use the same explicitly declared tail model, reconstructed as the two
    # original API expressions rather than the producer's reduced main.
    e = [v+2 for v in a]
    trace = 4-4*mp.fsum(e)/N
    c = 4*(mp.harmonic(N-K)-mp.harmonic(K))
    p = 4*(mp.harmonic(N+1)-mp.harmonic(K))-2*mp.fsum(
        e[k]/(N+1-k) for k in range(len(e)))
    selberg, pair = 2-trace, trace+c-lam*p
    return -selberg-pair


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('probe', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    mp.mp.dps = 80
    d = json.loads(args.probe.read_text())
    assert d['classification'].startswith('Continuous-density')
    assert not d['literalPrimeDataUsed'] and not d['independentCeilingProved']
    assert d['ceilingCredit'] == 0 and not d['zeroExclusion']
    assert not d['entryOrderCertified']
    rows, worst = [], mp.mpf(0)
    for y in (54, 142):
        a = moments(y)
        for N in (256, 1536, 8192, 16384, 32768, 65536,
                  1048576, 134217728, 268435456, 1073741824):
            r = next(r for r in d['regressionRows'] if r['N']==N and r['height']==y)
            if r['joinedReal'] == 0 and r['joinedImaginary'] == 0:
                assert r['displayedZeroIsNotExactVanishing']
            v = joined(N, a)
            err = abs(mp.re(v)-mp.mpf(r['joinedReal']))
            assert err < mp.mpf('2e-11')
            worst = max(worst, err)
            rows.append({'N': N, 'height': y, 'highPrecisionReal': mp.nstr(mp.re(v), 55),
                         'absoluteReplayError': mp.nstr(err, 20)})
    u = mp.mpf(10001)/20000
    c = mp.log(mp.mpf(32)/13)/(-2*u*mp.log(u))-mp.log(mp.mpf(19)/13)
    assert abs(mp.mpf(d['source'])-(-2+4*c)) < mp.mpf('1e-63')
    # Check the paper's displayed expression independently, without claiming
    # a known finite-height threshold or assuming that zero-gap is admissible.
    for r in d['ivicAsymptoticExpressionRows']:
        L = r['logHeight']
        gap = mp.mpf(r['horizontalGap'])
        v = 4*mp.log(L)+20*gap*mp.sqrt(gap)*L
        assert abs(v-mp.mpf(r['displayedAsymptoticUpperExpression'])) < mp.mpf('1e-34')
        assert v > 2 and not r['finiteHeightApplicabilityCertified']
    output = {'classification': 'Independent continuous-model regression only',
              'modelRowsReplayed': len(rows), 'rows': rows,
              'worstAbsoluteReplayError': mp.nstr(worst, 25),
              'allLoggedOrdersRetained': True, 'onlyOneCommonPhasePerHeight': True,
              'independentCeilingProved': False, 'actualPrimeCounterexample': False,
              'entryOrderCertified': False, 'ceilingCredit': 0}
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({k: output[k] for k in ('modelRowsReplayed', 'worstAbsoluteReplayError',
                                            'independentCeilingProved', 'ceilingCredit')}))


if __name__ == '__main__':
    main()
