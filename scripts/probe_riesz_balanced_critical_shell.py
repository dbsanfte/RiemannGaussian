#!/usr/bin/env python3
"""Optional signed critical-divisor audit of the balanced toy population.

Keep all label counts, both components of the original complex phase, the
factorial weight, and the same FULL ordinary-prime head. Integer tests for
the divisor cutoff and its two least-prime quotients are exact. This is the
earlier finite toy length, NOT the native moving length/dyadic carrier.
There is no fitted cancellation, prime-density substitution, eventual error
payment, or cofinal floor certificate in this script.
"""

import argparse
from collections import Counter, defaultdict
import cmath
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import probe_riesz_balanced_joint as base
import probe_riesz_balanced_signature as signature_probe


def critical_data(N, primes, divisors):
    """Pair with the least prime, then the least remaining prime.

    On a gap of the first pairing, R_L(n) = log(r) M_{n/r}(X/r).
    Pairing that integer Mobius prefix with q leaves exactly the shell
    X/(r*q) < d <= X/r in the divisors of n/(r*q).
    """
    X = 20000**(2*N)//10001**(2*N)
    r, q = primes[:2]
    crossing = []
    shell = []
    for mask, (d, sign) in enumerate(divisors):
        if not mask & 1 and X//r < d <= X:
            crossing.append((d, sign))
        if not mask & 3 and X//(r*q) < d <= X//r:
            shell.append((d, sign, mask.bit_count()))
    return crossing, shell


def as_complex(z):
    return {"re": z.real, "im": z.imag}


def run_order(N, heights):
    data = base.prepare(N, 10001/20000)
    u, L = data['u'], data['L']
    windows = [(1.95, 2.03), (1.971, 2.029)]
    counts = {w: Counter() for w in windows}
    classes = {w: Counter() for w in windows}
    ranks = {w: Counter() for w in windows}
    signs = {w: Counter() for w in windows}
    joined = {w: {y: defaultdict(complex) for y in heights} for w in windows}
    net = {w: {y: 0j for y in heights} for w in windows}
    gross = {w: defaultdict(float) for w in windows}
    examples = {}
    max_gap_error = 0.
    for n, primes, divisors in data['labels']:
        T = math.log(n)
        response = math.fsum(sign*max(L-math.log(d), 0.) for d, sign in divisors)
        crossing, shell = critical_data(N, primes, divisors)
        M = sum(sign for _, sign, _ in shell)
        if crossing:
            kind = 'active-least-prime-crossing'
        elif M == 0:
            kind = 'gap-zero'
        elif all(rank == 1 for _, _, rank in shell):
            kind = 'gap-prime-critical-divisors'
        elif len(shell) == 1:
            kind = 'gap-single-composite-critical-divisor'
        else:
            kind = 'gap-multiple-critical-divisors'
        if not crossing:
            error = abs(response-math.log(primes[0])*M)
            max_gap_error = max(max_gap_error, error)
            assert error < 1e-10, (N, n, primes, crossing, shell, response)
            if abs(M) == 1:
                A, B, signature_kind, _ = signature_probe.signature(N, primes, divisors)
                assert A == 0 and signature_kind == 'single-prime-log'
                assert B[0] == -M and all(b == 0 for b in B[1:])
                key = (len(primes), M)
                if key not in examples:
                    examples[key] = dict(n=n, primes=primes,
                        responseSign=M, criticalDivisors=shell,
                        labelCount=len(primes), exactIntegerCuts=True)
        magnitude = math.exp((N+1)*math.log(u)-1.5*T+
            (N+1)*math.log(T)-math.lgamma(N+1))/L
        for w in windows:
            if not w[0]*N < T <= w[1]*N:
                continue
            counts[w][len(primes)] += 1
            classes[w][kind] += 1
            gross[w][kind] += magnitude*abs(response)
            if not crossing:
                rank_pattern = ','.join(f'{k}:{v}' for k,v in
                    sorted(Counter(rank for _,_,rank in shell).items()))
                ranks[w][rank_pattern or 'empty'] += 1
                signs[w][f'count={len(primes)},prefix={M}'] += 1
            for y in heights:
                atom = -magnitude*response*cmath.exp(-1j*y*T)
                joined[w][y][kind] += atom
                net[w][y] += atom
    cases = []
    for w in windows:
        for y in heights:
            head = sum(m*(L-math.log(p))*cmath.exp(-1j*y*T)
                for p, _, m, T in data['headPairs'])
            assert abs(sum(joined[w][y].values())-net[w][y]) < 1e-11
            cases.append(dict(N=N, height=y, window=list(w),
                labels=sum(counts[w].values()), primeCounts=dict(sorted(counts[w].items())),
                responseClasses=dict(classes[w]), criticalRankPatterns=dict(ranks[w]),
                exactGapPrefixByLabelCount=dict(signs[w]),
                signedClassContributions={k:as_complex(v) for k,v in joined[w][y].items()},
                signedMain=as_complex(net[w][y]), signedFullHead=as_complex(head),
                signedJoint=as_complex(net[w][y]-head),
                diagnosticClassMagnitudes=dict(gross[w]),
                maxGapLogResponseError=max_gap_error,
                exactIntegerCriticalSupportRetained=True,
                everyCountAndOriginalComplexPhaseRetained=True,
                noCofinalFloorCertificate=True))
    return cases, list(examples.values())


def compare_signature_baseline(cases, path):
    """Use frozen, independently assembled label sums as a regression."""
    old = json.loads(path.read_text())
    index = {(x['N'], x['height'], tuple(x['window'])):x for x in old['cases']}
    checked = 0
    for row in cases:
        key = (row['N'], row['height'], tuple(row['window']))
        if key not in index:
            continue
        previous = index[key]
        assert row['labels'] == previous['labels']
        assert abs(row['signedMain']['re']-previous['signedMain']) < 1e-11
        assert abs(row['signedFullHead']['re']-previous['signedFullHead']) < 1e-11
        assert abs(row['signedJoint']['re']-previous['jointTotal']) < 1e-11
        checked += 1
    return checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[6,7])
    parser.add_argument('--heights', nargs='+', type=float, default=[54.,65.,100.])
    parser.add_argument('--output', type=Path,
        default=Path('.lake/riesz-balanced-critical-shell/probe.json'))
    args = parser.parse_args()
    assert all(3 <= N <= 8 for N in args.orders)
    assert all(y >= 54 for y in args.heights)
    cases, examples = [], []
    for N in args.orders:
        print(json.dumps(dict(event='preparing', order=N)), flush=True)
        rows, ex = run_order(N, args.heights)
        cases.extend(rows)
        examples.extend(dict(N=N, **v) for v in ex)
        for row in rows:
            print(json.dumps(row, allow_nan=False), flush=True)
    baseline = Path('.lake/riesz-balanced-signature/probe.json')
    regression_count = compare_signature_baseline(cases, baseline)
    paths = [Path(__file__), Path(base.__file__), Path(signature_probe.__file__), baseline]
    report = dict(schemaVersion=1, cases=cases, exactGapExamples=examples,
        frozenSignatureRegressions=regression_count,
        sources=[dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest())
            for p in paths],
        scope=dict(optionalOutsideBuildsCI=True, toyLength='-2N log(10001/20000)',
            exactIntegerDivisorCutoff=True, movingIntegerLength=False,
            nativeDyadicSchedule=False, fullNativeDeletionMasks=False,
            allCountSignedTotalsJoined=True, fullPrimeHeadUnchanged=True,
            noPerCountFittedWeights=True, noPhaseFreezing=True,
            noDensityOrExposedZeroHypothesis=True, previousEventualBudgetsApplied=False,
            noIndependentCofinalFloorBoundOrZeroExclusionInferred=True))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')


if __name__ == '__main__':
    main()
