#!/usr/bin/env python3
"""Optional whole-population signed interference audit, outside builds/CI.

Join every surviving toy count and the SAME complete signed prime head.
The Mobius cutoff is tested with integers; phases, factorial weights and
the full head allocation are unchanged. Cross terms are diagnostics of the
actual complex sum, not independently priced count allowances.

Grouping by a shared prime does NOT make incidences independent. In
particular, local least-prime cancellation is reported separately from
the cross-least-prime terms required for a whole signed bound.

This uses the frozen toy length -2N log u, not native moving integer length,
dyadic orders or deletion masks. No eventual budget, numerical certificate,
cofinal floor or zero exclusion is inferred.
"""

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
import probe_riesz_balanced_joint as base
from probe_riesz_balanced_signature import signature


def encode(z):
    return dict(re=float(z.real), im=float(z.imag))


def csum(values):
    return complex(math.fsum(z.real for z in values),
                   math.fsum(z.imag for z in values))


def complex_bins(keys, values, size):
    return (np.bincount(keys, weights=values.real, minlength=size)
            + 1j*np.bincount(keys, weights=values.imag, minlength=size))


def prepare(order):
    data = base.prepare(order, 10001/20000)
    count = len(data['labels'])
    totals = np.empty(count)
    amplitudes = np.empty(count)
    counts = np.empty(count, dtype=np.int16)
    least = np.empty(count, dtype=np.int32)
    owner = np.empty(count, dtype=np.int32)
    nonowner_overlap = np.zeros(count, dtype=bool)
    head_qs = {q for _, q, _, _ in data['headPairs']}
    overlap_rows, overlap_primes = [], []
    profile_counts = Counter()
    max_response_error = 0.
    for i, (n, primes, divisors) in enumerate(data['labels']):
        A, B, kind, _ = signature(order, primes, divisors)
        logs = [math.log(p) for p in primes]
        response = A*data['L']-math.fsum(b*x for b, x in zip(B, logs))
        literal = math.fsum(mu*max(data['L']-math.log(d), 0.)
                            for d, mu in divisors)
        max_response_error = max(max_response_error, abs(response-literal))
        assert abs(response-literal) < 1e-10
        T = math.log(n)
        magnitude = math.exp((order+1)*math.log(data['u'])-1.5*T
                            +(order+1)*math.log(T)-math.lgamma(order+1))/data['L']
        totals[i], amplitudes[i] = T, -response*magnitude
        counts[i], least[i], owner[i] = len(primes), primes[0], primes[-1]
        profile_counts[kind] += 1
        for p in primes:
            if p in head_qs:
                overlap_rows.append(i)
                overlap_primes.append(p)
                if p != primes[-1]:
                    nonowner_overlap[i] = True
        if len(primes) >= 4 and nonowner_overlap[i]:
            # Exact incidence certificate for these finite supplied labels.
            # The separate Lean theorem handles native moving length.
            assert A == 0 and all(b == 0 for b in B)
    head_T = np.array([T for _, _, _, T in data['headPairs']])
    head_a = np.array([-(data['L']-math.log(p))*m
                       for p, _, m, _ in data['headPairs']])
    head_least = np.array([min(p, q) for p, q, _, _ in data['headPairs']],
                         dtype=np.int32)
    head_second = np.array([q for _, q, _, _ in data['headPairs']], dtype=np.int32)
    max_least = int(max(max(least, default=0), max(head_least, default=0)))
    overlap_size = max(head_qs, default=0)+1
    return dict(N=order, u=data['u'], L=data['L'],
        T=totals, amplitude=amplitudes, counts=counts, least=least, owner=owner,
        nonowner_overlap=nonowner_overlap,
        head_T=head_T, head_amplitude=head_a, head_least=head_least,
        head_second=head_second, least_size=max_least+1,
        overlap_rows=np.array(overlap_rows, dtype=np.int32),
        overlap_primes=np.array(overlap_primes, dtype=np.int32),
        overlap_size=overlap_size, profiles=dict(profile_counts),
        max_response_error=max_response_error,
        min_head_least=int(min(head_least, default=0)),
        max_main_least=int(max(least, default=0)))


def experiment(data, height, window):
    N = data['N']
    keep = (window[0]*N < data['T']) & (data['T'] <= window[1]*N)
    weights = data['amplitude']*np.exp(-1j*height*data['T'])
    weights[~keep] = 0
    # Negative head is included in count 2; its complete old window stays.
    head = data['head_amplitude']*np.exp(-1j*height*data['head_T'])
    channels = {2: complex(head.sum())}
    least_channels = {2: complex_bins(data['head_least'], head, data['least_size'])}
    by_count = Counter(data['counts'][keep].tolist())
    for k in sorted(set(data['counts'].tolist())):
        selected = data['counts'] == k
        channels[int(k)] = complex(weights[selected].sum())
        least_channels[int(k)] = complex_bins(data['least'][selected],
                                             weights[selected], data['least_size'])
    keys = sorted(channels)
    net = csum(channels.values())
    diagonal = math.fsum(abs(z)**2 for z in channels.values())
    cross = []
    for i, k in enumerate(keys):
        for ell in keys[i+1:]:
            cross.append(dict(counts=[k, ell],
                globalCross=2*(channels[k]*channels[ell].conjugate()).real,
                sameLeastPrime=2*np.vdot(least_channels[ell], least_channels[k]).real))
    signed_cross = math.fsum(row['globalCross'] for row in cross)
    positive_cross = math.fsum(max(row['globalCross'], 0.) for row in cross)
    negative_cross = math.fsum(min(row['globalCross'], 0.) for row in cross)
    assert abs(abs(net)**2-diagonal-signed_cross) < 2e-16
    joined_least = sum(least_channels.values())
    local_energy = float(np.vdot(joined_least, joined_least).real)
    local_diagonal = math.fsum(float(np.vdot(z, z).real)
                              for z in least_channels.values())
    local_cross = math.fsum(row['sameLeastPrime'] for row in cross)
    assert abs(local_energy-local_diagonal-local_cross) < 2e-16
    assert abs(joined_least.sum()-net) < 3e-13
    even = csum(channels[k] for k in keys if k % 2 == 0)
    odd = csum(channels[k] for k in keys if k % 2 == 1)
    shared_main = complex_bins(data['overlap_primes'],
        weights[data['overlap_rows']], data['overlap_size'])
    shared_head = complex_bins(data['head_second'], head, data['overlap_size'])
    incidence_cross = float(2*np.vdot(shared_head, shared_main).real)
    owner_keep = keep & (data['owner'] < data['overlap_size'])
    owner_profile = complex_bins(data['owner'][owner_keep], weights[owner_keep],
                                 data['overlap_size'])
    triple_nonowner = complex_bins(data['overlap_primes'],
        weights[data['overlap_rows']]*
        ((data['counts'][data['overlap_rows']] == 3) &
         (data['owner'][data['overlap_rows']] != data['overlap_primes'])),
        data['overlap_size'])
    # At head-support primes, all nonowner higher-count incidences vanish.
    selected = data['head_second']
    assert np.max(np.abs((shared_main-owner_profile-triple_nonowner)[selected]),
                  initial=0) < 3e-13
    owner_cross = float(2*np.vdot(shared_head, owner_profile).real)
    triple_cross = float(2*np.vdot(shared_head, triple_nonowner).real)
    assert abs(incidence_cross-owner_cross-triple_cross) < 2e-16
    indices = np.flatnonzero((shared_main != 0) & (shared_head != 0))
    ranked = sorted((dict(prime=int(p), main=encode(shared_main[p]),
                         negativeHead=encode(shared_head[p]),
                         cross=2*(shared_main[p]*shared_head[p].conjugate()).real)
                     for p in indices), key=lambda r: abs(r['cross']), reverse=True)
    top_least = sorted((dict(prime=int(p), joined=encode(joined_least[p]),
                            channels={str(k): encode(least_channels[k][p]) for k in keys
                                      if least_channels[k][p] != 0})
                        for p in np.flatnonzero(joined_least)),
                       key=lambda r: abs(complex(r['joined']['re'], r['joined']['im'])),
                       reverse=True)[:8]
    return dict(N=N, height=height, window=list(window),
        labels=sum(by_count.values()), labelsByCount=dict(sorted(by_count.items())),
        headPairs=len(head), unchangedHeadWindow=[1.95, 2.03],
        signedCountChannels={str(k): encode(v) for k, v in channels.items()},
        signedMain=encode(net-channels[2]), signedFullHead=encode(-channels[2]),
        joint=encode(net), diagonalCountEnergy=diagonal,
        jointEnergy=abs(net)**2, signedCrossCountEnergy=signed_cross,
        positiveCrossCountEnergy=positive_cross, negativeCrossCountEnergy=negative_cross,
        jointToDiagonal=(abs(net)**2/diagonal if diagonal else None),
        crossTerms=cross, even=encode(even), odd=encode(odd),
        parityCross=2*(even*odd.conjugate()).real,
        sameLeastPrimeJoinedEnergy=local_energy,
        sameLeastPrimeDiagonalEnergy=local_diagonal,
        signedSameLeastPrimeCrossEnergy=local_cross,
        crossLeastPrimeEnergy=abs(net)**2-local_energy,
        leastPrimeSupportsDisjoint=(data['max_main_least'] < data['min_head_least']),
        largestMainLeastPrime=data['max_main_least'],
        smallestHeadLeastPrime=data['min_head_least'],
        sharedMainHeadPrimeIncidences=len(indices),
        signedSharedPrimeIncidenceCross=incidence_cross,
        signedOwnerHeadPrimeCross=owner_cross,
        signedTripleNonownerHeadPrimeCross=triple_cross,
        higherCountNonownerOverlapLabels=int(np.sum(keep & data['nonowner_overlap'] &
                                                   (data['counts'] >= 4))),
        higherCountNonownerOverlapExactZeroByIntegerSignature=True,
        wholeSharedPrimeProfileIsOwnerPlusTripleNonowner=True,
        sharedPrimeIncidenceCrossIsNotWholeCarrierEnergy=True,
        dominantSharedPrimeIncidences=ranked[:8], dominantLeastPrimeChannels=top_least,
        allCountsAndSameFullComplexHeadRetained=True,
        noArtificialPrimeOrCountPhaseRotation=True,
        exactIntegerCutoffFloatingLogsPhases=True, cofinalFloorProved=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders', type=int, nargs='+', default=[6, 7, 8])
    ap.add_argument('--heights', type=float, nargs='+',
                    default=[54., 64.75, 65., 65.25, 99.75, 100., 100.25])
    ap.add_argument('--scan', action='store_true',
                    help='Also scan actual logarithmic phase heights 54..102, step 2.')
    ap.add_argument('--output', type=Path,
                    default=Path('.lake/riesz-joint-interference/probe.json'))
    args = ap.parse_args()
    assert all(3 <= n <= 8 for n in args.orders)
    heights = sorted(set(args.heights) | (set(range(54, 103, 2)) if args.scan else set()))
    assert all(y >= 54 for y in heights)
    regression_path = Path('.lake/riesz-balanced-critical-shell/probe.json')
    frozen = {(r['N'], r['height'], tuple(r['window'])): r
              for r in json.loads(regression_path.read_text())['cases']}
    cases, regressions = [], 0
    for N in args.orders:
        print(json.dumps(dict(event='prepare', N=N)), flush=True)
        data = prepare(N)
        for height in heights:
            for window in [(1.95, 2.03), (1.971, 2.029)]:
                row = experiment(data, height, window)
                key = N, height, window
                if key in frozen:
                    old = frozen[key]
                    for name, other in [('signedMain', 'signedMain'),
                                        ('signedFullHead', 'signedFullHead'),
                                        ('joint', 'signedJoint')]:
                        z, w = row[name], old[other]
                        assert abs(complex(z['re']-w['re'], z['im']-w['im'])) < 3e-12
                    regressions += 1
                cases.append(row)
        selected = [r for r in cases if r['N'] == N]
        print(json.dumps(dict(event='complete', N=N, cases=len(selected),
            minimumJointToDiagonal=min(r['jointToDiagonal'] for r in selected),
            maximumJointToDiagonal=max(r['jointToDiagonal'] for r in selected),
            adverseCases=sum(r['joint']['re'] < 0 for r in selected),
            reinforcedCases=sum(r['signedCrossCountEnergy'] > 0 for r in selected),
            leastPrimeSupportDisjoint=all(r['leastPrimeSupportsDisjoint'] for r in selected))),
            flush=True)
    sources = [Path(__file__), Path(base.__file__),
               Path('scripts/probe_riesz_balanced_signature.py'), regression_path]
    report = dict(schemaVersion=1, cases=cases, frozenComplexRegressions=regressions,
        sourceHashes=[dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                      for p in sources],
        scope=dict(optionalOutsideBuildsCI=True, integerToyIntervalExhausted=True,
            everyRemainingToyCountAndSameFullHead=True,
            originalMobiusSignsPhaseFactorialAndAllocationKept=True,
            noSeparatedCountBudget=True, noIncidenceIndependenceAssumption=True,
            noCofinalSavingPercentClaim=True, noPrimeDensityApproximation=True,
            toyLength='-2N log(10001/20000)', nativeMovingLength=False,
            nativeDyadicSchedule=False, fullNativeDeletionMasks=False,
            previousEventualBudgetsApplied=False, numericalCertificate=False,
            floorCeilingContradictionOrZeroExclusionProved=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(json.dumps(dict(cases=len(cases), regressions=regressions, goalStillOpen=True)),
          flush=True)


if __name__ == '__main__':
    main()
