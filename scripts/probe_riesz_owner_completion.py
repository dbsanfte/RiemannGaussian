#!/usr/bin/env python3
"""Optional go/no-go test of completion after shared-owner cancellation.

Keep the unchanged balanced main and SAME full signed prime correction.
The completed cofactor row keeps squarefreeness, coprimality, the actual
factorial weight and full phase. The new ordinary-prime subtraction and
nonowner semiprime boundary are explicit, never paid by the counting error.

This uses the frozen toy length, not native orders/deletion masks. Floating
discrepancies are diagnostics, not proofs of a rate or a cofinal floor.
No new Lean carrier, prime-phase approximation or prime-density error is
introduced. The model density is that of squarefree integers with specified
divisibility/coprimality; it is NOT a prime-density approximation.
"""

import argparse
import cmath
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import probe_riesz_balanced_joint as base


def encode(z):
    return dict(re=float(z.real), im=float(z.imag))


def decode(z):
    return complex(z['re'], z['im'])


def total(values):
    values = tuple(values)
    return complex(math.fsum(z.real for z in values),
                   math.fsum(z.imag for z in values))


def prepare(N):
    data = base.prepare(N, 10001/20000)
    qs = sorted({q for _, q, _, _ in data['headPairs']})
    assert qs
    maximum = max(math.floor(math.exp(2.03*N-math.log(q))) for q in qs)
    spf, prime = base.arithmetic(maximum)
    factored = [None, []]+[base.factors(a, spf) for a in range(2, maximum+1)]
    divisors = {a: base.signed_divisors(ps) for a, ps in enumerate(factored)
                if a > 0 and ps is not None}
    rows, density_rows, prime_rows, main_rows = [], [], [], []
    by_count, nonowner_higher = Counter(), 0
    physical = 20000**(2*N)//10001**(2*N)
    assert physical == data['physical']
    # Re-evaluate the ENTIRE original balanced main independently, using
    # exact active-face integers to protect analytic zeros. Do not obtain
    # a purported total regression by just decoding the frozen main.
    for n, ps, ds in data['labels']:
        A, B = 0, [0]*len(ps)
        for mask, (d, mu) in enumerate(ds):
            if d > physical:
                continue
            A += mu
            for i in range(len(ps)):
                if mask & (1 << i):
                    B[i] += mu
        response = A*data['L']-math.fsum(z*math.log(p) for z, p in zip(B, ps))
        T = math.log(n)
        amplitude = math.exp((N+1)*math.log(data['u'])-1.5*T
            +(N+1)*math.log(T)-math.lgamma(N+1))/data['L']
        main_rows.append((T, -response*amplitude))
    for q in qs:
        c, b = math.log(q), data['L']-math.log(q)
        D = physical//q
        assert 0 < b and D < q
        # Exact finite squarefree-marked divisor scalar. Each specified
        # dividing prime contributes 1/(p+1); coprimality at q contributes
        # q/(q+1) because q exceeds the entire divisor cutoff.
        density = (6/math.pi**2)*(q/(q+1))*math.fsum(
            mu*(b-math.log(d))/math.prod(p+1 for p in factored[d])
            for d in range(1, D+1) if factored[d] is not None
            for mu in [(-1)**len(factored[d])])
        low = math.floor(math.exp(1.95*N-c))
        high = math.floor(math.exp(2.03*N-c))
        for a in range(low+1, high+1):
            T = c+math.log(a)
            amplitude = math.exp((N+1)*math.log(data['u'])-1.5*T
                +(N+1)*math.log(T)-math.lgamma(N+1))/data['L']
            density_rows.append((T, density*amplitude))
            ps = factored[a]
            if ps is None or q in ps:
                continue
            if prime[a]:
                # The whole ordinary-prime boundary; NOT the unchanged
                # original head and NOT an error term.
                assert a > D
                prime_rows.append((T, b*amplitude, q, a))
                continue
            if len(ps) < 2:
                continue
            # The exact rational cutoff selects the Riesz divisor face.
            A, B = 0, [0]*len(ps)
            for mask, (d, mu) in enumerate(divisors[a]):
                if d > D:
                    continue
                A += mu
                for i in range(len(ps)):
                    if mask & (1 << i):
                        B[i] += mu
            response = A*b-math.fsum(z*math.log(p) for z, p in zip(B, ps))
            literal = math.fsum(mu*max(b-math.log(d), 0.) for d, mu in divisors[a])
            assert abs(response-literal) < 1e-10
            owner = q > max(ps)
            count = len(ps)+1
            by_count[count] += 1
            if count >= 4 and not owner:
                assert A == 0 and all(z == 0 for z in B)
                nonowner_higher += 1
            rows.append((T, response*amplitude, count, owner, q, a))
    return dict(data=data, rows=rows, density=density_rows, prime=prime_rows, main=main_rows,
                headCofactors=len(qs), completeIncidences=dict(by_count),
                nonownerHigherIncidencesExactlyZero=nonowner_higher)


def experiment(prepared, height, window, frozen):
    data, rows = prepared['data'], prepared['rows']
    N, L = data['N'], data['L']
    keep = lambda T: window[0]*N < T <= window[1]*N
    phase = lambda T: cmath.exp(-1j*height*T)
    owned, nonowner_triples, higher, composite = [], [], [], []
    for T, amplitude, count, owner, _q, _a in rows:
        if not keep(T):
            continue
        z = amplitude*phase(T)
        composite.append(z)
        if owner:
            owned.append(z)
        elif count == 3:
            nonowner_triples.append(z)
        else:
            assert amplitude == 0.
        if count >= 4:
            higher.append(z)
    owned, tri, higher, comp = map(total, [owned, nonowner_triples, higher, composite])
    assert abs(comp-owned-tri) < 3e-13
    prime = total(amplitude*phase(T) for T, amplitude, _, _ in prepared['prime'] if keep(T))
    density = total(amplitude*phase(T) for T, amplitude in prepared['density'] if keep(T))
    discrepancy = comp+prime-density
    old = frozen[(N, height, window)]
    main, head = decode(old['signedMain']), decode(old['signedFullHead'])
    direct_main = total(amplitude*phase(T) for T, amplitude in prepared['main'] if keep(T))
    assert abs(main-direct_main) < 3e-13
    direct_head = total((L-math.log(p))*weight*phase(T)
                       for p, _, weight, T in data['headPairs'])
    assert abs(head-direct_head) < 3e-13
    # Match by the ACTUAL integer label, not by phase or an incidence
    # average. A larger original owner is never in the cofactor support,
    # so each overlapping prime-pair label has only one new marked row.
    old_by_label = {p*q: (p, q, weight, T)
                    for p, q, weight, T in data['headPairs'] if keep(T)}
    matched_prime, unmatched_prime, matched_old = [], [], []
    matched_labels, reinforcing_ratios = set(), []
    for T, amplitude, q, a in prepared['prime']:
        if not keep(T):
            continue
        z = amplitude*phase(T)
        old_pair = old_by_label.get(q*a)
        if old_pair is None:
            unmatched_prime.append(z)
            continue
        p, old_q, weight, old_T = old_pair
        assert q == old_q and a == p and q*a not in matched_labels
        assert abs(T-old_T) < 1e-12
        old_amplitude = (L-math.log(p))*weight
        assert amplitude >= old_amplitude > 0.
        matched_labels.add(q*a)
        matched_prime.append(z)
        matched_old.append(old_amplitude*phase(T))
        reinforcing_ratios.append(amplitude/old_amplitude)
    assert len(matched_labels) == len(old_by_label)
    matched_prime, unmatched_prime, matched_old = map(
        total, [matched_prime, unmatched_prime, matched_old])
    assert abs(matched_prime+unmatched_prime-prime) < 3e-13
    rest = main-owned
    joined = direct_main-direct_head
    assert abs(joined-decode(old['signedJoint'])) < 3e-13
    recombined = rest+discrepancy+density-prime-tri-head
    assert abs(recombined-joined) < 4e-13
    absolute_prime = math.fsum(abs(amplitude) for T, amplitude, _, _ in prepared['prime'] if keep(T))
    absolute_tri = math.fsum(abs(amplitude) for T, amplitude, k, owner, _, _ in rows
                            if keep(T) and k == 3 and not owner)
    return dict(N=N, height=height, window=list(window),
        sameFullOriginalHead=encode(head), originalBalancedMain=encode(main),
        actualJoint=encode(joined), sharedOwnerMain=encode(owned),
        sharedHigherCountMain=encode(higher), nonsharedMainRest=encode(rest),
        completeCompositeRow=encode(comp), nonownerTripleBoundary=encode(tri),
        newOrdinaryPrimeBoundary=encode(prime), signedSquarefreeDensityMain=encode(density),
        signedCountingDiscrepancy=encode(discrepancy), exactRecombinedJoint=encode(recombined),
        joinedBoundary=encode(-prime-tri-head),
        newPrimePlusTriple=encode(prime+tri),
        newPrimeBoundaryOnOriginalHeadLabels=encode(matched_prime),
        newPrimeBoundaryOffOriginalHeadLabels=encode(unmatched_prime),
        originalHeadOnMatchedCentralLabels=encode(matched_old),
        jointBoundaryOnIdenticalLabels=encode(-matched_prime-matched_old),
        matchedHeadLabels=len(matched_labels),
        everyOriginalCentralHeadLabelMatchedExactlyOnce=True,
        bothOriginalMainAndFullHeadIndependentlyReevaluated=True,
        newToOriginalPositiveAmplitudeMinimum=min(reinforcing_ratios),
        identicalLabelBoundariesReinforceBeforePhase=True,
        primeBoundaryMagnitude=abs(prime), countingDiscrepancyMagnitude=abs(discrepancy),
        primeBoundaryIsNotPaidByCountingDiscrepancy=True,
        absolutePrimeBoundaryDiagnostic=absolute_prime,
        absoluteNonownerTripleDiagnostic=absolute_tri,
        headCofactors=prepared['headCofactors'],
        nonownerHigherIncidencesExactlyZero=prepared['nonownerHigherIncidencesExactlyZero'],
        fullComplexPhaseOriginalFactorialAndAllCountsRetained=True,
        noNewBoundaryDeclaredSmall=True, noCofinalFloorProved=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders', type=int, nargs='+', default=[6, 7])
    ap.add_argument('--output', type=Path,
                    default=Path('.lake/riesz-owner-completion/probe.json'))
    args = ap.parse_args()
    assert all(N in [6, 7, 8] for N in args.orders)
    frozen_path = Path('.lake/riesz-balanced-critical-shell/probe.json')
    frozen = {(r['N'], r['height'], tuple(r['window'])): r
              for r in json.loads(frozen_path.read_text())['cases']}
    cases = []
    for N in args.orders:
        print(json.dumps(dict(event='prepare', N=N)), flush=True)
        data = prepare(N)
        for height in [54., 65., 100.]:
            for window in [(1.95, 2.03), (1.971, 2.029)]:
                row = experiment(data, height, window, frozen)
                cases.append(row)
                print(json.dumps({k: row[k] for k in ['N', 'height', 'window',
                    'actualJoint', 'sharedOwnerMain', 'newOrdinaryPrimeBoundary',
                    'nonownerTripleBoundary', 'signedCountingDiscrepancy']}, allow_nan=False),
                      flush=True)
    sources = [Path(__file__), Path(base.__file__), frozen_path]
    report = dict(schemaVersion=1, cases=cases, frozenComplexTotalRegressions=len(cases),
        sources=[dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sources],
        scope=dict(optionalOutsideBuildsCI=True, finiteToyIntegersExhausted=True,
            allCountsAndSameFullCorrectionRetained=True,
            squarefreeIntegerDensityNotPrimeDensity=True,
            everyNewPrimeAndTripleBoundaryKept=True,
            ownerFreeCompletionNotDeclaredDecay=True,
            noOrdinaryPrimeBoundaryNormPayment=True,
            toyLength='-2N log(10001/20000)', nativeMovingLength=False,
            nativeDyadicSchedule=False, fullNativeDeletionMasks=False,
            noPreviousNativeBudgetApplied=True, numericalCertificate=False,
            floorCeilingContradictionOrZeroExclusionProved=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(json.dumps(dict(cases=len(cases), regressions=len(cases), goalStillOpen=True)), flush=True)


if __name__ == '__main__':
    main()
