#!/usr/bin/env python3
"""Optional exact algebraic preflight before joined-pair statistical scans.

Collect unjoined factorial monomials with rational coefficients BEFORE
evaluating primes or phases. Incidence swaps preserve assigned leg orders;
the diagonal is retained exactly once. Actual-prime replay keeps the moving
length, radial correction, Selberg subtraction and literal period mask.
No complete support is substituted for the literal support. No floor credit.
"""

import argparse
from collections import defaultdict
from fractions import Fraction
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import numpy as np
from scipy.stats import binom

import probe_riesz_pair_joint as joint
import probe_riesz_pair_prefix as prefix
import probe_riesz_pair_structure as pair


def canonical_key(legs, support='same-prefix-support'):
    """Commute whole legs, never interchange their derivative orders."""
    return support, tuple(sorted(legs))


def term(component, orientation, left_order, right_order, constant=0, inverse_L=0,
         support='same-prefix-support'):
    a, b = orientation
    return dict(component=component, incidence=list(orientation),
        factorialOrders=[left_order, right_order], totalOrder=left_order+right_order,
        key=canonical_key(((a, left_order), (b, right_order)), support),
        constant=Fraction(constant), inverseL=Fraction(inverse_L),
        phaseIdentity='feature(s,left)*feature(s,right)=feature(s,left*right)')


def raw_terms(N, diagonal=False):
    M, K = N+1, 13*N//32
    orientations = [(0, 0)] if diagonal else [(0, 1), (1, 0)]
    out = []
    for a, b in orientations:
        for k in range(M+1):
            out.append(term('full_order_M', (a, b), k, M-k, Fraction(M, 2)))
        for k in range(M+2):
            out.append(term('full_order_M_plus_1', (a, b), k, M+1-k,
                            inverse_L=-Fraction(M*(M+1), 2)))
        for k in range(K+1):
            out.append(term('prefix_unlogged', (a, b), M-k, k, -M))
            out.append(term('prefix_shifted_log', (a, b), M-k+1, k,
                            inverse_L=M*(M-k+1)))
    return out


def survivor_terms(N, diagonal=False):
    M, K = N+1, 13*N//32
    orientations = [(0, 0)] if diagonal else [(0, 1), (1, 0)]
    out = []
    for a, b in orientations:
        for k in range(K+1, M-K):
            out.append(term('central_order_M', (a, b), k, M-k, Fraction(M, 2)))
        for k in range(K+1, M+1-K):
            out.append(term('central_order_M_plus_1', (a, b), k, M+1-k,
                            inverse_L=-Fraction(M*(M+1), 2)))
        for k in range(1, K+1):
            out.append(term('low_logged_order', (a, b), k, M+1-k, inverse_L=-M*k))
    return out


def collect(terms):
    grouped = defaultdict(lambda: [Fraction(0), Fraction(0)])
    for t in terms:
        grouped[t['key']][0] += t['constant']
        grouped[t['key']][1] += t['inverseL']
    return {key: tuple(value) for key, value in grouped.items()}


def equal_collections(left, right):
    return all(left.get(k, (0, 0)) == right.get(k, (0, 0)) for k in left.keys() | right.keys())


def encode_terms(terms):
    return [{**t, 'constant': str(t['constant']), 'inverseL': str(t['inverseL'])} for t in terms]


def exact_audit():
    checks, snapshots = [], []
    for N in (*range(97), 256, 640, 1536, 3584, 8192):
        for diagonal in (False, True):
            raw, remaining = raw_terms(N, diagonal), survivor_terms(N, diagonal)
            original, survivor = collect(raw), collect(remaining)
            assert equal_collections(original, survivor)
            endpoints = [key for key in original if any(k == 0 for _, k in key[1])]
            assert endpoints and all(original[key] == (0, 0) for key in endpoints)
            assert all(all(k > 0 for _, k in key[1]) for key in survivor)
            checks.append(dict(N=N, repeatedPrimeDiagonal=diagonal,
                unjoinedTerms=len(raw), distinctMonomials=len(original),
                exactlyZeroMonomials=sum(v == (0, 0) for v in original.values()),
                endpointMonomials=len(endpoints), allEndpointsCancel=True,
                survivors=len(survivor), coefficientCollectionsEqual=True))
            if N in (0, 8, 256):
                snapshots.append(dict(N=N, repeatedPrimeDiagonal=diagonal,
                    raw=encode_terms(raw), surviving=encode_terms(remaining)))
    # Negative controls: wrong orientation bookkeeping and deleting an
    # uncancelled endpoint are both detected; differing masks never match.
    N = 8
    raw, remaining = raw_terms(N), survivor_terms(N)
    missing = [t for t in raw if not (t['component'] == 'prefix_unlogged'
                                     and 0 in t['factorialOrders'])]
    assert not equal_collections(collect(missing), collect(remaining))
    same = term('a', (0, 1), 0, 2, 1)
    different = term('b', (1, 0), 2, 0, -1, support='different-mask')
    assert len(collect([same, different])) == 2
    swapped = term('b', (1, 0), 2, 0, -1)
    assert all(v == (0, 0) for v in collect([same, swapped]).values())
    wrong = term('b', (1, 0), 0, 2, -1)
    assert any(v != (0, 0) for v in collect([same, wrong]).values())
    return dict(checks=checks, templates=snapshots,
        negativeControls=dict(missingEndpointDetected=True, differentMasksKeptSeparate=True,
            swappedWholeLegsCancel=True, swappedOrdersWithoutLegsRejected=True),
        exactRationalCoefficients=True, algebraBeforePrimeEvaluation=True)


def complete_prime_regression():
    """Independent high-precision direct sums, not the sampled population."""
    mp.mp.dps = 90
    primes = [2, 3, 5, 7]
    records = []
    for N in (0, 1, 2, 8, 16, 32):
        M, K = N+1, 13*N//32
        L = mp.mpf(7)*(N+1)/5
        for y in (0, 54, 142):
            s = mp.mpf(3)/2+1j*y
            P = [sum(mp.log(p)**k/mp.factorial(k)*mp.exp(-s*mp.log(p)) for p in primes)
                 for k in range(M+2)]
            central = M/2*sum(P[k]*P[M-k] for k in range(K+1, M-K))
            central -= M*(M+1)/(2*L)*sum(P[k]*P[M+1-k] for k in range(K+1, M+1-K))
            central -= M/L*sum(k*P[k]*P[M+1-k] for k in range(1, K+1))

            def direct(p, q):
                x, z = mp.log(p), mp.log(q)
                T = x+z
                F = lambda a: sum(mp.binomial(M, k)*(a/T)**k*(1-a/T)**(M-k)
                                  for k in range(K+1))
                Q = T*(1-T/L)-T/L*((L-x)*F(z)+(L-z)*F(x))
                return Q*T**N/mp.factorial(N)*mp.exp(-s*T)

            unordered = sum(direct(p, q) for i, p in enumerate(primes) for q in primes[i+1:])
            whole_diagonal = sum(direct(p, p) for p in primes)/2
            error = abs(unordered-(central-whole_diagonal))
            assert error < mp.mpf('1e-75')
            if N == 8 and y == 0:
                assert abs(unordered-central) > mp.mpf('1e-8')
                assert abs(unordered-(central-2*whole_diagonal)) > mp.mpf('1e-8')
            records.append(dict(N=N, height=y, primeUniverse=primes,
                exactUnorderedMultiplicityRetained=True, wholeDiagonalSubtractedOnce=True,
                absoluteReplayError=float(error), literalPopulation=False))
    return records


def component_profiles(N, L, x, z):
    """All unjoined pieces in units of the SAME positive kernel K_N.

    Binomial probabilities evaluate factorial ratios stably; they are not
    replaced by continuum indicators. No phase or literal mask is averaged.
    """
    M, K, T = N+1, 13*N//32, x+z
    px, pz = x/T, z/T
    Fx, Fz = binom.cdf(K, M, px), binom.cdf(K, M, pz)
    raw = dict(full_order_M=T, full_order_M_plus_1=-T*T/L,
        prefix_unlogged=-T*(Fx+Fz), prefix_shifted_log=T/L*(x*Fz+z*Fx))

    def middle(n, probability):
        # Two separately evaluated tails avoid 1-cdf cancellation.
        return binom.sf(K, n, probability)-binom.sf(n-K-1, n, probability)

    surviving = dict(
        central_order_M=T/2*(middle(M, px)+middle(M, pz)),
        central_order_M_plus_1=-T*T/(2*L)*(middle(M+1, px)+middle(M+1, pz)),
        low_logged_order=-T/L*(x*binom.cdf(K-1, M, px)+z*binom.cdf(K-1, M, pz)))
    return raw, surviving


def literal_replay(boxes):
    records, profiles = [], []
    for b in boxes:
        N, L = b['N'], pair.parameters(b['N'])['L']
        raw, remaining = component_profiles(N, L, b['x'], b['z'])
        R, S = sum(raw.values()), sum(remaining.values())
        Q, mask_error = prefix.comparison(N, L, b['x'], b['z'])
        c, T = b['coefficient'], b['T']
        completed = -T/L*(L-np.maximum(L-b['x'], 0)-np.maximum(L-b['z'], 0)+np.maximum(L-T, 0))
        radial_correction = -np.where(c['central'], 0, completed)
        par = pair.parameters(N)
        larger = np.array(b['p'], dtype=object)[:, None]
        smaller = np.array(b['q'], dtype=object)[None, :]
        head_mask = ((par['ownerLow'] <= larger) & (larger <= par['ownerHigh']) &
                     (N*N < larger) & (larger < par['physical']) & (N**3 < smaller))
        correction_mask = (par['ownerLow'] <= larger) & (larger <= par['physical'])
        literal_pieces = dict(
            original_riesz=np.where(c['central'], completed, 0.),
            original_allocated_head=np.where(head_mask,
                T/L*(L-b['x'])*(1-c['allocated']), 0.),
            original_unallocated_correction=-np.where(correction_mask,
                T/L*(L-b['x']), 0.))
        prefix_defect = S+radial_correction-c['selberg']
        literal_defect = S+mask_error+radial_correction-c['selberg']
        error = max(float(np.max(np.abs(R-Q))), float(np.max(np.abs(S-Q))),
                    float(np.max(np.abs(prefix_defect-b['prefixDefectCoefficient']))),
                    float(np.max(np.abs(literal_defect-
                        (c['joined']+radial_correction-c['selberg'])))),
                    float(np.max(np.abs(literal_defect-
                        (sum(literal_pieces.values())-c['selberg'])))))
        assert error < 1e-9*max(1., float(np.max(np.abs(Q))))
        # All component phases are the SAME literal product phase; the
        # positive normalization is common and is not a source-scale bound.
        y = 100
        pl, ep = joint.correlations.integer_height_phase(b['p'], y)
        qr, eq = joint.correlations.integer_height_phase(b['q'], y)
        phase = pl[:, None]*qr[None, :]
        keep = joint.exact_period_mask(b, y)
        ref = b['ref']
        kernel = np.exp(N*np.log1p((T-ref)/ref)-1.5*(T-ref))/N
        # This is the handoff to statistical discovery: evaluate only the
        # independently reconstructed SURVIVOR, with the original literal
        # corrections retained, after the exact coefficient audit passed.
        b['weights'] = prefix_defect*kernel
        weights = dict(raw, **remaining, **literal_pieces, owner_mask_difference=mask_error,
            radial_flag_correction=radial_correction, selberg_subtraction=-c['selberg'])
        signed = {name: pair.encode(complex(np.sum((value*kernel*phase)[keep])))
                  for name, value in weights.items()}
        joined_response = complex(np.sum((prefix_defect*kernel*phase)[keep]))
        actual_response = complex(np.sum((literal_defect*kernel*phase)[keep]))
        raw_response = sum(complex(np.sum((v*kernel*phase)[keep])) for v in raw.values())
        reduced_response = sum(complex(np.sum((v*kernel*phase)[keep])) for v in remaining.values())
        assert abs(raw_response-reduced_response) < 1e-8*max(1., abs(raw_response))
        records.append(dict(box=b['id'], N=N, seed=b['seed'], movingLength=L,
            sampledPairIncidences=int(T.size), retainedAtRegressionHeight=int(keep.sum()),
            height=str(y), components=signed, joinedPrefixDefect=pair.encode(joined_response),
            literalJoinedDefect=pair.encode(actual_response), geometryReplayMaxAbsoluteError=error,
            maskSignatures=dict(original_riesz='original central label flag',
                original_allocated_head='original owner/head/physical/rough flags with exact allocation',
                original_unallocated_correction='original owner/physical flags',
                allComponents='same literal complete-period support and full product phase'),
            differentOriginalMasksNotAlgebraicallyIdentified=True,
            phaseRadiusUpper=max(ep, eq), sourceScale=False, cofinalFloorCredit=0))
        # Retain the whole factorial row for a representative ACTUAL pair;
        # the generic exact ledger covers the other sampled incidences.
        x, z = float(b['x'][0, 0]), float(b['z'][0, 0])
        orders = np.arange(N+3)
        profiles.append(dict(box=b['id'], N=N, actualPrimes=[str(b['p'][0]), str(b['q'][0])],
            factorialIndices=orders.tolist(),
            massOrderM_p=binom.pmf(orders, N+1, x/(x+z)).tolist(),
            massOrderM_q=binom.pmf(orders, N+1, z/(x+z)).tolist(),
            massOrderMPlus1_p=binom.pmf(orders, N+2, x/(x+z)).tolist(),
            massOrderMPlus1_q=binom.pmf(orders, N+2, z/(x+z)).tolist(),
            originalOwnerOrderIndices=pair.unpaid_orders(N).tolist(),
            prefixIntegerEndpoint=13*N//32, oneRepresentativePairNotExhaustiveRows=True))
    return records, profiles


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old', type=Path, default=Path('.lake/riesz-pair-structure/scan.primes.json'))
    ap.add_argument('--new', type=Path, default=Path('.lake/riesz-pair-joint/new-primes.json'))
    ap.add_argument('--balanced', type=Path, default=Path('.lake/riesz-balanced-prime-sampling/result.primes.json'))
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-algebra/preflight.json'))
    ap.add_argument('--scan-survivors', action='store_true',
                    help='Run the existing coupled phase scan AFTER exact collection.')
    ap.add_argument('--height', default='100',
                    help='Exact height label for the optional survivor scan.')
    args = ap.parse_args()
    exact = exact_audit()
    regression = complete_prime_regression()
    boxes = joint.prepare(args.old, args.new, args.balanced)
    records, profiles = literal_replay(boxes)
    scanned = []
    if args.scan_survivors:
        grouped = defaultdict(list)
        for b in boxes:
            if b['kind'] == 'bulk':
                grouped[(b['N'], b['seed'])].append(b)
        for (N, seed), use in sorted(grouped.items()):
            summary, data, _ = joint.profile(use, args.height, np.arange(-64, 65)/64)
            scanned.append(dict(N=N, seed=seed, height=args.height, summary=summary, curves=data,
                exactAlgebraCompletedFirst=True, allSurvivingCouplingModesRetained=True,
                frequencyGridNotAUniformBound=True, referencePermutationsRun=False,
                regressionOnly=(args.height in ('100', '142')), cofinalFloorCredit=0))
    output = dict(classification='Exact algebraic preflight, followed by finite actual-prime replay',
        sources=[prefix.digest(p) for p in ('scripts/probe_riesz_pair_algebra.py',
            'RiemannGaussian/ZetaRieszPairPrefixConvolution.lean',
            'RiemannGaussian/ZetaRieszPairPrefixPayment.lean',
            'scripts/probe_riesz_pair_joint.py', args.old, args.new, args.balanced)],
        exactAlgebra=exact, completeFinitePrimeRegression=regression,
        literalComponents=records, factorialRowProfiles=profiles,
        survivorPhaseProfiles=scanned,
        coverage=dict(boxes=len(boxes), sampledPairIncidences=sum(b['T'].size for b in boxes),
            orders=sorted({b['N'] for b in boxes}), literalPhaseHeights=['100'],
            optionalSurvivorScanHeight=args.height if args.scan_survivors else None,
            regressionHeightAlreadyCoveredByZeroFreeRegions=True),
        limitations=dict(completeConvolutionNotIdentifiedWithLiteralSupport=True,
            ownerMaskDifferenceRetained=True, radialFlagCorrectionRetained=True,
            repeatedPrimeDiagonalRetainedExactlyOnce=True,
            sourceNormalizedIndependentSignedEstimate=False,
            allSamplesBelow65536=True, finiteSamplesNotCofinal=True),
        cofinalFloorCredit=0, floor=False, zeroExclusion=False, RH=False)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, allow_nan=False)+'\n')
    print(json.dumps(dict(output=str(args.output), exactCases=len(exact['checks']),
        actualSampledIncidences=output['coverage']['sampledPairIncidences'],
        maxReplayError=max(r['geometryReplayMaxAbsoluteError'] for r in records),
        orderZeroCancellationExact=True, floor=False)))


if __name__ == '__main__':
    main()
