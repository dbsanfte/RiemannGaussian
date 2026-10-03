#!/usr/bin/env python3
"""Optional paid-incidence/cutoff-price diagnostic; outside builds and CI.

Enumerate complete divisor inventories for the literal cubic-crossing labels.
Keep the WHOLE native allocation in the old increment and the canonical-owner
allocation in the paid increment. Join both counts and every cutoff period
before pricing. This is a diagnostic of the exact incidence ledger, not a
density sample, native count-cropped population, finite error certificate,
cofinal price bound or zero exclusion. Large period edges and logs float.
"""

import argparse
from collections import defaultdict
from itertools import combinations
import json
import math
from pathlib import Path

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_complex_null_profiles import period_edge
from probe_riesz_cubic_cutoff import literal_row
from probe_riesz_lower_radial import parameters


def subsets(primes):
    for count in range(len(primes)+1):
        for chosen in combinations(primes, count):
            yield math.prod(chosen), (-1)**count


def prepare(j):
    labels = []
    for count in (3, 5):
        row = literal_row(j, 54., count)
        n = row['N']
        pars = parameters(n)
        primes = sorted(map(int, row['exactOriginalFactorization']))
        p, r, q = primes[-1], primes[0], primes[1]
        label = math.prod(primes)
        total = math.log(label)
        assert core_mask(n, label, dict.fromkeys(primes, 1), pars, 2**(j+3)) == 'core'
        all_allocated = sum(allocation(n, pars['orders'], 1-math.log(v)/total)
                            for v in primes if n*n < v < pars['physical'])
        owner_allocated = allocation(n, pars['orders'], 1-math.log(p)/total)
        assert -1e-10 <= owner_allocated <= all_allocated <= 1+1e-10
        all_allocated = min(1., max(0., all_allocated))
        incidences = []
        seen = set()
        for middle, _ in subsets(primes[2:-1]):
            b = r*q*middle
            e = label//(p*b)
            outer = math.log(p*b)
            if not (3899*n/2000 < outer <= (39/20-1/2016)*n and
                    outer <= 3899*n/2000+math.log(r*q) and
                    outer+math.log(p) > 203*n/100 and math.log(p) < 243*n/200):
                continue
            hinge = lambda v: max(math.log(p*v)-pars['length'], 0.)-max(
                math.log(v)-pars['length'], 0.)
            if hinge(b) == 0:
                continue
            for delta, _ in subsets([r, q]):
                if math.log(delta) >= outer-3899*n/2000:
                    continue
                d, cofactor = e*delta, b//delta
                assert d*cofactor == label//p and (d, cofactor) not in seen
                seen.add((d, cofactor))
                parity = (-1)**sum(cofactor % v == 0 for v in primes)
                incidences.append((d, cofactor, parity, hinge(cofactor)))
        assert incidences
        labels.append(dict(label=label, primes=primes, largest=p, total=total,
                           all_unassigned=1-all_allocated, owner_unassigned=1-owner_allocated,
                           log_amplitude=row['sourceScaledLogAmplitude'],
                           incidences=incidences))
    return n, pars, labels


def experiment(j, heights):
    n, pars, rows = prepare(j)
    common_scale = max(row['log_amplitude'] for row in rows)
    endpoint = max(row['label'] for row in rows)
    events = defaultdict(lambda: [0., 0.])
    cases = []
    for height in heights:
        events.clear()
        expected_original = expected_paid = 0.
        for row in rows:
            amplitude = math.exp(row['log_amplitude']-common_scale)
            phase = math.cos(height*row['total'])
            original_weight = -amplitude*row['all_unassigned']*phase
            paid_weight = amplitude*row['owner_unassigned']*phase
            for d, sign in subsets(row['primes']):
                events[d][0] += original_weight*sign
                expected_original += original_weight*sign*max(pars['length']-math.log(d), 0.)
            for _, b, parity, hinge in row['incidences']:
                coefficient = paid_weight*parity
                # This is EXACTLY 1_{pb<=k}-1_{b<=k}, not a label deletion.
                events[b][1] -= coefficient
                events[row['largest']*b][1] += coefficient
                expected_paid += coefficient*hinge
        events[endpoint]  # Retain the full finite endpoint.
        points = sorted(events)
        original = paid = 0.
        groups = defaultdict(lambda: [0., 0.])
        unit = 2*math.pi/height
        for left, right in zip(points, points[1:]):
            original += events[left][0]
            paid += events[left][1]
            lo, hi = max(math.log(left), pars['length']), math.log(right)
            if hi <= lo:
                continue  # Both exact profiles are flat before the hinge.
            period = math.floor(lo/unit)
            while lo < hi:
                edge = min(hi, period_edge(period, unit))
                if edge <= lo:
                    period += 1
                    continue
                width = edge-lo
                groups[period][0] -= width*original
                groups[period][1] -= width*paid
                lo, period = edge, period+1
        original_total = math.fsum(g[0] for g in groups.values())
        paid_total = math.fsum(g[1] for g in groups.values())
        raw_price = math.fsum(max(-g[0], 0.) for g in groups.values())
        pruned_price = math.fsum(max(-(g[0]-g[1]), 0.) for g in groups.values())
        tolerance = 2e-8*max(1., raw_price, pruned_price, abs(expected_original), abs(expected_paid))
        assert abs(original_total-expected_original) <= tolerance
        assert abs(paid_total-expected_paid) <= tolerance
        assert -pruned_price-abs(paid_total) <= original_total+tolerance
        # A finite diagnostic must fund the actual total, not pretend the
        # eventual geometric theorem has a certified starting order here.
        funded_price = min(raw_price, pruned_price+abs(paid_total))
        assert -funded_price <= original_total+tolerance
        cases.append(dict(height=height, completeGroups=len(groups), rawPrice=raw_price,
                          prunedVariationPrice=pruned_price, signedPaidTotal=paid_total,
                          finitePriceWithActualTotal=funded_price,
                          finiteRescaledGain=raw_price-funded_price,
                          originalSignedTotal=original_total,
                          prunedSignedTotal=original_total-paid_total,
                          originalAbelResidual=original_total-expected_original,
                          paidIncidenceResidual=paid_total-expected_paid,
                          earlyPaidIncrement=0.,
                          eventualGeometricBudgetAppliedAtThisOrder=False))
    return dict(N=n, dyadicIndex=j, labels=len(rows),
                exactCompleteDivisorIncidences=sum(2**len(r['primes']) for r in rows),
                paidOriginalIncidences=sum(len(r['incidences']) for r in rows),
                originalCountCeiling=2**(j+3), nativeCountCeiling=2**(j+3)//864+1,
                nativeCountCropAdmitsLabels=False, sourceAmplitudeLogScale=common_scale,
                allOriginalMasksChecked=True, allAllocationDistinctFromOwnerAllocation=True,
                cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dyadic-index', nargs='+', type=int, choices=[1, 2], default=[1, 2])
    parser.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-paid-incidence/probe.json'))
    args = parser.parse_args()
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error('finite heights >=54 required')
    report = dict(schemaVersion=1, cases=[experiment(j, args.heights) for j in args.dyadic_index],
                  scope=dict(optionalOutsideBuildsCI=True, originalWholeAndOwnerAllocationsRetained=True,
                             countPeriodsJoinedBeforePricing=True, probabilityOrPopulationEstimate=False,
                             wholeNativePopulation=False, cofinalPriceBound=False, floorProved=False,
                             probablePrimes=True, floatingLogsPhases=True, largePeriodEdgesInterpolated=True,
                             nativeCountCropEmptyAtProbedOrders=True))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(json.dumps(report, indent=2, allow_nan=False))


if __name__ == '__main__':
    main()
