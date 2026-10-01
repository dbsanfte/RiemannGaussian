#!/usr/bin/env python3
"""Optional actual-integer regression of unpaid short-block cancellation.

Use the existing original-core transcription and moving Riesz length.
Select the two smallest cofactor primes, keep all four divisor incidences
and their common allocation/factorial/complex observation, and compare the
joined block with the absolute values of its separate incidences.

This tests transcription and floating algebra. It does not certify prime
logarithms, a cofinal schedule, a population estimate or the global floor.
"""

import argparse
from collections import Counter
import json
import math
import random
import time

import mpmath as mp
from sympy import factorint, isprime, nextprime

from probe_riesz_canonical_joint import core_mask, parameters, subset_rows


def diagnose(n, label, factors, pars, count_ceiling):
    mask = core_mask(n, label, factors, pars, count_ceiling)
    if mask != "core":
        return {"mask": mask, "selected": False}
    primes = sorted(factors)
    p, r, s = primes[-1], primes[0], primes[1]
    a, block = label//p, r*s
    total, owner = math.log(label), math.log(p)
    cutoff, defect = total-3899*n/2000, total-pars["length"]
    log_block = math.log(block)
    admissible = owner < 243*n/200 and log_block < cutoff and log_block <= defect
    selected = admissible and (defect <= owner or owner+log_block <= defect)
    if not admissible:
        return {"mask": mask, "selected": False,
                "coreCount": len(primes)}
    terms, old_paid_overlap = [], 0
    for d in (1, r, s, block):
        b = a//d
        assert d*b == a
        sign = (-1)**(len(primes)-1-(0 if d == 1 else 2 if d == block else 1))
        outer = math.log(p*b)
        hinge = max(outer-pars["length"], 0)-max(math.log(b)-pars["length"], 0)
        terms.append(sign*hinge)
        if outer <= 3899*n/2000:
            old_paid_overlap += 1
    joined, absolute = sum(terms), sum(abs(v) for v in terms)
    reflected = math.log(a)-pars["length"]
    log_r, log_s = math.log(r), math.log(s)
    tent = (max(reflected, 0)-max(reflected-log_r, 0)
            -max(reflected-log_s, 0)+max(reflected-log_r-log_s, 0))
    predicted = -(-1)**(len(primes)-1)*tent
    assert abs(joined-predicted) <= 2e-11*max(1.0, absolute)
    if selected:
        assert abs(joined) <= 2e-11*max(1.0, absolute)
    assert old_paid_overlap == 0
    riesz = sum(sign*max(pars["length"]-math.log(b), 0)
                for b, _, sign in subset_rows(factors))
    return {
        "mask": mask, "selected": selected, "rawBlockEligible": True,
        "hingeCrossing": not selected, "coreCount": len(primes),
        "unitJoinedWithNonunits": True, "divisorTerms": terms,
        "joinedCoefficient": joined, "separateAbsoluteCoefficient": absolute,
        "fullReflectedCoefficient": -riesz,
        "predictedSignedCofactorTent": predicted,
        "floatingTentIdentityError": abs(joined-predicted),
        "previousPaidOverlap": old_paid_overlap,
        "normalizedBlockLog": log_block/n,
        "normalizedShortCutoff": cutoff/n,
        "normalizedReflectedCutoff": defect/n,
        "normalizedOwnerLog": owner/n,
    }


def diagnose_orbits(n, label, factors, pars, count_ceiling):
    """Keep all disjoint based blocks and the two retained boundaries."""
    mask = core_mask(n, label, factors, pars, count_ceiling)
    if mask != "core":
        return {"mask": mask, "selectedOrbits": 0}
    primes = sorted(factors)
    p, r, s = primes[-1], primes[0], primes[1]
    a, block = label//p, r*s
    total, owner = math.log(label), math.log(p)
    cutoff, defect = total-3899*n/2000, total-pars["length"]
    log_r, log_s = math.log(r), math.log(s)
    log_block = log_r+log_s
    # Only the base changes: every incidence still has the observation at p*a.
    base_factors = {q: 1 for q in primes[2:-1]}
    selected = short = retained = overlap = 0
    selected_terms, selected_absolute = [], 0.0
    crossing_causes, witness_bases = Counter(), []
    all_orbit_error, max_selected_error = 0.0, 0.0
    seen = set()
    for e, e_count, _ in subset_rows(base_factors):
        log_e = math.log(e)
        admissible = (owner < 243*n/200 and log_e+log_block < cutoff
                      and log_e+log_block <= defect)
        chosen = admissible and (defect-log_e <= owner
                                 or owner+log_e+log_block <= defect)
        terms, short_members = [], 0
        for delta, delta_count in ((1, 0), (r, 1), (s, 1), (block, 2)):
            d = e*delta
            assert d not in seen
            seen.add(d)
            b = a//d
            assert d*b == a
            sign = (-1)**(len(primes)-1-e_count-delta_count)
            outer = math.log(p*b)
            hinge = max(outer-pars["length"], 0)-max(math.log(b)-pars["length"], 0)
            terms.append(sign*hinge)
            if math.log(d) < cutoff:
                short += 1
                short_members += 1
                if not chosen:
                    retained += 1
            if chosen and outer <= 3899*n/2000:
                overlap += 1
        def tent(x):
            return (max(x, 0)-max(x-log_r, 0)-max(x-log_s, 0)
                    +max(x-log_r-log_s, 0))
        predicted = (-1)**(len(primes)-1-e_count)*(tent(defect-log_e)
                     -tent(math.log(a)-pars["length"]-log_e))
        joined = math.fsum(terms)
        err = abs(joined-predicted)
        all_orbit_error = max(all_orbit_error, err)
        assert err <= 2e-11*max(1., sum(abs(v) for v in terms))
        if chosen:
            selected += 1
            selected_terms.extend(terms)
            selected_absolute += sum(abs(v) for v in terms)
            max_selected_error = max(max_selected_error, abs(joined))
            assert abs(joined) <= 2e-11*max(1., selected_absolute)
            assert short_members == 4
            if len(witness_bases) < 12:
                witness_bases.append(log_e/n)
        elif short_members and owner < 243*n/200 and pars["length"] <= 3899*n/2000:
            if log_e+log_block >= cutoff:
                cause = "short_cutoff_crossing"
                assert cutoff-log_block-1e-11 <= log_e < cutoff
            else:
                cause = "reflected_hinge_crossing"
                y = math.log(a)-pars["length"]
                assert y-log_block-1e-11 < log_e < y+1e-11
            crossing_causes[cause] += short_members
    assert len(seen) == 2**(len(primes)-1)
    assert overlap == 0
    return {
        "mask": mask, "coreCount": len(primes), "selectedOrbits": selected,
        "selectedOriginalIncidences": 4*selected,
        "originalShortIncidences": short, "retainedShortIncidences": retained,
        "retainedCrossings": dict(crossing_causes),
        "maximumFloatingOrbitIdentityError": all_orbit_error,
        "maximumFloatingSelectedError": max_selected_error,
        "jointSelectedCoefficient": math.fsum(selected_terms),
        "separateAbsoluteSelectedCoefficient": selected_absolute,
        "previousPaidOverlap": overlap,
        "selectedBaseLogShares": witness_bases,
        "commonOriginalWeightRetained": True,
        "populationMassCertified": False, "floorCertified": False,
    }


def run(n, samples, seed, count_ceiling):
    start = time.monotonic()
    pars = parameters(n, 32)
    masks, selected_counts = Counter(), Counter()
    selected, largest_error, absolute = 0, 0.0, 0.0
    orbits, orbit_incidences, retained_short = 0, 0, 0
    for i in range(samples):
        rng = random.Random((seed << 48)+(n << 32)+i)
        cell = rng.randrange(32)
        lo, hi = pars["edges"][cell:cell+2]
        label = rng.randrange(lo+1, hi+1)
        factors = {int(p): int(e) for p, e in factorint(label).items()}
        assert math.prod(p**e for p, e in factors.items()) == label
        assert all(isprime(p) for p in factors)
        row = diagnose(n, label, factors, pars, count_ceiling)
        orbit_row = diagnose_orbits(n, label, factors, pars, count_ceiling)
        orbits += orbit_row["selectedOrbits"]
        orbit_incidences += orbit_row.get("selectedOriginalIncidences", 0)
        retained_short += orbit_row.get("retainedShortIncidences", 0)
        masks[row["mask"]] += 1
        if row["selected"]:
            selected += 1
            selected_counts[row["coreCount"]] += 1
            largest_error = max(largest_error, abs(row["joinedCoefficient"]))
            absolute += row["separateAbsoluteCoefficient"]
    return {
        "N": n, "samples": samples, "seed": seed,
        "seconds": time.monotonic()-start,
        "coreMasks": dict(masks), "selectedLabels": selected,
        "selectedCounts": dict(selected_counts),
        "maximumFloatingBlockError": largest_error,
        "summedSeparateAbsoluteCoefficients": absolute,
        "selectedDisjointOrbits": orbits,
        "selectedOrbitIncidences": orbit_incidences,
        "retainedShortIncidences": retained_short,
        "eventualLengthHypothesisMet": pars["length"] >= 11*n/8,
        "cofinalScheduleTested": False, "floorCertified": False,
        "populationMassCertified": False,
    }


def witness(n, family="cancelled"):
    start = time.monotonic()
    # Six genuine primes; the selected small block is NOT the entire response.
    shares = ((.7, .615, .55, .059, .03, .013, .012, .011, .01) if family == "orbits"
              else (.61, .59, .55, .135, .064, .018, .012, .011, .01) if family == "orbit_crossing"
              else (.7, .615, .55, .103, .015, .017) if family == "cancelled"
              else (.61, .59, .55, .218, .015, .017) if family == "crossing6"
              else (.61, .59, .55, .112, .106, .015, .017))
    with mp.workdps(max(80, int(.65*n/math.log(10))+40)):
        primes = [int(nextprime(int(mp.exp(mp.mpf(str(x))*n)))) for x in shares]
    assert len(set(primes)) == len(shares) and all(isprime(p) for p in primes)
    label = math.prod(primes)
    cutoff = 20000**n//(10001**n*(n+1))
    physical = (cutoff+2)**2
    u = 10001/20000
    tilt = 1/(-2*math.log(u))
    log_rate = (2-2*tilt)*math.log(u)-math.log(tilt)
    with mp.workdps(80):
        trial = min(int(mp.exp(-n*log_rate/(2*(tilt+2.5)))), cutoff+1)
    pars = dict(length=math.log(physical), physical=physical, trial=trial)
    row = diagnose(n, label, dict.fromkeys(primes, 1), pars, 64)
    assert row["rawBlockEligible"]
    assert row["selected"] == (family in ("cancelled", "orbits"))
    return {
        "N": n, "seconds": time.monotonic()-start,
        "family": family, "labelDigits": len(str(label)), "count": len(shares),
        "eventualLengthHypothesisMet": pars["length"] >= 11*n/8,
        "movingLengthRatio": pars["length"]/n,
        "result": row,
        "basedOrbits": diagnose_orbits(n, label, dict.fromkeys(primes, 1), pars, 64),
        "cofinalScheduleTested": False,
        "nonemptinessCertified": False, "floorCertified": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="*", default=[24, 28, 32])
    parser.add_argument("--samples", type=int, default=256)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--count-ceiling", type=int, default=64)
    parser.add_argument("--witness-orders", type=int, nargs="*", default=[])
    parser.add_argument("--crossing-witness-orders", type=int, nargs="*", default=[])
    parser.add_argument("--orbit-witness-orders", type=int, nargs="*", default=[])
    args = parser.parse_args()
    if any(n < 16 for n in args.orders) or args.samples < 1:
        parser.error("orders >=16 and samples >=1 required")
    for n in args.orders:
        print(json.dumps({"scope": __doc__, "result": run(
            n, args.samples, args.seed, args.count_ceiling)}), flush=True)
    for n in args.witness_orders:
        print(json.dumps({"scope": __doc__, "witness": witness(n)}), flush=True)
    for n in args.crossing_witness_orders:
        for family in ("crossing6", "crossing7"):
            print(json.dumps({"scope": __doc__, "witness": witness(n, family)}), flush=True)
    for n in args.orbit_witness_orders:
        for family in ("orbits", "orbit_crossing"):
            print(json.dumps({"scope": __doc__, "witness": witness(n, family)}), flush=True)
