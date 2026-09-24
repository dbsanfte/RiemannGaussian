#!/usr/bin/env python3
"""Exploratory log-density model of the literal triple/five-prime packet.

NOT a Lean certificate and NOT a count of actual primes. Prime density is
replaced by dx/log(x). The moving Riesz length, factorial rectangle and
binomial allocation can be retained inside this explicitly labelled model.
All five-prime signs are independently checked by all 32 divisor subsets.

Run with a Python environment containing numpy and scipy. No ordinary
build or CI invokes this optional numerical probe.
"""
import argparse
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy
from scipy.stats import binom, qmc

PLO, PHI, RLO, RHI = 21/40, 113/200, 1/100, 3/100


def subset_hinge(shares, cutoff):
    answer = np.zeros(len(shares))
    for mask in itertools.product((0, 1), repeat=shares.shape[1]):
        answer += (-1)**sum(mask)*np.maximum(0, cutoff-shares@np.asarray(mask))
    return answer


def three_hinge(b, c, r, d):
    return (np.maximum(0, d)-np.maximum(0, d-b)-np.maximum(0, d-c)-np.maximum(0, d-r)
            +np.maximum(0, d-b-c)+np.maximum(0, d-b-r)+np.maximum(0, d-c-r)
            -np.maximum(0, d-b-c-r))


def sample_packet(power, seed, lam, n=None, total_log=None):
    z = qmc.Sobol(4, scramble=True, seed=seed).random_base2(power)
    p = PLO+(PHI-PLO)*z[:, 0]
    r = RLO+(RHI-RLO)*z[:, 1]
    q = 1-p-r
    alo, ahi = q/3, q-2*r
    a = alo+(ahi-alo)*z[:, 2]
    blo, bhi = (q-a)/2, np.minimum(a, q-a-r)
    b = blo+(bhi-blo)*z[:, 3]
    c = q-a-b
    d = lam-p
    shares = np.column_stack((p, a, b, c, r))
    region = (a >= d) & (d > b) & (d > c+r) & (d <= b+c+r)
    region &= (p > a) & (a > b) & (b > c) & (c > r)
    first = region & (d <= b+r)
    second = region & (d > b+r) & (d <= b+c)
    third = region & (d > b+c)
    reduced = np.where(first, b-d, np.where(second, -r, np.where(third, d-b-c-r, 0)))
    # Independent 32-subset enumeration on a deterministic prefix.
    take = min(len(shares), 8192)
    original = subset_hinge(shares[:take], lam)
    sign_error = np.max(np.abs((original+reduced[:take])[region[:take]]), initial=0.0)
    jac = (PHI-PLO)*(RHI-RLO)*(ahi-alo)*(bhi-blo)
    density = -reduced/(lam*np.prod(shares, axis=1))*jac
    # The entire ordered five-prime log-share box, including both signs.
    # The cofactor is saturated throughout this scan (1-p <= lambda).
    # This diagnostic is not the selected packet: its complement is reported.
    assert np.all(1-p <= lam)
    full_response = three_hinge(b, c, r, d)-three_hinge(b, c, r, d-a)
    full_density = full_response/(lam*np.prod(shares, axis=1))*jac
    full_subset_error = np.max(np.abs(original+full_response[:take]), initial=0.0)
    raw = density.copy()
    allocation = np.zeros(len(p))
    if n is not None:
        allocation = allocated_fraction(n, shares)
        physical = r*total_log > 2*math.log(n)
        density *= (1-allocation)*physical
        full_density *= (1-allocation)*physical
    pieces = [float(np.mean(density*m)) for m in (first, second, third)]
    return {
        "quintuple": sum(pieces), "regions": pieces,
        "quintuple_raw": float(np.mean(raw)),
        "allocated_loss": float(np.mean(raw*allocation)),
        "hinge_max_absolute_error": float(sign_error),
        "full_box_subset_error": float(full_subset_error),
        "full_five_box_signed": float(np.mean(full_density)),
        "full_five_box_positive": float(np.mean(np.maximum(full_density, 0))),
        "full_five_box_negative_magnitude": float(np.mean(np.maximum(-full_density, 0))),
        "outside_packet_signed": float(np.mean(full_density+density)),
        "p": p, "r": r, "weighted": density,
    }


def allocated_fraction(n, shares):
    # unpaidOrders = lowerWing minus reserveOrders minus highOrders.
    low = max((n+1)//8+1, (n+5)//5+1)
    high = (13*n)//32
    return np.sum(binom.cdf(high, n+1, 1-shares)-binom.cdf(low-1, n+1, 1-shares), axis=1)


def rectangle_fraction(n, p, r):
    result = np.zeros_like(p)
    for j in range((21*n+39)//40, (23*n)//40+1):
        lo = max(0, (n+99)//100-1, (13*n)//40+1-j)
        hi = min(n+1-j, (4*n)//100-1, (27*n)//40-j)
        if lo <= hi:
            result += binom.pmf(j, n+1, p)*(binom.cdf(hi, n+1-j, r/(1-p))-
                                               binom.cdf(lo-1, n+1-j, r/(1-p)))
    return result


def triple_integral(lam, n=None, total_log=None, degree=72, bounds=None):
    plo, phi, rlo, rhi = bounds or (PLO, PHI, RLO, RHI)
    z, w = np.polynomial.legendre.leggauss(degree)
    p, r = np.meshgrid(plo+(phi-plo)*(z+1)/2, rlo+(rhi-rlo)*(z+1)/2, indexing="ij")
    p, r = p.ravel(), r.ravel()
    weights = (np.outer(w, w)*(phi-plo)*(rhi-rlo)/4).ravel()
    q = 1-p-r
    density = 1/(lam*p*q)
    raw = float(weights@density)
    if n is not None:
        shares = np.column_stack((p, q, r))
        density *= rectangle_fraction(n, p, r)*(1-allocated_fraction(n, shares))
        density *= (r*total_log > 2*math.log(n)) & (q >= 1-lam) & (r < 1-lam)
    return float(weights@density), raw


def compact(row):
    return {k: v for k, v in row.items() if k not in ("p", "r", "weighted")}


def phase_diagnostic(triple, quintuple):
    """Exact common-phase test of the sampled densities, not a source limit.

    A positive quintuple surplus reverses its effect when cosine changes sign.
    Capping a matched packet leaves that surplus in the rest of the carrier.
    """
    return {
        "signed_density_triple_minus_quintuple": triple-quintuple,
        "common_phase_real": {str(c): (triple-quintuple)*c for c in (-1, -0.5, 0, 0.5, 1)},
        "unmatched_quintuple_after_capped_transport": max(0., quintuple-triple),
        "symmetric_relative_count_error_to_lose_surplus": (quintuple-triple)/(quintuple+triple),
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--power", type=int, default=18)
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    u = 10001/20000
    report = {"status": "exploratory continuous prime-density model; not certified and not actual prime counts",
              "numpy": np.__version__, "scipy": scipy.__version__, "sample_power": args.power,
              "seeds": args.seeds, "radius": u, "asymptotic": [], "moving_window": [], "finite_order": []}
    for lam in (-2*u*math.log(u),):
        trials = [sample_packet(args.power, s, lam) for s in range(args.seeds)]
        t, _ = triple_integral(lam)
        vals = [a["quintuple"] for a in trials]
        result = {"lambda": lam, "triple": t, "quintuple_mean": float(np.mean(vals)),
                  "seed_spread": max(vals)-min(vals), "ratio": float(np.mean(vals))/t,
                  "trials": [compact(a) for a in trials], "local_boxes": [],
                  "phase_diagnostic": phase_diagnostic(t, float(np.mean(vals)))}
        # Matching with p,r also frozen is stronger than matching total log only.
        trial = trials[0]
        for ip in range(4):
            for ir in range(4):
                plo, phi = PLO+(PHI-PLO)*ip/4, PLO+(PHI-PLO)*(ip+1)/4
                rlo, rhi = RLO+(RHI-RLO)*ir/4, RLO+(RHI-RLO)*(ir+1)/4
                selected = (trial["p"] >= plo)&(trial["p"] < phi)&(trial["r"] >= rlo)&(trial["r"] < rhi)
                qm = float(np.mean(trial["weighted"]*selected))
                tm, _ = triple_integral(lam, bounds=(plo, phi, rlo, rhi))
                result["local_boxes"].append({"p": [plo, phi], "r": [rlo, rhi], "triple": tm,
                                               "quintuple": qm, "ratio": qm/tm})
        report["asymptotic"].append(result)
    for slope in np.linspace(1.95, 2.05, 11):
        lam = -2*math.log(u)/slope
        row = sample_packet(args.power, 0, lam)
        t, _ = triple_integral(lam)
        report["moving_window"].append({"total_log_over_N": float(slope), "lambda": lam,
                                       "triple": t, "ratio": row["quintuple"]/t,
                                       "phase_diagnostic": phase_diagnostic(t, row["quintuple"]),
                                       **compact(row)})
    for n in (256, 640, 1536, 4096):
        total_log = n/u
        # Exact length differs from this stable expression by at most
        # 4*(n+1)*u**n, insignificant at these orders. This is reported, not hidden.
        ell = -2*n*math.log(u)-2*math.log(n+1)
        lam = ell/total_log
        row = sample_packet(args.power, 0, lam, n, total_log)
        t, traw = triple_integral(lam, n, total_log)
        report["finite_order"].append({"N": n, "total_log": total_log, "lambda": lam,
                                      "length_error_bound": 4*(n+1)*math.exp(n*math.log(u)),
                                      "triple": t, "triple_raw": traw,
                                      "ratio": row["quintuple"]/t if t else None, **compact(row)})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"asymptotic": [{k:v for k,v in x.items() if k not in ("trials", "local_boxes")}
                                     for x in report["asymptotic"]],
                      "moving_window_ratios": [[x["total_log_over_N"], x["ratio"]] for x in report["moving_window"]],
                      "finite_order": [[x["N"], x["triple"], x["quintuple"], x["ratio"]]
                                       for x in report["finite_order"]]}, indent=2))


if __name__ == "__main__":
    main()
