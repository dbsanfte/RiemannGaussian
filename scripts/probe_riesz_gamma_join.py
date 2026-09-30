#!/usr/bin/env python3
"""Optional finite regression for the Gamma/count/complement alignment.

This is floating exploration, not a certificate. The test ordinates are not
asserted zeta zeros. In particular a finite set of primes does not satisfy a
selected-zero prime-completion hypothesis. The arithmetic diagnostic keeps
the stated masks; earlier adaptive support deletions are not certified at
this small order. It is a mask model, not the full literal coreResponse.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path

import mpmath as mp

from probe_riesz_selected_gamma import hinge_average


def subsets(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            break
        sub = (sub - 1) & mask


def orders(n):
    return [(j, h) for j in range(n + 2)
            for h in range(n + 2 - j)
            if 13*n < 40*(j+h) <= 27*n
            and 21*n <= 40*j <= 23*n and n <= 100*(h+1) <= 4*n]


def run():
    mp.mp.dps = 75
    n, count_cut = 320, 55
    u = mp.mpf(10001)/20000
    # Known Mersenne primes; arithmetic below uses their literal integers.
    exponents = [19, 61, 89, 107, 127, 521]
    primes = [2**k - 1 for k in exponents]
    logs = list(map(mp.log, primes))
    full = (1 << len(primes))-1
    sums = {s: sum(logs[i] for i in range(len(primes)) if s >> i & 1)
            for s in range(full+1)}
    cutoff = int(mp.floor(u**(-n)/(n+1)))
    length = 2*mp.log(cutoff+2)
    rect = orders(n)
    fact = [mp.factorial(k) for k in range(n+2)]

    def theta(t, a, b):
        total = t+a+b
        return sum(fact[n+1]/(fact[j]*fact[h]*fact[n+1-j-h])
                   *(t/total)**j*(a/total)**h*(b/total)**(n+1-j-h)
                   for j, h in rect)

    def riesz(s, d):
        if d <= 0 or (s.bit_count() > 1 and sums[s] <= d):
            return mp.mpf(0)
        return sum((-1)**v.bit_count()*max(0, d-sums[v]) for v in subsets(s))

    @lru_cache(None)
    def avg_hinge(j, mask):
        return hinge_average(j, u, length-sums[mask])

    @lru_cache(None)
    def avg_riesz(j, mask):
        return sum((-1)**v.bit_count()*avg_hinge(j, v) for v in subsets(mask))

    def old_share(mask):
        total = sums[mask]
        if mask.bit_count() < 3:
            return mp.mpf(0)
        return sum(mp.binomial(n+1, k)*((total-logs[i])/total)**k
                   *(logs[i]/total)**(n+1-k)
                   for i in range(len(primes)) if mask >> i & 1
                   for k in range(n+2)
                   if k <= 13*n//32 and 5*(n+1-k) < 4*n)

    labels = []
    for mask in range(1, full+1):
        ids = [i for i in range(len(primes)) if mask >> i & 1]
        total = sums[mask]
        flags = {
            "count": 3 <= len(ids) < count_cut,
            "core_window": mp.mpf(39)*n/20 < total <= mp.mpf(203)*n/100,
            "physical_annulus": length < total < 2*length,
            "nondominant": logs[ids[-1]] < mp.mpf(13)*total/20,
            "physical_primes": all(n*n < primes[i] < (cutoff+2)**2 for i in ids),
            "allocation_cancelling_sector_absent": not any(
                mp.mpf(17)/64 <= (total-logs[i])/total <= mp.mpf(11)/32 for i in ids),
        }
        if all(flags.values()):
            p, r = ids[-1], ids[0]
            th = theta(logs[p], logs[r], total-logs[p]-logs[r])
            wrong = sum(theta(logs[i], logs[r], total-logs[i]-logs[r])
                        for i in ids[1:-1])
            labels.append((mask, th, old_share(mask), wrong, flags))

    results = []
    for height in (0, 60):
        s0 = mp.mpf(3)/2 + mp.j*height
        kmax = max(n+1-j-h for j, h in rect)
        moments = {
            i: [logs[i]**k/fact[k]*mp.polylog(-k, mp.exp(-s0*logs[i]))
                for k in range(kmax+1)]
            for i in range(len(primes))
        }

        @lru_cache(None)
        def middle(mask):
            if not mask:
                return [mp.mpc(1)]+[mp.mpc(0)]*kmax
            i = (mask & -mask).bit_length()-1
            rest = middle(mask ^ (1 << i))
            return [sum(rest[a]*moments[i][k-a] for a in range(k+1))
                    for k in range(kmax+1)]

        selected = mp.mpc(0)
        for r in range(len(primes)):
            larger = full ^ ((1 << (r+1))-1)
            for middle_mask in subsets(larger):
                if not middle_mask:
                    continue
                response_mask = middle_mask | (1 << r)
                weights = middle(middle_mask)
                for j, h in rect:
                    selected += (u**(n+1-j)/j * logs[r]**h/fact[h]
                                 *mp.exp(-s0*logs[r])*weights[n+1-j-h]
                                 *avg_riesz(j, response_mask))
        selected *= -(n+1)/length

        packet = rest = core = mp.mpc(0)
        rows = []
        for mask, th, allocated, wrong, flags in labels:
            total = sums[mask]
            p = max(i for i in range(len(primes)) if mask >> i & 1)
            cofactor = mask ^ (1 << p)
            unshifted = riesz(cofactor, length)
            translated = riesz(cofactor, length-logs[p])
            marked_zero = (sums[cofactor]/total)**(n+1)
            atom = (-u**(n+1)*(n+1)/length*(1-allocated)*riesz(mask, length)
                    *total**(n+1)/fact[n+1]*mp.exp(-s0*total))
            translated_atom = (u**(n+1)*(n+1)/length*(1-allocated)*translated
                               *total**(n+1)/fact[n+1]*mp.exp(-s0*total))
            packet += th*atom
            rest += (1-th)*atom
            core += atom
            rows.append({
                "factor_exponents": [exponents[i] for i in range(len(primes)) if mask >> i & 1],
                "masks": flags, "rectangle_mass": str(th), "complement_mass": str(1-th),
                "old_allocation": str(allocated), "wrong_owner_mass": str(wrong),
                "mass_sum_error": str(abs(th+(1-th)-1)),
                "saturated_composite_cofactor": bool(sums[cofactor] <= length),
                "unshifted_cofactor_riesz": str(unshifted),
                "translated_atom_error": str(abs(atom-translated_atom)),
                "translated_complement_error": str(abs((1-th)*(atom-translated_atom))),
                "marked_zero_order_mass": str(marked_zero),
                "zero_order_bound": str(mp.mpf(2)**(n+1)/mp.mpf(3)**(n+1)),
                "positive_marked_mass": str(1-marked_zero),
            })
        encode = lambda z: {"real": str(mp.re(z)), "imag": str(mp.im(z))}
        results.append({
            "height": height, "mask_model_labels": rows,
            "scaled_selected_gamma": encode(selected),
            "scaled_mask_model_rectangle": encode(packet),
            "scaled_mask_model_complement": encode(rest),
            "scaled_mask_model_core": encode(core),
            "same_label_recombination_error": str(abs(packet+rest-core)),
            "selected_minus_mask_model": encode(selected-packet),
            "joint_defect_identity_error": str(abs((selected+rest-core)-(selected-packet))),
            "residual_scope": {
                "allocation_complement": "exactly zero on each matched arithmetic label",
                "least_prime_ordering": "retained in both finite expressions",
                "owner": "wrong-owner mass recorded per label; no asymptotic inference",
                "count": "Gamma cofactor includes all subsets; core model has at least three primes",
                "physical_cutoff": "fixed prime universe is rough, but virtual marked variable is continuous",
                "unshifted_hinge": "zero on saturated composite cofactors; checked per label",
                "unseparated": ["marked-prime measure and phase", "radial and label masks",
                                "Euler proper powers", "old allocation outside the matched labels"],
            },
        })

    # An independent finite all-count regression at a nontrivial cutoff.
    small = [17, 23, 29, 31]
    r, q = small[0], small[1:]
    d = mp.mpf(6)
    height = 60
    z = mp.mpf(3)/2+mp.j*height
    feat = [mp.exp(-z*mp.log(p)) for p in q]
    qmask = (1 << len(q))-1
    hinge = lambda x: max(0, x)-max(0, x-mp.log(r))
    left = right_sum = mp.mpc(0)
    for v in subsets(qmask):
        shift = sum(mp.log(q[i]) for i in range(len(q)) if v >> i & 1)
        right_sum += (-1)**v.bit_count()*mp.fprod(feat[i] for i in range(len(q)) if v >> i & 1)*hinge(d-shift)
        if v:
            weight = mp.fprod(feat[i]/(1-feat[i]) for i in range(len(q)) if v >> i & 1)
            kernel = sum((-1)**w.bit_count()*hinge(d-sum(mp.log(q[i]) for i in range(len(q)) if w >> i & 1))
                         for w in subsets(v))
            left += weight*kernel
    right = mp.fprod(1/(1-v) for v in feat)*right_sum-hinge(d)
    return {
        "scope": "Uncertified finite mask-model diagnostic, not literal coreResponse. No selected-zero hypothesis or cofinal bound.",
        "N": n, "u": str(u), "length": str(length), "count_cut": count_cut,
        "prime_exponents": exponents, "rectangle_order_count": len(rect),
        "all_count_euler_identity_error": str(abs(left-right)), "joint_checks": results,
        "unpaid": ["virtual-to-literal marked measure with the complementary orders and masks",
                   "virtual order-zero boundary (the matched literal boundary has a Lean geometric bound)",
                   "remaining shifted channels in a selected-mode-only decomposition"],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    content = json.dumps(run(), indent=2)+"\n"
    if args.output:
        args.output.write_text(content)
    print(content)
