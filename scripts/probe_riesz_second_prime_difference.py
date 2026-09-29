#!/usr/bin/env python3
"""Optional second-prime extraction diagnostic; never a CI certificate.

Compare identical actual-prime labels in the full central radial window.
All factorial allocation weights and the full cosine phase are retained.
Costs omit the unevaluated sqrt(E), earlier nested core deletions and the
remaining sectors. No asymptotic bound follows from these finite probes.
"""
# Copyright (c) 2026 David Sanftenberg. Apache-2.0.
import math, json
import numpy as np
from probe_riesz_retained_discrepancy import coefficients
from probe_riesz_sieve_mean import arithmetic
from probe_riesz_central_prime_difference import balanced

def probe(N, r, s):
    u = 10001 / 20000
    y = 54.0
    upper = (math.floor(u ** (-N) / (N + 1)) + 2) ** 2
    L = math.log(upper)
    pop = math.floor(math.exp(2.029 * N) / (N * N + 1))
    cap = pop // (r * s)
    (mu, phi) = arithmetic(max(pop, upper))
    ints = np.arange(len(phi))
    primes = np.flatnonzero((phi == ints - 1) & (ints >= 2))
    ps = primes[(primes > N * N) & (primes < upper)]
    fs = [[] for _ in range(cap + 1)]
    for q in primes[primes <= cap]:
        for n in range(int(q), cap + 1, int(q)):
            fs[n].append(int(q))
    blocks = []
    labels = 0
    maxreg = 0.0

    def F(k, lp, two):
        g = np.minimum(lp[:, None], np.maximum(L - np.log(k), 0)[None, :]) - np.minimum(lp[:, None], np.maximum(L - math.log(r) - np.log(k), 0)[None, :])
        if two:
            g -= np.minimum(lp[:, None], np.maximum(L - math.log(s) - np.log(k), 0)[None, :]) - np.minimum(lp[:, None], np.maximum(L - math.log(r * s) - np.log(k), 0)[None, :])
        return g
    for b in range(cap.bit_length()):
        low = 2 ** b
        end = min(2 * low, cap)
        if end <= low:
            continue
        P = ps[(np.log(ps) + math.log(r * s * end) > 1.971 * N) & (np.log(ps) + math.log(r * s * low) <= 2.029 * N)]
        if not len(P):
            continue
        lp = np.log(P)
        rows = []
        for n in range(max(2, low + 1), end + 1):
            if mu[n] == 0 or not fs[n] or min(fs[n]) <= s:
                continue
            factors = [r, s, *fs[n]]
            logs = np.log(factors)
            v = math.log(r * s * n)
            T = lp + v
            mask = (T > 1.971 * N) & (T <= 2.029 * N) & (lp < 0.65 * T) & (P > max(factors))
            if not mask.any():
                continue
            elig = [math.log(q) for q in factors if N * N < q < upper]
            poly = coefficients(N, logs, elig) @ lp[None, :] ** np.arange(N + 2)[:, None]
            W = -poly * np.exp(-T / 2) / (r * s * n * P) * np.cos(y * T) * u ** (N + 1) / (L * math.factorial(N))
            rows.append(W * mask)
            labels += int(mask.sum())
            if len(rows) <= 10:
                ds = [1]
                for q in fs[n]:
                    ds += [q * d for d in ds]
                ds = np.array(ds)
                all_d = np.concatenate([ds, r * ds, s * ds, r * s * ds])
                direct = np.minimum(lp[:, None], np.maximum(0.0, L - np.log(all_d))[None, :]) @ mu[all_d]
                maxreg = max(maxreg, float(np.max(abs(F(ds, lp, True) @ mu[ds] - direct))))
        if not rows:
            continue
        A = np.array(rows)
        k = np.arange(1, end + 1, dtype=float)
        kk = np.arange(1, s * end + 1, dtype=float)
        V = F(k, lp, True)
        D = (V[:, :-1] - V[:, 1:]) * np.sqrt(k[:-1])
        V0 = F(kk, lp, False)
        D0 = (V0[:, :-1] - V0[:, 1:]) * np.sqrt(kk[:-1])
        assert np.max(np.sum(D * D, axis=1)) <= 6 * math.log(r) + 1e-08
        good = P >= r * s
        if any(good):
            assert np.max(np.sum(D[good] * D[good], axis=1)) <= 4 * math.log(r) + 1e-08
        old = balanced(A, D0, s * end)
        new = balanced(A, D, end)
        blocks.append(dict(end=end, onePrimeCost=old, twoPrimeCost=new))
    print(json.dumps(dict(N=N, primes=[r, s], labels=labels, onePrimeCost=sum((b['onePrimeCost'] for b in blocks)), twoPrimeCost=sum((b['twoPrimeCost'] for b in blocks)), maxIdentityError=maxreg, blocks=blocks)), flush=True)

def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-order', type=int, default=10, choices=[6, 8, 10])
    args = parser.parse_args()
    for N in [6, 8, 10]:
        if N <= args.max_order:
            for pair in [(2, 3), (2, 5), (3, 5)]:
                probe(N, *pair)
if __name__ == '__main__':
    main()
