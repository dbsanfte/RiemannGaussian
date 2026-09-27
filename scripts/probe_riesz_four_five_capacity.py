#!/usr/bin/env python3
"""Optional angular four/five-prime compensation probe, NOT a certificate.

Compare the positive four-prime coefficient with the negative five-prime
coefficient on the negative-cosine side. Within each cutoff-ratio interval,
take pointwise worst-case envelopes before numerical integration. Exact
hinges suffice to locate extrema of the piecewise-affine numerator divided
by the positive cutoff. Floating point and Sobol integration remain unproved.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from scipy.stats import qmc


def samples(k, power, seed, least):
    cuts = np.sort(qmc.Sobol(k - 1, scramble=True, seed=seed).random_base2(power), axis=1)
    free = 1 - k * least
    shares = least + free * np.diff(np.column_stack(
        (np.zeros(len(cuts)), cuts, np.ones(len(cuts)))), axis=1)
    density = free**(k - 1) / (math.factorial(k) * math.factorial(k - 1))
    return shares, density / np.prod(shares, axis=1)


def four_cost(x, lam):
    p = x[:, 0]
    return np.maximum(p + 1 - 2 * lam - np.sum(
        np.maximum(x[:, 1:] - (lam - p)[:, None], 0), axis=1), 0) / lam


def four_envelope(x, lo, hi):
    lower, upper = np.full(len(x), lo), np.full(len(x), hi)
    out = np.maximum(four_cost(x, lower), four_cost(x, upper))
    for i in (1, 2, 3):
        hinge = np.clip(x[:, 0] + x[:, i], lo, hi)
        out = np.maximum(out, four_cost(x, hinge))
    return out


def subset_hinges(x):
    sums, signs = np.zeros((len(x), 1)), np.ones(1)
    for column in x.T:
        sums = np.concatenate((sums, sums + column[:, None]), axis=1)
        signs = np.concatenate((signs, -signs))
    order = np.argsort(sums, axis=1)
    sums = np.take_along_axis(sums, order, axis=1)
    sign = signs[order]
    # At each hinge the new term is zero, so including it is harmless.
    response = sums * np.cumsum(sign, axis=1) - np.cumsum(sign * sums, axis=1)
    return sums, sign, response


def pair_balance(x, lam):
    """Signed five-prime minorant; lam is a matrix of rowwise cutoffs."""
    out = 3 - 4*lam
    for i in range(5):
        out = out + np.maximum(x[:, i, None] - (1-lam), 0)
        for j in range(i+1, 5):
            out = out - np.maximum(1-lam-x[:, i, None]-x[:, j, None], 0)
    return out


def five_envelopes(x, edges):
    out = np.empty((len(x), len(edges) - 1))
    pair_out = np.empty_like(out)
    max_identity_error = 0.
    for start in range(0, len(x), 8192):
        xx = x[start:start + 8192]
        sums, sign, response = subset_hinges(xx)
        pair_hinges = pair_balance(xx, sums)
        for j, (lo, hi) in enumerate(zip(edges[:-1], edges[1:])):
            raw_left = np.sum(sign * np.maximum(lo - sums, 0), axis=1)
            left = np.maximum(raw_left, 0) / lo
            right = np.maximum(np.sum(sign * np.maximum(hi - sums, 0), axis=1), 0) / hi
            valid = (sums >= lo) & (sums <= hi)
            hinge_values = np.where(valid, np.maximum(response, 0) / np.maximum(sums, lo), np.inf)
            out[start:start + len(xx), j] = np.minimum(
                np.minimum(left, right), np.min(hinge_values, axis=1))
            pair_left_raw = pair_balance(xx, np.full((len(xx), 1), lo))[:, 0]
            pair_left = np.maximum(pair_left_raw, 0)/lo
            pair_right = np.maximum(pair_balance(xx, np.full((len(xx), 1), hi))[:, 0], 0)/hi
            pair_hinge_values = np.where(
                valid, np.maximum(pair_hinges, 0)/np.maximum(sums, lo), np.inf)
            pair_out[start:start + len(xx), j] = np.minimum(
                np.minimum(pair_left, pair_right), np.min(pair_hinge_values, axis=1))
            # Reflection's discarded triple hinges are the large-pair excess.
            triple_credit = np.zeros(len(xx))
            for a in range(5):
                for b in range(a+1, 5):
                    triple_credit += np.maximum(xx[:, a]+xx[:, b]-lo, 0)
            active = np.max(xx, axis=1) <= 1/2
            max_identity_error = max(max_identity_error, float(np.max(np.abs(
                raw_left[active] - pair_left_raw[active] - triple_credit[active]))))
    assert max_identity_error < 1e-11
    assert np.max(pair_out - out) < 1e-11
    return out, pair_out, max_identity_error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--power', type=int, default=19)
    parser.add_argument('--seeds', nargs='+', type=int, default=[41, 73])
    parser.add_argument('--bins', type=int, default=12)
    parser.add_argument('--least-five', type=float, default=1/100)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert 0 < args.least_five < .2 and args.bins > 0
    edges = np.linspace(693/1015, 139/195, args.bins + 1)
    rows = []
    errors = []
    for seed in args.seeds:
        four, w4 = samples(4, args.power, seed, 0)
        four = np.sort(four, axis=1)[:, ::-1]
        w4 *= four[:, 0] <= 601/1000
        five, w5 = samples(5, args.power, seed, args.least_five)
        w5 *= np.max(five, axis=1) <= 1/2
        supply, pair_supply, err = five_envelopes(five, edges)
        errors.append(dict(seed=seed, reflected_identity_max_error=err))
        for j, (lo, hi) in enumerate(zip(edges[:-1], edges[1:])):
            cost = float(np.mean(w4 * four_envelope(four, lo, hi)))
            credit = float(np.mean(w5 * supply[:, j]))
            pair_credit = float(np.mean(w5 * pair_supply[:, j]))
            entry = dict(seed=seed, cutoff_lo=float(lo), cutoff_hi=float(hi),
                         four_cost_upper_model=cost, five_credit_lower_model=credit,
                         ratio=credit/cost, five_pair_minorant_lower_model=pair_credit,
                         pair_minorant_ratio=pair_credit/cost)
            rows.append(entry)
            print(entry, flush=True)
    sources = [Path(__file__)]
    report = dict(
        scope='Uncertified angular density comparison; no literal prime-sum bound',
        normalization='Coefficient/log(n); radial factorial and complex phase omitted',
        samples_per_seed=2**args.power, seeds=args.seeds, bins=args.bins,
        four_largest_max='601/1000', five_largest_max='1/2',
        five_least_min=args.least_five, cutoff_range=['693/1015', '139/195'],
        minimum_ratio=min(row['ratio'] for row in rows), rows=rows,
        minimum_pair_minorant_ratio=min(row['pair_minorant_ratio'] for row in rows),
        identity_errors=errors,
        source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
        limitations=[
            'The interval envelopes are evaluated in floating point, not certified arithmetic.',
            'Sobol scrambles do not give a rigorous integration error bound.',
            'The four-prime upper model sets the unassigned allocation fraction to one.',
            'The five-prime lower model also omits allocation; its eventual error must be paid.',
            'Actual masks, counts, radial weights, phase cells and prior supply spending still require a proof.',
            'No signed prime-density transport or cofinal numerical floor follows.',
            'Opposing positive-cosine terms and all other counts stay in the signed rest.' ])
    args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
