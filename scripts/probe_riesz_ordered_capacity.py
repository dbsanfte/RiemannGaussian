#!/usr/bin/env python3
"""Deterministic four/five angular-envelope exploration, NOT a certificate.

The exact ordered caps and one-dimensional integration formulas are proved
in ZetaRieszOrderedCapacity.lean. This adaptive FLOATING-POINT computation
has no checked rounding, covering, symmetry, or arithmetic transport proof.
Its lower/upper names describe the intended analytic enclosure directions.
The output is a diagnostic outside ordinary CI, never a proof dependency.
"""

import argparse
import hashlib
import heapq
import json
import math
from pathlib import Path


LOW = 693 / 1015
HIGH = 139 / 195
LEAST = 1 / 100
LARGEST_FOUR = 601 / 1000
LOG_LOWER_TERMS = 8
LOG_UPPER_TERMS = 16


def log_polynomial(x, upper=False):
    """Lean's log_rational_bounds_sharp evaluated in unverified floating point."""
    if x <= 1:
        return 0.0
    count = LOG_UPPER_TERMS if upper else LOG_LOWER_TERMS
    z = (x - 1) / (x + 1)
    z2, term, value = z * z, z, 0.0
    for j in range(count):
        value += term / (2 * j + 1)
        term *= z2
    if upper:
        value += term / ((2 * count + 1) * (1 - z2))
    return 2 * value


def cap_integral(cap, low, high, total, upper=False):
    """Integrate min(r,cap)/(r*(total-r)); low=0 uses its right limit."""
    if cap <= 0 or high <= low:
        return 0.0
    assert 0 <= low < high < total
    seam = max(low, min(cap, high))
    value = log_polynomial((total - low) / (total - seam), upper)
    if high > seam:
        assert seam > 0
        value += cap / total * log_polynomial(
            high * (total - seam) / (seam * (total - high)), upper)
    if upper:
        value = min(value, log_polynomial((total - low) / (total - high), True))
    return value


def four_bounds(box, low, high):
    """Ordered p>=q>=a>=r, p+q+a+r=1; integrate r exactly first."""
    pl, ph, ql, qh = box
    sl, sh = 1 - ph - qh, 1 - pl - ql
    rl, rh = max(0, sl - qh), sh / 2
    cap_hi = max(0, min(high - pl, 1 - low - ql, 1 + ph - 2 * low))
    cap_lo = max(0, min(low - ph, 1 - high - qh, 1 + pl - 2 * high))
    if rl >= rh or cap_hi == 0:
        return 0.0, 0.0
    volume = (ph - pl) * (qh - ql)
    if rh >= sl:
        # A positive cap forces a>(low-LARGEST_FOUR)/2.
        upper = rh / (((low - LARGEST_FOUR) / 2) * low * pl * ql) * volume
    else:
        upper = cap_integral(cap_hi, rl, rh, sl, True) / (low * pl * ql) * volume
    rlo, rhi = max(0, sh - ql), sl / 2
    lower = (cap_integral(cap_lo, rlo, rhi, sh) / (high * ph * qh) * volume
             if rlo < rhi else 0.0)
    return lower, upper


def five_bounds(box, low, high, fibres):
    """Sum all three tents before integrating two symmetric large primes.

    The three large shares are x,y,z, x+y=v; small shares are b>=r,
    b+r=1-v-z. Dividing the unordered large triple by 3! and summing
    its three equal tent integrals gives 1/2. The x integral contributes
    2/v*log((v-d)/d), cancelling that 1/2 exactly.
    """
    vl, vh, zl, zh = box
    sl, sh = 1 - vh - zh, 1 - vl - zl
    if (vl >= low or zl >= 1 - high or sh <= 2 * LEAST or
            zh < high - vh or 2 * zh + vh < 2 * (1 - low) or
            3 * zh + vh < 1 or zh + 2 * vh < 1):
        return 0.0, 0.0
    rl, rh = max(LEAST, sh - zl, sh - vl / 2), sl / 2
    cap_lo = max(0, min(low - vh, 1 - high - zh))
    volume = (vh - vl) * (zh - zl)
    lower = 0.0
    if (rl < rh and cap_lo > 0 and vl >= 1 - low and
            vl + zl >= high and vl + 2 * zl >= 2 * (1 - low)):
        for i in range(fibres):
            a = rl + (rh - rl) * i / fibres
            b = rl + (rh - rl) * (i + 1) / fibres
            d = max(sh - a, 1 - low - zl, vh - 1 / 2)
            ratio = (vl - d) / d
            if ratio > 1:
                lower += (log_polynomial(ratio) * cap_integral(cap_lo, a, b, sh)
                          / (high * vh * zh) * volume)
    # This upper estimate only chooses subdivision priorities. The five
    # supply uses the positive lower sums, not this priority estimate.
    rlo, rhi = max(LEAST, sl - zh, sl - vh / 2), sh / 2
    cap_hi = max(0, min(low - vl, 1 - high - zl))
    if rlo >= rhi or cap_hi <= 0:
        return lower, lower
    d = max(sl - rhi, 1 - low - zh, vl - 1 / 2, LEAST)
    log_hi = log_polynomial(max(1, (vh - d) / d), True)
    if rhi < sl:
        upper = log_hi * cap_integral(cap_hi, rlo, rhi, sl, True)
    else:
        upper = log_hi * math.log(rhi / rlo)
    upper *= volume / (low * vl * zl)
    return lower, max(lower, upper)


def adaptive(bounds, root, count):
    serial = 0
    lower, upper = bounds(root)
    heap = [(-(upper - lower), serial, root, lower, upper)]
    splits = 0
    while heap and len(heap) < count:
        _, _, box, _, _ = heapq.heappop(heap)
        axis = 0 if box[1] - box[0] > box[3] - box[2] else 2
        midpoint = (box[axis] + box[axis + 1]) / 2
        left, right = list(box), list(box)
        left[axis + 1], right[axis] = midpoint, midpoint
        for child in (tuple(left), tuple(right)):
            lo, hi = bounds(child)
            assert 0 <= lo <= hi and math.isfinite(hi)
            if hi > 0:
                serial += 1
                heapq.heappush(heap, (-(hi - lo), serial, child, lo, hi))
        splits += 1
    return dict(lower=math.fsum(row[3] for row in heap),
                upper=math.fsum(row[4] for row in heap),
                active_cells=len(heap), splits=splits)


def main():
    global LOG_LOWER_TERMS, LOG_UPPER_TERMS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bins', type=int, default=8)
    parser.add_argument('--four-cells', type=int, default=30000)
    parser.add_argument('--five-cells', type=int, default=10000)
    parser.add_argument('--fibres', type=int, default=8)
    parser.add_argument('--padding', type=float, default=1/100000)
    parser.add_argument('--log-lower-terms', type=int, default=LOG_LOWER_TERMS)
    parser.add_argument('--log-upper-terms', type=int, default=LOG_UPPER_TERMS)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert min(args.bins, args.four_cells, args.five_cells, args.fibres,
               args.log_lower_terms, args.log_upper_terms) > 0
    assert 0 <= args.padding < 1/10000
    LOG_LOWER_TERMS, LOG_UPPER_TERMS = args.log_lower_terms, args.log_upper_terms
    rows = []
    for i in range(args.bins):
        low = LOW + (HIGH - LOW) * i / args.bins - args.padding
        high = LOW + (HIGH - LOW) * (i + 1) / args.bins + args.padding
        four = adaptive(lambda box: four_bounds(box, low, high),
                        (2 * low - 1, LARGEST_FOUR, (1 - LARGEST_FOUR) / 3, 1 - low),
                        args.four_cells)
        five = adaptive(lambda box: five_bounds(box, low, high, args.fibres),
                        (max(1 - low, high / 2), low, LEAST, 1 - high), args.five_cells)
        rows.append(dict(cutoff=[low, high], four=four, five=five,
                         ratio=five['lower'] / four['upper']))
    sources = [Path(__file__), Path('RiemannGaussian/ZetaRieszOrderedCapacity.lean'),
               Path('RiemannGaussian/ZetaRieszCapacityCheck.lean')]
    report = dict(
        status='UNVERIFIED_FLOATING_POINT_DIAGNOSTIC',
        normalization='Coefficient/log(n) with unordered harmonic simplex density',
        cutoff_range=['693/1015', '139/195'], four_largest_max='601/1000',
        five_largest_max='1/2', five_least_min='1/100',
        five_region='Three macro shares above both small shares; all pair macro sums >=1-low; macro total >=high',
        bins=args.bins, four_cells=args.four_cells, five_cells=args.five_cells,
        fibres=args.fibres, cutoff_padding=args.padding,
        log_lower_terms=LOG_LOWER_TERMS, log_upper_terms=LOG_UPPER_TERMS,
        minimum_ratio=min(row['ratio'] for row in rows), rows=rows,
        source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
        limitations=[
            'No directed rounding or kernel-checked finite cover; these numbers are not certified bounds.',
            'Lean proves the cap identities, signed atom inequalities, zero-endpoint formulas and cell enclosure lemmas.',
            'A Lean cap checker and one interior supply-cell bound are proved; this full enumeration is not checked.',
            'The angular symmetry/cover still needs formal transport.',
            'Allocation, original masks, phase-arc population comparison and disjoint spending remain obligations.',
            'No source-normalized prime-sum floor or zero exclusion follows.',
            'All positive-cosine contributions and all other prime counts remain signed.' ])
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'minimum_model_ratio': report['minimum_ratio'],
                      'status': report['status']}))


if __name__ == '__main__':
    main()
