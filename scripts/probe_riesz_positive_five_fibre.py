#!/usr/bin/env python3
"""Optional, uncertified positive-five interior cost exploration.

Integrate the least-share cap before enclosing the three outer variables.
The second-largest share remains Q-r in the denominator. Floating-point
range calculations guide a possible later Lean certificate; this script
does NOT certify an integral, a literal prime count, or a signed sum.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import heapq
import itertools
import json
import math
from pathlib import Path


def shifted_integral(r0, upper, total, cap):
    seam = min(upper, r0 + cap)
    value = -r0 / total * math.log(seam / r0) if r0 > 0 else 0.0
    value -= (1 - r0 / total) * math.log((total - seam) / (total - r0))
    if upper > seam:
        value += cap / total * math.log(
            upper / seam * (total - seam) / (total - upper))
    return max(0.0, value)


def estimate(low, high, cells):
    owner = 119 / 200
    root = (((3 * low - 1) / 2, owner),
            ((low - owner) / 2, (1 - (3 * low - 1) / 2) / 3),
            ((low - owner) / 2, (1 - low) / 2))

    def enclosure(box):
        (pl, ph), (bl, bh), (al, ah) = box
        if bl >= ah:
            return 0.0
        upper = min(bh, 1 - pl - bl - 2 * al)
        r0 = max(0.0, low - ph - bh, 2 * low - 2 * ph - bh - ah)
        cap = min(high - pl, 1 + 2 * ph - 3 * low)
        if upper <= r0 or cap <= 0:
            return 0.0
        total = 1 - ph - bh - ah
        # q >= a and q >= total-r are kept together, including coarse cells.
        middle = min(upper, max(r0, total - al))
        integral = (shifted_integral(r0, middle, total, cap)
                    if middle > r0 else 0.0)

        def constant_denominator(end):
            seam = min(end, r0 + cap)
            value = seam - r0 - (r0 * math.log(seam / r0) if r0 > 0 else 0.0)
            if end > seam:
                value += cap * math.log(end / seam)
            return value

        if upper > middle:
            integral += (constant_denominator(upper)
                         - constant_denominator(middle)) / al
        return integral / (low * pl * bl * al) * math.prod(h - l for l, h in box)

    def best_split(box):
        options = []
        for axis in range(3):
            lo, hi = box[axis]
            midpoint = (lo + hi) / 2
            left = box[:axis] + ((lo, midpoint),) + box[axis + 1:]
            right = box[:axis] + ((midpoint, hi),) + box[axis + 1:]
            ul, ur = enclosure(left), enclosure(right)
            options.append((ul + ur, axis, left, right, ul, ur))
        return min(options, key=lambda x: x[0])

    serial, heap, rows = itertools.count(), [], []

    def push(box, value):
        if value:
            heapq.heappush(heap, (-value, next(serial), box, value, best_split(box)))

    total = enclosure(root)
    push(root, total)
    for k in range(1, cells + 1):
        _, _, _, old, split = heapq.heappop(heap)
        _, _, left, right, ul, ur = split
        total += ul + ur - old
        push(left, ul)
        push(right, ur)
        if k in {100, 1000, 10000, 30000, cells}:
            rows.append({'splits': k, 'positive_cells': len(heap),
                         'floating_enclosure_estimate': total})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cells', type=int, default=100000)
    parser.add_argument('--output', type=Path,
                        default=Path('docs/riesz-positive-five-fibre-probe.json'))
    args = parser.parse_args()
    if args.cells < 1:
        parser.error('--cells must be positive')
    intervals = [('existing central bin', Fraction(78068869, 113100000),
                  Fraction(26165377, 37700000)),
                 ('candidate tighter saddle bin; transfer not proved here',
                  Fraction(693, 1000), Fraction(1733, 2500))]
    payload = {
        'scope': 'Uncertified numerical exploration, not a Lean or arithmetic certificate.',
        'variables': 'P largest share; r<=b<=a<=q cofactor shares; q=1-P-b-a-r',
        'kernel': 'max(0,min(d,r,r+b-d,r+b+a-2*d,1-P-3*d)), d=lambda-P',
        'normalization': 'kernel/(lambda*P*r*b*a*q); radial factor and phase excluded',
        'largest_share_ceiling': '119/200',
        'rows': [{'cutoff_scope': label, 'low': str(lo), 'high': str(hi),
                  'refinements': estimate(float(lo), float(hi), args.cells)}
                 for label, lo, hi in intervals],
        'limitations': [
            'Floating-point errors and complete-cell enclosures are not checked in Lean.',
            'The refined saddle bin still needs its exact moving-length theorem.',
            'No original allocation, physical-mask or literal prime-count transfer is proved here.',
            'The cost cannot be spent in the joint floor or ceiling until those obligations are discharged.'
        ],
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    }
    args.output.write_text(json.dumps(payload, indent=2) + '\n')
    for row in payload['rows']:
        print(row['cutoff_scope'], row['refinements'][-1])


if __name__ == '__main__':
    main()
