#!/usr/bin/env python3
"""Regenerate the small exact owner-credit box table, not a prime certificate.

Rational arithmetic proposes 4-dimensional cubes in the already supported
five-prime region. Lean checks every coordinate inequality, every lower
score, uniqueness and the total. No floating-point result is trusted.
The table is intentionally small enough for the ordinary cached build.
"""

from fractions import Fraction as Q
from itertools import combinations
from math import prod
from pathlib import Path


def rows():
    eps, width = Q(1, 10**6), Q(9998, 10**6)
    lower, upper = Q(69, 100), Q(7, 10)
    result = []
    for index in combinations(range(2, 32), 4):
        a = [Q(i, 100)+eps for i in index]
        b = [x+width for x in a]
        p, pmin = 1-sum(a), 1-sum(b)
        if not (Q(1, 2)+Q(1, 1000) <= pmin and p <= Q(14, 25)
                and b[3]+eps <= pmin and 1-a[3]-a[2]+eps <= lower
                and upper+eps <= 1-b[1]-b[0]):
            continue
        cap = (min(a[0], max(0, min(lower-1+a[2]+a[1]+a[0], 1-upper-b[2])))
               + min(a[0], max(0, min(lower-1+a[3]+a[1]+a[0], 1-upper-b[3])))
               + min(a[0], max(0, min(lower-b[3]-b[2], sum(a)-upper))))
        score = width**4*cap/(upper*p*prod(b))
        numerator = (score*10**9).__floor__()
        if numerator > 0:
            result.append((*index, numerator))
    return result


def main():
    data = rows()
    target = Path(__file__).resolve().parents[1]/'RiemannGaussian/ZetaRieszFiveOwnerBoxes.lean'
    text = target.read_text()
    begin = '  -- BEGIN GENERATED EXACT BOXES\n'
    end = '  -- END GENERATED EXACT BOXES'
    left, tail = text.split(begin, 1)
    _, right = tail.split(end, 1)
    body = '  ['+',\n   '.join('('+','.join(map(str, r))+')' for r in data)+']\n'
    target.write_text(left+begin+body+end+right)
    print(f'{len(data)} boxes; checked target numerator {sum(r[4] for r in data)}/1000000000')


if __name__ == '__main__':
    main()
