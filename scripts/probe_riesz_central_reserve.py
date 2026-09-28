#!/usr/bin/env python3
"""Evaluate the scalar central-credit rate, not the literal prime sum.

The Lean inequalities are eventual, with an unevaluated starting order.
These numbers therefore do not certify a prime-sum bound at any listed N.
The diagnostic makes delayed growth visible without rerunning any cover.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--radius', type=float, default=10001/20000)
    parser.add_argument('--height', type=float, default=54)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    assert .5 < args.radius <= 10001/20000 and abs(args.height) >= 54
    constant = math.pi*args.radius*math.exp(-1)/(24000*abs(args.height))
    rows = []
    for n in [256, 640, 1536, 4096, 16384, 65536, 262144, 1048576]:
        log_credit = math.log(constant)+n*math.log(2*args.radius)-math.log(n+1)
        rows.append(dict(order=n, log_scalar_credit=log_credit,
                         scalar_credit=math.exp(log_credit)))
    payload = dict(scope='Floating-point evaluation of a proved eventual scalar rate; not a prime-sum certificate at these orders.',
                   radius=args.radius, height=args.height,
                   formula='pi*u*exp(-1)/(24000*abs(y)) * (2*u)^N/(N+1)',
                   constant=constant, rows=rows,
                   limitations=[
                       'The starting order of the literal prime-sum comparison is unevaluated.',
                       'No value of coreResponse or its signed complement is computed.',
                       'Positive and negative comparisons have different signed complements.',
                       'No whole-carrier floor, ceiling or zero exclusion follows.'],
                   source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if args.output:
        args.output.write_text(json.dumps(payload, indent=2)+'\n')
    else:
        print(json.dumps(payload, indent=2))


if __name__ == '__main__':
    main()
