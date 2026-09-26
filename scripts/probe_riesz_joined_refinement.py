#!/usr/bin/env python3
"""Optional refinement of the same coupled ball-arithmetic expression.

Use an independently checked positive-term binomial-tail algorithm in the
existing probe. The mathematical quadrature/lattice expression is unchanged;
its balls include the geometric truncation remainder of each binomial tail.
No continuum quadrature/grid error or actual prime-sum bound is claimed.
Inputs are hashed before execution and checked again before writing output.
Keep outside ordinary CI and exhaustive numerical-certificate workflows.
"""
import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path

import probe_riesz_joined_balls as joined
from riesz_binomial_balls import binomial_tail


def sources():
    root = Path(__file__).parent
    return {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in
            (Path(__file__).name, 'riesz_binomial_balls.py',
             'probe_riesz_joined_balls.py', 'requirements-riesz-balls.txt')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=65536)
    parser.add_argument('--grid', type=int, default=128)
    parser.add_argument('--tnodes', type=int, default=48)
    parser.add_argument('--rnodes', type=int, default=128)
    parser.add_argument('--pnodes', type=int, default=256)
    parser.add_argument('--bits', type=int, default=384)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if (args.order < 10000 or args.grid < 32 or args.bits < 256 or args.workers < 1
            or min(args.tnodes, args.rnodes, args.pnodes) < 2):
        parser.error('require N>=10000, grid>=32, bits>=256, positive workers, nodes>=2')
    frozen = sources()
    # Both algorithms enclose the same exact binomial probability. This
    # replacement changes only numerical evaluation, never the carrier.
    joined.binomial_tail = binomial_tail
    result = joined.run(args.order, args.grid, args.tnodes, args.rnodes,
                        args.pnodes, args.bits, args.workers)
    assert sources() == frozen, 'A running probe input changed; do not attribute its output'
    result['source_sha256'] = frozen
    result['binomial_evaluation'] = 'positive finite tail plus explicit geometric remainder'
    result['versions'] = {name: importlib.metadata.version(name)
                          for name in ('python-flint', 'numpy', 'scipy')}
    result['proof_status'] = ('Finite ball-arithmetic expression only. No continuum '
                              'enclosure, actual prime-sum estimate, or eventual conclusion.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
