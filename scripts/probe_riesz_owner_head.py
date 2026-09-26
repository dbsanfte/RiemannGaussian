#!/usr/bin/env python3
"""Optional audit of the joined cutoff-independent one-cofactor head.

Its exact beta/conditional-binomial marginal is the same on both faces:
integrating the least share produces Bin(N+1,p) on the same owner band.
The joined head integral is consequently ZERO, with the physical owner
mask and radial window retained. A nonzero finite quadrature difference
measures head aliasing only, not the rest of the response or a prime sum.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
import multiprocessing
from pathlib import Path
import time

from flint import arb, ctx
import probe_riesz_owner_coupled as owner
import probe_riesz_joined_continuous_balls as coupled


def display(value):
    with ctx.workprec(192):
        return str(value+0)


def radial_row(it):
    T, wt = coupled.TS[it]
    lam = coupled.LENGTH/T
    assert arb(3)/5 < lam < 1
    envelope = 49*(T/40000).exp()
    totals, skipped = [arb(0), arb(0)], [arb(0), arb(0)]
    omega = 3*T/500
    exponential = (T/40000).exp()
    for face in range(2):
        for ir, (r, wr) in enumerate(coupled.RS[face]):
            for p, pw in owner.OWNER_ROWS[face][ir]:
                weight = wt*wr*pw
                bound = (weight*envelope).upper()
                if bound < NODE_BUDGET:
                    skipped[face] += bound
                    continue
                e = (T*p/40000).exp()
                first = 1+6*e*(omega*p).cos()
                second = 1+6*(exponential/e)*(omega*(1-p)).cos()
                totals[face] += weight*first*second*(lam-p)/(lam*(1-p))
    return dict(radial_index=it,
                fronts=[str(v+arb(0, e.upper())) for v, e in zip(totals, skipped)],
                skipped_budget=[display(e) for e in skipped])


def main():
    global NODE_BUDGET
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=262144)
    parser.add_argument('--tnodes', type=int, default=48)
    parser.add_argument('--rnodes', type=int, default=160)
    parser.add_argument('--pnodes', type=int, default=256)
    parser.add_argument('--bits', type=int, default=768)
    parser.add_argument('--workers', type=int, default=2)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.order < 10000 or min(args.tnodes, args.rnodes, args.pnodes, args.workers) < 1:
        parser.error('Invalid order, node counts or workers')
    start = time.monotonic()
    source_hashes = lambda: dict(owner.sources(), **{Path(__file__).name:
                                      hashlib.sha256(Path(__file__).read_bytes()).hexdigest()})
    frozen = source_hashes()
    owner.prepare(args.order, args.tnodes, args.rnodes, args.pnodes,
                  4, 192, args.bits, '1e-40')
    NODE_BUDGET = arb('1e-40')/(2*args.tnodes*args.rnodes*args.pnodes)
    totals, rows = [arb(0), arb(0)], []
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.with_suffix('.rows.jsonl').open('w') as log, ProcessPoolExecutor(
            max_workers=args.workers, mp_context=multiprocessing.get_context('fork')) as pool:
        log.write(json.dumps(dict(source_sha256=frozen, arguments={k: str(v) if isinstance(v, Path)
                                                                   else v for k, v in vars(args).items()}))+'\n')
        for row in pool.map(radial_row, range(args.tnodes)):
            rows.append(row)
            for face in range(2):
                totals[face] += arb(row['fronts'][face])
            log.write(json.dumps(row)+'\n')
            log.flush()
            print('radial', len(rows), args.tnodes, 'seconds', time.monotonic()-start, flush=True)
    assert source_hashes() == frozen, 'Source changed during audit'
    out = dict(N=args.order, tnodes=args.tnodes, rnodes=args.rnodes, pnodes=args.pnodes,
               finite_head_fronts=[display(v) for v in totals],
               joined_head_alias=display(totals[0]-totals[1]), exact_joined_head=0,
               source_sha256=frozen, seconds=time.monotonic()-start,
               scope='Finite-quadrature error of the cutoff-independent model head only. '
                     'The remaining coupled response and arithmetic prime-sum error are unestimated.')
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out), flush=True)


if __name__ == '__main__':
    main()
