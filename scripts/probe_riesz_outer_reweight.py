#!/usr/bin/env python3
"""Optional sensitivity test on a completed coupled-model sample grid.

Reuse the expensive response values without changing any prime/model input.
Coarsened interpolatory weights match polynomial moments at midpoint
abscissae of the ORIGINAL FINITE quadrature measure. They are not a rigorous
quadrature-error bound. A q-point subset matches only q moments, whereas the
full Gaussian rule has independently checked moments through degree 2*q-1.
The full grid is independently reassembled and checked against its recorded
ball; all frozen source hashes and row indices are checked first.
"""
import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx
from probe_riesz_joined_balls import beta_rule
from riesz_radial_gamma import gamma_rule


def coarsen(rule, count):
    """Lagrange weights for a deterministic subset of a finite measure."""
    size = len(rule)
    assert 2 <= count <= size
    indices = [j*(size-1)//(count-1) for j in range(count)]
    assert len(set(indices)) == count
    if count == size:
        return dict(enumerate(w for _, w in rule)), dict(
            points=count, full_rule=True, moment_checks=0,
            total_variation=str(sum(abs(w) for _, w in rule)))
    center = (rule[0][0]+rule[-1][0])/2
    scale = (rule[-1][0]-rule[0][0])/2
    xs = [((x-center)/scale).mid() for x, _ in rule]
    ys = [xs[i] for i in indices]
    denominators = [arb(1) for _ in indices]
    for j in range(count):
        for k in range(count):
            if k != j:
                denominators[j] *= ys[j]-ys[k]
        assert not denominators[j].contains(0)
    weights = [rule[i][1] for i in indices]
    selected = set(indices)
    for i, (x, (_, weight)) in enumerate(zip(xs, rule)):
        if i in selected:
            continue
        product = arb(1)
        for y in ys:
            product *= x-y
        for j, y in enumerate(ys):
            weights[j] += weight*product/((x-y)*denominators[j])
    for k in range(count):
        observed = sum(w*y**k for w, y in zip(weights, ys))
        reference = sum(w*x**k for x, (_, w) in zip(xs, rule))
        assert observed.overlaps(reference), ('moment mismatch', count, k)
    return dict(zip(indices, weights)), dict(
        points=count, full_rule=False, moment_checks=count,
        total_variation=str(sum(abs(w) for w in weights)),
        negative_weights=sum(w < 0 for w in weights))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--tnodes', default='32,40,44,46,48')
    parser.add_argument('--rnodes', default='96,128,144,152,160')
    args = parser.parse_args()
    run = json.loads(args.run.read_text())
    assert not run['benchmark_only']
    for name, expected in run['source_sha256'].items():
        assert hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() == expected
    rows_path = args.run.with_suffix('.rows.jsonl')
    with rows_path.open() as source:
        header = json.loads(next(source))
        assert header['source_sha256'] == run['source_sha256']
        rows = [json.loads(line) for line in source]
    nt, nr, n = run['tnodes'], run['rnodes'], run['N']
    for argument, field in [('order', 'N'), ('tnodes', 'tnodes'),
                            ('rnodes', 'rnodes'), ('pnodes', 'pnodes'),
                            ('degree', 'degree'), ('bits', 'bits')]:
        assert header['arguments'][argument] == run[field]
    expected_keys = {(it, f, ir) for it in range(nt) for f in range(2) for ir in range(nr)}
    values = {tuple(row['key']): row['value'] for row in rows}
    assert len(rows) == len(values) and set(values) == expected_keys
    with ctx.workprec(max(4096, run['bits'])):
        ts, _ = gamma_rule(n, arb(10001)/20000, arb(39)*n/20, arb(203)*n/100, nt)
    hs = [(n+99)//100-2, n//25-1]
    with ctx.workprec(run['bits']):
        rs = [beta_rule(h+1, n-h+1, nr) for h in hs]
    ctx.prec = 4096
    values = {key: arb(value) for key, value in values.items()}
    tc = [int(x) for x in args.tnodes.split(',')]
    rc = [int(x) for x in args.rnodes.split(',')]
    assert nt in tc and nr in rc
    tw = {q: coarsen(ts, q) for q in tc}
    rw = [{q: coarsen(rule, q) for q in rc} for rule in rs]
    comparisons = []
    for tq in tc:
        for rq in rc:
            fronts = [sum(wt*wr*values[it, f, ir]
                          for it, wt in tw[tq][0].items()
                          for ir, wr in rw[f][rq][0].items()) for f in range(2)]
            joined = fronts[0]-fronts[1]
            assert joined.is_finite()
            if tq == nt and rq == nr:
                assert all(v.overlaps(arb(old)) for v, old in zip(fronts, run['fronts']))
                assert joined.overlaps(arb(run['joined']))
            row = dict(tnodes=tq, rnodes=rq,
                       fronts=[str(v) for v in fronts], joined=str(joined))
            comparisons.append(row)
            print(json.dumps(row), flush=True)
    report = dict(
        scope='Finite-grid interpolation sensitivity only. Full original sample grid '
              'reassembled independently. No continuous quadrature-error, prime-sum, '
              'asymptotic or zero-exclusion bound.',
        interpretation='Subset rules have only count-1 polynomial degree, not the '
                       '2*count-1 degree of genuine Gaussian rules. They may amplify '
                       'pointwise enclosures previously paid by tiny original weights. '
                       'Their disagreement is not evidence of a different continuous integral.',
        N=n, pnodes=run['pnodes'], frozen_sources_verified=True,
        complete_rows_verified=len(rows), original_run=run,
        input_sha256=hashlib.sha256(args.run.read_bytes()).hexdigest(),
        rows_sha256=hashlib.sha256(rows_path.read_bytes()).hexdigest(),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        radial_rules={q: tw[q][1] for q in tc},
        least_rules=[{q: f[q][1] for q in rc} for f in rw],
        comparisons=comparisons)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
