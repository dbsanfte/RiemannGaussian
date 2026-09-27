#!/usr/bin/env python3
"""Audit all saved rows of an owner-coupled radial diagnostic, even if its
final precision gate failed. Never weaken that gate or overwrite the run.

Reconstruct the ORIGINAL finite quadrature weights and enclosures. This
checks row completeness, source provenance and finite-grid arithmetic only;
it does not enclose the continuous outer integral or transfer to primes.
Keep outside ordinary CI and exhaustive numerical-certificate verification.
"""
import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx
from probe_riesz_joined_balls import beta_rule
from riesz_radial_gamma import gamma_rule


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(path, compare=None):
    with path.open() as source:
        header = json.loads(next(source))
        rows = [json.loads(line) for line in source]
    args = header['arguments']
    assert not args['benchmark'], 'A benchmark checkpoint is not the coupled sum'
    assert 'probe_riesz_owner_coupled.py' in header['source_sha256'], 'Wrong radial-rule family'
    for name, expected in header['source_sha256'].items():
        assert digest(Path(__file__).with_name(name)) == expected, name
    nt, nr, n = args['tnodes'], args['rnodes'], args['order']
    expected = {(it, f, ir) for it in range(nt) for f in range(2) for ir in range(nr)}
    keys = {tuple(row['key']) for row in rows}
    assert len(rows) == len(keys) and keys == expected, 'Incomplete or duplicate rows'
    ctx.prec, ctx.threads = max(4096, args['bits']), 1
    ts, radial_audit = gamma_rule(n, arb(10001)/20000,
                                 arb(39)*n/20, arb(203)*n/100, nt)
    hs = [(n+99)//100-2, n//25-1]
    with ctx.workprec(args['bits']):
        rs = [beta_rule(h+1, n-h+1, nr) for h in hs]
    fronts, tails = [arb(0), arb(0)], [arb(0), arb(0)]
    uncertainties, evaluations = [], [0, 0]
    for row in rows:
        it, face, ir = row['key']
        weight = ts[it][1]*rs[face][ir][1]
        value = weight*arb(row['value'])
        assert weight > 0 and value.is_finite()
        fronts[face] += value
        tails[face] += abs(weight)*arb(row['count_tail'])
        evaluations[face] += row['response_evaluations']
        uncertainties.append(dict(key=row['key'], weighted_radius=float(value.rad()),
            weighted_value=str(value), radial_share=str(ts[it][0]/n),
            least_share=str(rs[face][ir][0]),
            norm_enclosed_points=row.get('norm_enclosed_points', 0),
            response_evaluations=row['response_evaluations']))
    uncertainties.sort(key=lambda row: row['weighted_radius'], reverse=True)
    joined = fronts[0]-fronts[1]
    assert joined.is_finite()
    passed = bool(joined.rad() < arb(args['max_radius']))
    comparison = None
    if compare is not None:
        old = json.loads(compare.read_text())
        assert not old['benchmark_only'] and old['N'] == n
        assert old['source_sha256'] == header['source_sha256']
        assert all(old[k] == args[k] for k in ('rnodes', 'pnodes', 'degree', 'bits',
                                               'subdivision', 'projection_bits', 'compression'))
        comparison = dict(input_sha256=digest(compare), tnodes=old['tnodes'],
            joined=old['joined'], finite_grid_balls_overlap=bool(joined.overlaps(arb(old['joined']))),
            interpretation='Agreement of two different finite quadrature grids is not an outer error bound.')
    return dict(
        scope='Audit of a complete owner-coupled checkpoint. No continuous quadrature, prime-sum or asymptotic bound.',
        arguments=args, complete_rows_verified=len(rows), frozen_sources_verified=True,
        checkpoint_sha256=digest(path), source_sha256=header['source_sha256'],
        audit_script_sha256=digest(Path(__file__)), radial_moment_checks=radial_audit['moment_checks'],
        fronts=[str(x) for x in fronts], joined=str(joined),
        omitted_model_count_allowance=[str(x) for x in tails],
        requested_radius=args['max_radius'], requested_radius_gate_passed=passed,
        status='requested finite-grid precision passed' if passed else 'requested finite-grid precision FAILED',
        response_evaluations=evaluations,
        largest_weighted_row_radii=uncertainties[:16],
        sum_weighted_row_radii_diagnostic=sum(x['weighted_radius'] for x in uncertainties),
        rows_over_1e_21=sum(x['weighted_radius'] > 1e-21 for x in uncertainties),
        comparison=comparison)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--checkpoint', type=Path, required=True)
    ap.add_argument('--compare-run', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert args.output != args.checkpoint and args.output != args.compare_run
    report = audit(args.checkpoint, args.compare_run)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    for key in ('status', 'complete_rows_verified', 'fronts', 'joined', 'response_evaluations'):
        print(key, report[key])


if __name__ == '__main__':
    main()
