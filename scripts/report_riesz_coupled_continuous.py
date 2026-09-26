#!/usr/bin/env python3
"""Preserve completed optional continuous-model runs and their frozen inputs.

This report does not supply an outer quadrature error bound or an arithmetic
estimate. It refuses benchmark-only/incomplete row checkpoints. Differences
between runs are diagnostics, never error estimates for the integral.
"""
import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_completed(path, root):
    result = json.loads(path.read_text())
    assert not result['benchmark_only'], 'A benchmark is not a completed coupled sum'
    for name, expected in result['source_sha256'].items():
        assert digest(root/'scripts'/name) == expected, (path, name)
    checkpoint = path.with_suffix('.rows.jsonl')
    with checkpoint.open() as stream:
        header = json.loads(next(stream))
        assert header['source_sha256'] == result['source_sha256']
        keys = set()
        for line in stream:
            row = json.loads(line)
            key = tuple(row['key'])
            assert key not in keys
            assert arb(row['value']).is_finite() and arb(row['count_tail']).is_finite()
            keys.add(key)
    wanted = {(it, f, ir) for it in range(result['tnodes']) for f in range(2)
              for ir in range(result['rnodes'])}
    assert keys == wanted, 'Incomplete row checkpoint'
    assert arb(result['joined']).is_finite()
    result['row_checkpoint_sha256'] = digest(checkpoint)
    result['completed_row_count'] = len(keys)
    result['run_report_sha256'] = digest(path)
    result['radial_rule'] = result['setup'].get('radial_rule', 'ordinary-legendre')
    allowance = sum(abs(arb(v)) for v in result['omitted_model_count_allowance'])
    result['joint_omitted_count_allowance'] = str(allowance)
    # No assertion is made that either ball contains the continuum integral.
    result['finite_quadrature_with_count_allowance'] = str(
        arb(result['joined'])+arb(0, allowance.upper()))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('runs', nargs='+', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    ctx.prec = 4096
    root = Path(__file__).resolve().parents[1]
    rows = [read_completed(path, root) for path in args.runs]
    comparisons = []
    for i, first in enumerate(rows):
        for j in range(i+1, len(rows)):
            second = rows[j]
            if first['N'] != second['N']:
                continue
            comparisons.append(dict(first=i, second=j,
                signed_difference=str(arb(second['joined'])-arb(first['joined'])),
                warning='Difference of finite quadrature expressions, not a continuum error bound.'))
    out = dict(scope='Completed numerical finite-mode refinements only. Response evaluation '
                     'and roundoff enclosed; outer quadrature and prime transport unresolved. '
                     'No asymptotic, retained signed prime-sum or zero-exclusion claim.',
               sources_verified=True, runs=rows, comparisons=comparisons,
               report_script_sha256=digest(Path(__file__)))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    for row in rows:
        print(row['radial_rule'], row['tnodes'], row['rnodes'], row['pnodes'], row['joined'])


if __name__ == '__main__':
    main()
