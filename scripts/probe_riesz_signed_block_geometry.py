#!/usr/bin/env python3
"""Optional global signed-null detector on complete supplied unpaid blocks.

Input records contain id, unpaidScope.eligible, baseline, nullColumns and
optionally bound/original. Paid records are skipped before optimization.
No incomplete subset/sample price is accepted as a native block price.
Default execution runs independent unit regressions only.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
from riesz_signed_block_geometry import self_test, solve


def export(value):
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, dict):
        return {key: export(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return list(map(export, value))
    return value


def scan(record):
    result = dict(id=record['id'], original=record.get('original'),
                  nativePopulationOrFloorCertified=False)
    if not record.get('unpaidScope', {}).get('eligible', False):
        return dict(**result, status='skipped_paid_or_unverified_before_optimization')
    if not record.get('allOriginalGroupsRetained', False):
        return dict(**result, status='incomplete_price_not_optimized')
    try:
        fit = solve(record['baseline'], record['nullColumns'], record.get('bound', 4))
    except (ValueError, RuntimeError) as exc:
        return dict(**result, status='unresolved', reason=str(exc))
    return dict(**result, status='exact_finite_input_replay', certificate=export(fit),
                actualPrimeWeightsValidatedByThisScript=False)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--inputs-json', type=Path)
    p.add_argument('--skip-self-test', action='store_true')
    p.add_argument('--output', type=Path,
                   default=Path('.lake/riesz-signed-null-gain/detector.json'))
    args = p.parse_args()
    unit = None if args.skip_self_test else self_test()
    if unit is not None:
        assert scan(dict(id='paid', unpaidScope=dict(eligible=False)))['status'].startswith('skipped')
        assert scan(dict(id='incomplete', unpaidScope=dict(eligible=True)))['status'] == 'incomplete_price_not_optimized'
        invalid = dict(id='nonnull', unpaidScope=dict(eligible=True),
                       allOriginalGroupsRetained=True, baseline=[-2, 1], nullColumns=[[1], [0]])
        assert scan(invalid)['status'] == 'unresolved'
        unit['paidIncompleteAndNonnullGuards'] = 3
    report = dict(schemaVersion=1,
                  head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                  selfTest=unit,
                  rows=[scan(record) for record in json.loads(args.inputs_json.read_text())]
                       if args.inputs_json else [],
                  scope=dict(optionalOutsideBuildsCI=True,
                             nativeFloorCertified=False,
                             unpaidGateBeforeOptimization=True,
                             exactRationalReplay=True,
                             independentUnitRegressionsAreNotUnpaidPopulationScans=True))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    report['sources'] = {}
    for path in (Path(__file__), Path('scripts/riesz_signed_block_geometry.py')):
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        snapshot = args.output.parent/f'source-{digest}.py'
        snapshot.write_bytes(data)
        report['sources'][str(path)] = dict(sha256=digest, snapshot=str(snapshot))
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(json.dumps(dict(selfTest=report['selfTest'], suppliedRecords=len(report['rows'])), indent=2))


if __name__ == '__main__':
    main()
