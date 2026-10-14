"""Outcome-conditioned resource retry; preserve the first probe unchanged."""
import json
import subprocess
import sys
from pathlib import Path
import run_cancellation_arithmetic as R
import run_cancellation_dual_probe as first
import exact_dual_support_reconstruction as D
import check_grouped_arithmetic as G


def run(parent):
    parent = Path(parent); R.validate_sources(parent); first.validate(parent)
    previous = parent/'dual-probe-001'
    failure = R.read(previous/'result.json')
    if failure['dual']['status'] != 'missing_resource' or failure['dual']['reason'] != 'certificate denominator limit':
        raise ValueError('declared retry trigger absent')
    out = parent/'dual-probe-002'
    out.mkdir(); (out/'frozen_source').mkdir()
    names = first.EXTRA + ['run_cancellation_dual_retry.py']
    hashes = {}
    for n in names:
        data = (R.ROOT/n).read_bytes(); (out/'frozen_source'/n).write_bytes(data); hashes[n] = R.sha(R.ROOT/n)
    limits = dict(first.LIMITS, max_denominator=2**4096)
    spec = dict(attempt_index=26, limits=limits,
        trigger='exact reconstruction reached denominator cap; only this resource limit raised to match coefficient-bit cap',
        previous_result_sha256=R.sha(previous/'result.json'), parent_training_sha256=R.sha(parent/'training.json'),
        parent_source_seal_sha256=R.sha(parent/'source_seal.json'), posthoc=True, original_failure_retained=True)
    R.write(out/'spec.json', spec); R.write(out/'source_seal.json', dict(hashes=hashes))
    seals = dict(spec_sha256=R.sha(out/'spec.json'), source_seal_sha256=R.sha(out/'source_seal.json'))
    R.write(out/'seal.json', seals)
    def validate():
        R.validate_sources(parent); first.validate(parent)
        if R.sha(previous/'result.json') != spec['previous_result_sha256'] or R.sha(parent/'training.json') != spec['parent_training_sha256']:
            raise ValueError('retry inputs changed')
        if R.read(out/'seal.json') != seals or R.sha(out/'spec.json') != seals['spec_sha256'] or R.sha(out/'source_seal.json') != seals['source_seal_sha256']:
            raise ValueError('retry seal changed')
        for n,h in hashes.items():
            if R.sha(R.ROOT/n) != h or R.sha(out/'frozen_source'/n) != h: raise ValueError('retry source changed')
    validate()
    attempt = R.read(parent/'training.json')['attempts'][26]; program = attempt['program']
    scales = R.read(parent/'protocol.json')['training_scales']
    instances = [R.build(program, X)['instance'] for X in scales]+R.constraints(program)
    if list(map(R.digest, instances)) != attempt['case_hashes']+attempt['auxiliary_hashes']:
        raise ValueError('retry case mismatch')
    result = D.reconstruct_joint_separator(instances, allow_constant_slack=True, **limits)
    check = G.verify_joint_dual(instances, result, allow_constant_slack=True) if result.get('certified') else None
    R.write(out/'result.json', dict(dual=result, independent_finite_check=check,
        instance_hashes=list(map(R.digest, instances)), original_status=attempt['synthesis']['status'],
        scope='resource retry of declared finite cone; no all-scale estimate', global_bound_proved=False, RH_proved=False))
    validate()
    R.write(out/'producer_receipt.json', dict(result_sha256=R.sha(out/'result.json'),
        spec_sha256=R.sha(out/'spec.json'), original_failure_unchanged=True,
        test_provenance='unchanged exact utility passed four tests in sealed probe-001; no utility edits',
        global_bound_proved=False, RH_proved=False))
    print(json.dumps(dict(status=result['status'], certified=result.get('certified'), reason=result.get('reason'),
        lhs_dot_y=result.get('lhs_dot_y'), support_size=len(result.get('diagnostics', {}).get('support', [])))))


if __name__ == '__main__': run(sys.argv[1])
