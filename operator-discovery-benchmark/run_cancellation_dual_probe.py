"""Sealed outcome-conditioned Farkas reconstruction for one archived failure."""
import argparse
import json
import subprocess
import sys
from pathlib import Path
import run_cancellation_arithmetic as R
import exact_dual_support_reconstruction as D
import check_grouped_arithmetic as G

EXTRA = ['run_cancellation_dual_probe.py', 'exact_dual_support_reconstruction.py',
         'test_exact_dual_support_reconstruction.py']
LIMITS = dict(time_limit=60, max_rows=1200, max_variables=40000, max_work=30000000,
              max_denominator=1000000000000, max_coefficient_bits=4096,
              max_columns=1024, max_monomials=30000, max_operations=200000000,
              max_horizon=4096, max_degree=12)


def freeze(parent):
    parent = Path(parent); R.validate_sources(parent)
    out = parent/'dual-probe-001'
    if out.exists(): raise FileExistsError('new probe required')
    training = R.read(parent/'training.json')
    attempt = training['attempts'][26]
    if attempt['synthesis']['status'] != 'no_certificate_found' or attempt['program']['constraint'] != 'zero_cubic':
        raise ValueError('declared posthoc failed-case selection')
    out.mkdir(); (out/'frozen_source').mkdir()
    hashes = {}
    for name in EXTRA:
        data = (R.ROOT/name).read_bytes(); (out/'frozen_source'/name).write_bytes(data)
        hashes[name] = R.sha(R.ROOT/name)
    spec = dict(attempt_index=26, program=attempt['program'], limits=LIMITS,
                selection='posthoc: largest declared q and C in failed zero-cubic extension family; no fresh discovery evaluation',
                parent_training_sha256=R.sha(parent/'training.json'),
                parent_source_seal_sha256=R.sha(parent/'source_seal.json'),
                original_status_retained=True, global_bound_proved=False, RH_proved=False)
    R.write(out/'spec.json', spec)
    R.write(out/'source_seal.json', dict(hashes=hashes))
    R.write(out/'seal.json', dict(spec_sha256=R.sha(out/'spec.json'), source_seal_sha256=R.sha(out/'source_seal.json')))


def validate(parent):
    parent = Path(parent); R.validate_sources(parent); out = parent/'dual-probe-001'
    if R.read(out/'seal.json') != dict(spec_sha256=R.sha(out/'spec.json'), source_seal_sha256=R.sha(out/'source_seal.json')):
        raise ValueError('probe seal changed')
    hashes = R.read(out/'source_seal.json')['hashes']
    if set(hashes) != set(EXTRA): raise ValueError('probe source coverage')
    for n, h in hashes.items():
        if R.sha(R.ROOT/n) != h or R.sha(out/'frozen_source'/n) != h: raise ValueError('probe source changed')
    spec = R.read(out/'spec.json')
    if spec['parent_training_sha256'] != R.sha(parent/'training.json') or spec['parent_source_seal_sha256'] != R.sha(parent/'source_seal.json'):
        raise ValueError('parent inputs changed')
    return spec


def run(parent):
    parent = Path(parent); out = parent/'dual-probe-001'; spec = validate(parent)
    if (out/'tests.json').exists(): raise FileExistsError('probe already started')
    test = subprocess.run([sys.executable, '-B', '-m', 'unittest', 'test_exact_dual_support_reconstruction'],
                           cwd=R.ROOT, capture_output=True, text=True, timeout=30)
    R.write(out/'tests.json', dict(returncode=test.returncode, stdout=test.stdout, stderr=test.stderr))
    if test.returncode: raise ValueError('probe tests failed')
    attempt = R.read(parent/'training.json')['attempts'][spec['attempt_index']]
    protocol = R.read(parent/'protocol.json'); program = attempt['program']
    ordinary = [R.build(program, X)['instance'] for X in protocol['training_scales']]
    auxiliary = R.constraints(program)
    if list(map(R.digest, ordinary)) != attempt['case_hashes'] or list(map(R.digest, auxiliary)) != attempt['auxiliary_hashes']:
        raise ValueError('probe instance mismatch')
    instances = ordinary + auxiliary
    result = D.reconstruct_joint_separator(instances, allow_constant_slack=program['allow_constant_slack'], **spec['limits'])
    check = G.verify_joint_dual(instances, result, allow_constant_slack=program['allow_constant_slack']) if result.get('certified') else None
    R.write(out/'result.json', dict(dual=result, independent_finite_check=check,
        instance_hashes=list(map(R.digest, instances)), original_status=attempt['synthesis']['status'],
        scope='posthoc finite declared-cone obstruction only', global_bound_proved=False, RH_proved=False))
    validate(parent)
    R.write(out/'producer_receipt.json', dict(result_sha256=R.sha(out/'result.json'), tests_sha256=R.sha(out/'tests.json'),
        spec_sha256=R.sha(out/'spec.json'), original_training_unchanged=True, global_bound_proved=False, RH_proved=False))
    print(json.dumps(dict(status=result['status'], certified=result.get('certified'), reason=result.get('reason'),
                          lhs_dot_y=result.get('lhs_dot_y'), support_size=len(result.get('diagnostics', {}).get('support', [])))))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('command', choices=('freeze', 'run')); parser.add_argument('parent')
    args = parser.parse_args(); (freeze if args.command == 'freeze' else run)(args.parent)
