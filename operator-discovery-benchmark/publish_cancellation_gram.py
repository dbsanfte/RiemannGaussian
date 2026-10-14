"""Bind independently reviewed Gram results and supplied factor calibration."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def read(p):
    return json.loads(p.read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def write(p, value):
    with p.open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True, allow_nan=False)
        f.write('\n')


def publish():
    base = ROOT/'cancellation-arithmetic-results'
    old = base/'publication-001'
    gram = base/'pilot-001/gram-probe-001'
    factor = base/'factor-calibration-001'
    out = base/'publication-002'
    if out.exists():
        raise FileExistsError('new publication required')
    old_manifest = read(old/'manifest.json')
    for n, h in old_manifest['files'].items():
        if sha(ROOT/n) != h:
            raise ValueError('prior publication changed: '+n)
    check = read(gram/'independent_verification.json')
    uniform = read(gram/'uniform_scope_independent_review.json')
    calibration = read(factor/'verification.json')
    root_calibration = read(factor/'root_verification.json')
    if not all(v['all_passed'] for v in [check, calibration, root_calibration]):
        raise ValueError('verified artifacts required')
    if (uniform['unsigned_reduction_verified'] is not True or uniform['lhs_dot_y'] != '-1'
            or uniform['constant_dual_coordinates'] != ['0']*5
            or uniform['adjudication_sha256'] != sha(ROOT/'cancellation_gram_adjudication.json')
            or root_calibration['verification_sha256'] != sha(factor/'verification.json')):
        raise ValueError('mathematical review binding')
    for name, h in uniform['input_sha256'].items():
        if sha(gram/(name+'.json')) != h:
            raise ValueError('uniform scope audit binding')
    for name, h in check['input_sha256'].items():
        if sha(gram/(name+'.json')) != h:
            raise ValueError('Gram audit binding')
    for name, h in calibration['input_sha256'].items():
        if sha(factor/name) != h:
            raise ValueError('factor audit binding')
    for directory in [gram, factor]:
        for n, h in read(directory/'source_seal.json')['hashes'].items():
            if sha(ROOT/n) != h or sha(directory/'frozen_source'/n) != h:
                raise ValueError('source changed: '+n)
    out.mkdir()
    report = dict(schema=2, previous_publication='publication-001',
        prior_manifest_sha256=sha(old/'manifest.json'),
        gram=dict(training_statuses=check['training_statuses'], final_statuses=check['final_statuses'],
            dual_status=check['dual_status'], independent_audit=True, tests=21,
            obstruction='entire fixed shared full-PSD cone under gamma=0; all rational C>=0, integer q>=1',
            obstruction_is_arithmetic_refutation=False,
            unsigned_certificate='exact all-scale alias of supplied Cauchy certificate, gamma=56/3; no offdiagonal gain',
            missing_final_scale=13),
        factor=dict(supplied_calibration=True, tests=10, fixtures=6,
            shared_group_adapter=True, bound_search_performed=False,
            capabilities=['complete ordered factor partitions', 'exact rational-power cutoffs',
                          'signed rational kernels', 'coprime relation multipliers',
                          'full complements and product multiplicities']),
        next_action='new frozen factor/relation program search, then analytic proof attempts with complete residuals',
        global_bound_proved=False, RH_proved=False)
    write(out/'report.json', report)
    own = ['CANCELLATION_GRAM_HANDOFF.txt', 'publish_cancellation_gram.py',
           'cancellation_gram_adjudication.json', 'cancellation_gram_adjudication.txt',
           'cancellation_full_gram_uniform_independent_review.txt',
           'cancellation_relational_extension_research.txt', 'cancellation_factor_calibration_handoff.txt']
    files = {ROOT/n for n in own}
    files.update([old/'manifest.json', old/'report.json', out/'report.json'])
    for directory in [gram, factor]:
        files.update(p for p in directory.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
        files.update(ROOT/n for n in read(directory/'source_seal.json')['hashes'])
    manifest = dict(schema=1, files={str(p.relative_to(ROOT)):sha(p) for p in sorted(files)},
                    global_bound_proved=False, RH_proved=False)
    write(out/'manifest.json', manifest)
    for n, h in manifest['files'].items():
        if sha(ROOT/n) != h:
            raise ValueError('publication end hash changed')
    pointer = dict(publication='publication-002', report_sha256=sha(out/'report.json'),
                   manifest_sha256=sha(out/'manifest.json'), global_bound_proved=False, RH_proved=False)
    temp = base/'latest-002.tmp'
    write(temp, pointer)
    temp.replace(base/'latest.json')
    print(json.dumps(dict(publication=str(out.relative_to(ROOT)), bound_files=len(manifest['files']),
                          global_bound_proved=False, RH_proved=False)))


if __name__ == '__main__':
    publish()
