"""Publish already audited full14 results without re-running their optimizers."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
FLAGS = dict(global_bound_proved=False, RH_proved=False)
NOTES = ['COMPLETE_GRAM_SEARCH_HANDOFF.txt', 'complete_gram_scope.txt',
         'complete_gram_direction_retry_note.txt', 'complete_gram_next_strategy.txt']


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def write(path, value):
    with path.open('x') as handle:
        json.dump(value, handle, sort_keys=True, indent=2, allow_nan=False)
        handle.write('\n')


def bound(base, hashes):
    for name, expected in hashes.items():
        require(sha(base / name) == expected, 'artifact binding: ' + str(base / name))


def prior_manifests():
    records = {}
    for name, count in [('publication-006', 319), ('publication-005', 263),
                        ('publication-004', 343), ('publication-003', 259)]:
        path = BASE / name / 'manifest.json'
        files = read(path)['files']
        require(len(files) == count, 'prior publication count')
        bound(ROOT, files)
        records[name] = dict(manifest_sha256=sha(path), bound_files=count)
    path = ROOT / 'detector-performance-results/publication-001/manifest.json'
    files = read(path)['files']
    require(len(files) == 244, 'resource manifest count')
    bound(ROOT, files)
    records['resource-publication-001'] = dict(manifest_sha256=sha(path), bound_files=244)
    return records


def audited_stage(name, runner, tests_expected, sources_expected, *, storage=False):
    d = BASE / name
    review_name = 'verification.json' if storage else 'independent_verification.json'
    review = read(d / review_name)
    require(review.get('all_passed') is True, 'admitted archive: ' + name)
    require(all(review.get(k) is False for k in FLAGS), 'finite audit scope')
    bound(d, review['input_sha256'])
    require(read(d / 'seal.json') == {
        key + '_sha256': sha(d / (key + '.json'))
        for key in ['protocol', 'source_seal', 'input']}, 'protocol/input/source seal')
    inputs = read(d / 'input.json')
    if storage:
        bound(BASE / 'complete-gram-search-001', inputs)
    else:
        bound(ROOT, inputs['input_sha256'])
        require(set(inputs['input_sha256']) == set(runner.INPUTS), 'all preregistered inputs')
    source = read(d / 'source_seal.json')
    source_names = runner.source_names() if storage else runner.sources()
    require(set(source) == set(source_names) and len(source) == sources_expected,
            'complete frozen source closure')
    bound(ROOT, source)
    bound(d / 'frozen_source', source)
    receipt = read(d / 'receipt.json')
    terminal = receipt if storage else receipt['files_sha256']
    actual = {str(p.relative_to(d)): sha(p) for p in d.rglob('*.json')
              if p.name not in ['receipt.json', review_name]}
    require(terminal == actual, 'complete terminal artifact set')
    bound(d, terminal)
    if not storage:
        require(receipt['source_count'] == sources_expected, 'terminal source count')
    tests = read(d / 'tests.json')
    match = re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$', tests['stdout'] + tests['stderr'])
    require(tests['returncode'] == 0 and match is not None
            and int(match.group(1)) == tests_expected, 'frozen calibration admission')
    protocol = read(d / 'protocol.json')
    require(all(protocol.get(k) is False for k in FLAGS), 'finite protocol scope')
    if storage:
        require(protocol['spec'] == runner.SPEC and protocol['no_new_float_search'] is True,
                'fixed entire anchored state family')
    else:
        require(protocol['language'] == runner.P.SPEC
                and protocol['gram_specs'] == runner.P.gram_specs()
                and protocol['gram_groups'] == runner.P.group_descriptors(), 'complete full14 grammar')
        require(protocol['parallel'] == runner.PARALLEL and protocol['tests'] == runner.TESTS,
                'frozen resources and calibrations')
        require(protocol['parallel']['workers'] == 1
                and protocol['parallel']['worker_memory_bytes'] == 6*1024**3
                and protocol['parallel']['memory_budget_bytes'] == 6*1024**3, '6GiB worker and total')
    return dict(directory=d, source=source, review=review, protocol=protocol,
                tests_passed=tests_expected, review_name=review_name)


def load_inputs():
    import run_complete_gram_moment_probe as P1
    import run_complete_gram_moment_probe_v2 as P2
    import run_complete_gram_search as S
    import complete_gram_storage_diagnostic as K
    priors = prior_manifests()
    stages = [audited_stage('complete-gram-moment-probe-001', P1, 12, 68),
              audited_stage('complete-gram-moment-probe-002', P2, 15, 68),
              audited_stage('complete-gram-search-001', S, 44, 79),
              audited_stage('complete-gram-storage-probe-001', K, 3, 42, storage=True)]
    first, second, search, storage = stages
    failed = read(first['directory'] / 'result.json')
    require(failed['status'] == 'missing_resource'
            and failed['reason'] == 'coefficient_bits resource limit'
            and first['review']['independent_full_moment_replay_passed'] is False,
            'original failed diagnostic preserved')
    probe = read(second['directory'] / 'result.json')
    require(probe['status'] == 'complete'
            and second['review']['independent_full_moment_replay_passed'] is True
            and second['review']['missing_coordinate_occurrences'] == 0,
            'complete exact moment diagnostic')
    require(second['review']['region_statuses'] == {
        name: 'witness_invalid_for_complete_cone' for name in ['full_child', 'full_parent']},
        'both prior regional witnesses invalidated')
    protocol = search['protocol']
    require(protocol['program'] == S.PROGRAM and protocol['limits'] == S.LIMITS
            and protocol['solver_limits'] == S.SOLVER_LIMITS and protocol['dual_limits'] == S.DUAL_LIMITS
            and protocol['dictionary'] == S.P.C.descriptors(), 'fixed signed search and resources')
    require(protocol['training_scales'] == [1,2,3,5] and protocol['final_scales'] == [8,13]
            and protocol['final_refit'] is False and protocol['no_actual_signed_response_inputs'] is True,
            'source selection and finite transfer scope')
    result = read(search['directory'] / 'jobs/dual-000.json')
    dual = result['synthesis']
    require(result['status'] == 'exact_separator' and result['independent_check']['verified'] is True
            and dual['certified'] is True and dual['independent_full_Gram_check_passed'] is True,
            'independently admitted full-cone separator')
    require(len(dual['saved_support']) == 701 and dual['constant_coordinates'] == ['0']*5
            and dual['lhs_dot_y'] == '-1', 'exact separator and scalar budget scope')
    compression = dual['diagnostics']['row_compression']
    require(compression['original_rows'] == 1366 and compression['reduced_rows'] == 877
            and compression['original_work_proxy'] == 671253766
            and compression['native_work_proxy'] == 430958677
            and compression['total_work_proxy'] == 446048494 <= S.DUAL_LIMITS['max_work'] == 450000000,
            'charged compressed work within unchanged cap')
    expected_decision = dict(dual_status='exact_separator', run_primal=False, final_scales=[])
    require(read(search['directory'] / 'decision.json') == expected_decision
            and search['review']['decision'] == expected_decision, 'exact dual pruning')
    require(search['review']['checkpoint_checks'] == ['jobs/dual-000-proposal.json'],
            'independently bound full checkpoint')
    require([p.name for p in (search['directory'] / 'jobs').glob('*.json')
             if not p.name.endswith('-proposal.json')] == ['dual-000.json'], 'no claimed primal or transfer')
    diagnostic = read(storage['directory'] / 'result.json')
    require(diagnostic == K.compute(dual), 'exact anchored moment replay')
    require(diagnostic['status'] == 'witness_invalid_for_anchored_storage_cone'
            and diagnostic['direction'] == ['0','1']+['0']*12
            and diagnostic['increment_formal_constant_per_X'] == '0'
            and diagnostic['larger_cone_feasibility_proved'] is False
            and diagnostic['uniform_innovation_bound_proved'] is False, 'limited storage conclusion')
    return dict(priors=priors, stages=stages, failed=failed, probe=probe,
                result=result, dual=dual, compression=compression, diagnostic=diagnostic)


def report(inputs):
    archives = []
    for stage in inputs['stages']:
        d = stage['directory']
        archives.append(dict(name=d.name, source_count=len(stage['source']),
                             tests_passed=stage['tests_passed'],
                             verification_kind=stage['review_name'],
                             verification_sha256=sha(d / stage['review_name'])))
    c = inputs['compression']
    return dict(schema=7, previous_research_publication='publication-006',
                prior_manifests=inputs['priors'], archives=archives,
                gram_group_dimensions=dict(full_child=14, full_parent=14),
                original_scalar_sources_and_targets_preserved=True,
                prior_four_group_cone_embedded=True,
                original_coefficient_bit_resource_failure_preserved=True,
                bounded_direction_retry=dict(prior_witness_invalid_in_both_regions=True,
                                            missing_coordinates=0, new_floating_search=False),
                full14_search=dict(status=inputs['result']['status'], support_size=701,
                                   result_sha256=sha(inputs['stages'][2]['directory'] / 'jobs/dual-000.json'),
                                   selected_rows=c['original_rows'], compressed_rows=c['reduced_rows'],
                                   raw_native_work_proxy=c['original_work_proxy'],
                                   native_work_proxy=c['native_work_proxy'],
                                   total_charged_work_proxy=c['total_work_proxy'], work_limit=450000000,
                                   constant_coordinates=['0']*5, target_pairing='-1',
                                   all_original_equations_independently_checked=True,
                                   cost=inputs['result']['cost'], primal_attempted=False,
                                   final_transfers_attempted=False,
                                   scope='exact fixed shared full14 gamma-zero certificate cone; arbitrary scalar budget shifts'),
                anchored_storage_diagnostic=dict(status=inputs['diagnostic']['status'],
                    result_sha256=sha(inputs['stages'][3]['directory'] / 'result.json'),
                    negative_direction='half=P_floor(t/2)', matrix='H_child-4 H_parent',
                    entire_anchored_PSD_family_preregistered=True, new_prime_sign_information=False,
                    half_energy_is_twice_previous_dyadic_energy=True,
                    half_energy_identity_domain='dyadic X>=2; half energy at X=1 is zero',
                    verification='same-implementation exact replay; not independent uniform-bound admission',
                    primal_feasibility_proved=False, uniform_innovation_bound_proved=False),
                next_action='implement typed signed storage increment with independent coercivity, scalar-growth and recovery checks before searching the entire anchored PSD state family',
                future_resources=dict(worker_memory_bytes=6*1024**3, total_memory_bytes=6*1024**3,
                                      total_charged_work_limit=450000000),
                collaboration_policy='Sol 6.1 subagents only for substantial long-running parallelizable work; small tasks in main thread',
                critical_finite_certificate_found=False, all_scale_bound_found=False, **FLAGS)


def publish():
    inputs = load_inputs()
    out = BASE / 'publication-007'
    require(not out.exists(), 'exclusive publication007')
    previous = read(BASE / 'latest.json')
    require(previous['publication'] == 'publication-006'
            and previous['manifest_sha256'] == sha(BASE / 'publication-006/manifest.json')
            and previous['report_sha256'] == sha(BASE / 'publication-006/report.json'), 'current pointer binding')
    files = {ROOT / n for n in NOTES + ['publish_cancellation_complete_gram.py']}
    for stage in inputs['stages']:
        files.update(p for p in stage['directory'].rglob('*')
                     if p.is_file() and '__pycache__' not in p.parts)
        files.update(ROOT / n for n in stage['source'])
    files.update(BASE / 'publication-006' / n for n in ['manifest.json', 'report.json'])
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sorted(files)}
    out.mkdir()
    (out / 'frozen_source').mkdir()
    for n in NOTES + ['publish_cancellation_complete_gram.py']:
        p = out / ('frozen_source/' + n if n.endswith('.py') else n)
        p.write_bytes((ROOT / n).read_bytes())
        hashes[str(p.relative_to(ROOT))] = sha(p)
    write(out / 'report.json', report(inputs))
    hashes[str((out / 'report.json').relative_to(ROOT))] = sha(out / 'report.json')
    write(out / 'manifest.json', dict(schema=1, files=hashes, **FLAGS))
    bound(ROOT, read(out / 'manifest.json')['files'])
    load_inputs()
    bound(ROOT, read(out / 'manifest.json')['files'])
    require(read(BASE / 'latest.json') == previous, 'no intervening publication')
    pointer = dict(publication='publication-007', manifest_sha256=sha(out / 'manifest.json'),
                   report_sha256=sha(out / 'report.json'), **FLAGS)
    write(BASE / 'latest-007.tmp', pointer)
    (BASE / 'latest-007.tmp').replace(BASE / 'latest.json')
    return dict(publication='publication-007', bound_files=len(hashes), **FLAGS)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['validate', 'publish'])
    args = parser.parse_args()
    if args.action == 'publish':
        print(json.dumps(publish()))
    else:
        print(json.dumps(dict(all_passed=True, publication_written=False, report=report(load_inputs()))))
