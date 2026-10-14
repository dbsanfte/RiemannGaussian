"""Publish universal formal identity calibration with explicit remaining gaps."""
import argparse
import ast
import json
from pathlib import Path

import run_parametric_source_identities as R
import check_parametric_source_identities_run as C

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
RUN = BASE / 'parametric-source-identities-001'
PREVIOUS = BASE / 'publication-018'
OUT = BASE / 'publication-019'
SELF = 'publish_cancellation_parametric_source_identities.py'
TEST = 'test_publish_cancellation_parametric_source_identities.py'
NOTE = 'PARAMETRIC_SOURCE_IDENTITIES_HANDOFF.txt'
ANALYSES = ['parametric_identity_soundness_review_v1.txt', 'primitive_state_free_search_preconditioning_analysis_v1.txt']
FLAGS = dict(R.FLAGS)
read, sha, require = R.read, R.sha, R.require


def sources():
    pending = [SELF[:-3], TEST[:-3]]
    seen = set()
    while pending:
        name = pending.pop()
        path = ROOT / (name + '.py')
        if name in seen or not path.is_file():
            continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split('.')[0])
    return sorted(name + '.py' for name in seen)


def scoped(value):
    for key in FLAGS:
        require(value.get(key) is False, 'no stronger theorem promotion ' + key)


def validate_outcome(review, execution):
    scoped(review)
    scoped(execution)
    require(review.get('schema') == 'parametric-source-identities-independent-review-v1'
            and review.get('all_passed') is True, 'completed universal calibration audit')
    require(execution.get('schema') == 'parametric-source-identities-run-v1' and execution.get('completed') is True,
            'completed frozen calibration')
    require(type(review.get('recipe_count')) is int and review['recipe_count'] == 74,
            'complete supplied recipe set')
    require(review.get('formal_source_roots_independently_checked') is True
            and review.get('full_source_compiler_equivalence_formally_proved') is False
            and review.get('finite_sampling_used_as_universal_proof') is False,
            'universal symbolic roots with explicit unproved compiler bridge')
    rows = review.get('results')
    require(type(rows) is list and len(rows) == 74 and rows == execution.get('results'), 'same complete replayed outcomes')
    for index, row in enumerate(rows):
        require(type(row.get('index')) is int and row['index'] == index and row.get('producer_status') == 'proved'
                and row.get('FORMAL_EQ_verified') is True, 'each supplied formal identity independently verified')
    require(review.get('formal_identities_verified') == execution.get('formal_identities_verified') == 74,
            'formal count follows all supplied identities')
    require(execution.get('resources') == R.RESOURCES, 'same whole-experiment resource reservation')
    cost = execution.get('cost', {})
    require(type(cost.get('elapsed_seconds')) in (int, float) and 0 <= cost['elapsed_seconds'] <= 300
            and cost.get('address_space_limit_bytes') == 2*1024**3, 'completed bounded calibration process')


def load_inputs():
    catalogue = R.validate(RUN)
    receipt = read(RUN / 'receipt.json')
    actual = {str(p.relative_to(RUN)) for p in RUN.rglob('*') if p.is_file()
              and p.relative_to(RUN).parts[0] != 'frozen_source'
              and str(p.relative_to(RUN)) not in ('receipt.json', 'independent_verification.json')}
    require(actual == set(receipt['files_sha256']), 'complete terminal inventory')
    for name, value in receipt['files_sha256'].items():
        require(sha(RUN / name) == value, 'bound terminal evidence ' + name)
    review, execution = read(RUN / 'independent_verification.json'), read(RUN / 'execution.json')
    expected_names = {'source_seal.json', 'recipes.json', 'protocol.json', 'seal.json', 'tests.json', 'execution.json', 'receipt.json'}
    require(set(review.get('input_sha256', {})) == expected_names, 'complete filename-based independent review bindings')
    for name, value in review['input_sha256'].items():
        require(sha(RUN / name) == value, 'same independent review input ' + name)
    require(review.get('source_count') == receipt['source_count'] == len(R.sources()) and review.get('tests_passed') == 54,
            'complete frozen source and prescore test count')
    validate_outcome(review, execution)
    previous = read(PREVIOUS / 'manifest.json', 1048576)
    require(len(previous['files']) == 317, 'complete publication018 parent')
    for name, value in previous['files'].items():
        require(sha(ROOT / name) == value, 'immutable parent publication ' + name)
    return dict(catalogue=catalogue, review=review, execution=execution)


def report(inputs):
    review, execution = inputs['review'], inputs['execution']
    return dict(schema=19, previous_research_publication='publication-018',
                previous_manifest_sha256=sha(PREVIOUS / 'manifest.json'), previous_report_sha256=sha(PREVIOUS / 'report.json'),
                independent_review_sha256=sha(RUN / 'independent_verification.json'), terminal_receipt_sha256=sha(RUN / 'receipt.json'),
                source_count=review['source_count'], tests_passed=54, supplied_recipe_instances=74,
                formal_identities_verified=74, families=dict(divisor_cell_state=72, primitive_rowmass=2),
                mode='calibration of supplied reusable laws; not a new-operator discovery count',
                supported_rules='typed finite sums, exact local ring and Boolean algebra, complete partitions, capture-free sum rules',
                generic_rational_root_calibration=['1/3', '1/2', '2/3', '1/6'],
                ordinary_source_cut_parameters=['1/3', '1/2', '2/3'],
                formal_source_roots_independently_checked=True, full_source_compiler_equivalence_formally_proved=False,
                finite_samples_used_as_universal_proof=False, new_prime_distribution_estimate=False,
                producer_operations=sum(v['producer_operations'] for v in execution['results']),
                worker_checker_operations=sum(v['checker_operations'] for v in execution['results']),
                whole_audit_operations=review['audit_operations'], whole_audit_seconds=review['elapsed_seconds'],
                cost=execution['cost'], resources=R.RESOURCES,
                remaining_obligations=['complete symbolic adapter for the target and all contributing operators',
                                       'universal nonconstant identity for a fixed positive candidate',
                                       'separate arithmetic specialization and signed innovation bound',
                                       'ordinary-zeta recovery premises'],
                next_numerical_work='one preregistered positive cone-Jacobi scaling experiment from publication018; preserve original exact endpoint checks',
                next_proof_work='extend checked source identities toward full candidate cancellation; no finite-grid promotion',
                analyses=[dict(file=name, sha256=sha(ROOT / name)) for name in ANALYSES], handoff=NOTE, **FLAGS)


def publish():
    require(not OUT.exists(), 'exclusive publication019')
    inputs = load_inputs()
    latest = read(BASE / 'latest.json')
    require(latest.get('publication') == 'publication-018' and latest.get('manifest_sha256') == sha(PREVIOUS / 'manifest.json')
            and latest.get('report_sha256') == sha(PREVIOUS / 'report.json'), 'latest completed publication018')
    files = {ROOT / NOTE, PREVIOUS / 'manifest.json', PREVIOUS / 'report.json'}
    files.update(ROOT / name for name in ANALYSES + sources() + R.sources())
    files.update(p for p in RUN.rglob('*') if p.is_file())
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sorted(files)}
    OUT.mkdir()
    (OUT / 'frozen_source').mkdir()
    for name in (SELF, TEST, NOTE):
        p = OUT / ('frozen_source/' + name if name.endswith('.py') else name)
        p.write_bytes((ROOT / name).read_bytes())
        hashes[str(p.relative_to(ROOT))] = sha(p)
    R.write(OUT / 'report.json', report(inputs))
    hashes[str((OUT / 'report.json').relative_to(ROOT))] = sha(OUT / 'report.json')
    R.write(OUT / 'manifest.json', dict(schema=1, files=hashes, **FLAGS), 1048576)
    for name, value in hashes.items():
        require(sha(ROOT / name) == value, 'complete publication019 file binding')
    load_inputs()
    require(read(BASE / 'latest.json') == latest, 'no intervening publication')
    R.write(BASE / 'latest-019.tmp', dict(publication='publication-019', manifest_sha256=sha(OUT / 'manifest.json'),
                                       report_sha256=sha(OUT / 'report.json'), **FLAGS))
    (BASE / 'latest-019.tmp').replace(BASE / 'latest.json')
    return dict(publication='publication-019', bound_files=len(hashes), **FLAGS)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['validate', 'publish'])
    args = parser.parse_args()
    print(json.dumps(publish() if args.action == 'publish' else report(load_inputs()), sort_keys=True))
