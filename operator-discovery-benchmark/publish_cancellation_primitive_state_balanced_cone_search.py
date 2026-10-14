"""Publish a checked balanced three-block search without theorem promotion."""
import argparse
import ast
from fractions import Fraction
import json
from pathlib import Path
import re

import check_primitive_state_balanced_cone_search_run as CHECK

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
RUN = BASE / 'primitive-state-balanced-cone-search-001'
PREVIOUS = BASE / 'publication-020'
SEED_PUBLICATION = BASE / 'publication-018'
OUT = BASE / 'publication-021'
SELF = 'publish_cancellation_primitive_state_balanced_cone_search.py'
TEST = 'test_publish_cancellation_primitive_state_balanced_cone_search.py'
NOTE = 'PRIMITIVE_STATE_BALANCED_CONE_SEARCH_HANDOFF.txt'
ANALYSES = ['primitive_state_balanced_cone_analysis_v1.txt',
            'primitive_state_uniform_identity_probe_design_v1.txt']
FLAGS = dict(CHECK.FLAGS)
read, sha, require = CHECK.read, CHECK.sha, CHECK.require


def write(path, value):
    data = json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()
    require(len(data) <= 1048576, 'bounded publication metadata')
    with Path(path).open('xb') as handle:
        handle.write(data)


def bind(root, hashes):
    for name, value in hashes.items():
        path = CHECK.path_under(root, name)
        require(sha(path) == value, 'immutable evidence binding ' + name)


def publisher_sources():
    pending, seen = [SELF[:-3], TEST[:-3]], set()
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


def scope(value):
    require(type(value) is dict, 'explicit publication evidence')
    for key in FLAGS:
        require(value.get(key) is False, 'no theorem promotion ' + key)


def validate_outcome(review, execution, record, proposal, endpoint, check):
    scope(review)
    require(review.get('schema') == 'primitive-state-balanced-cone-search-independent-review-v1'
            and review.get('all_passed') is True, 'completed independent balanced cone audit')
    fixed = dict(original_finite_equations=5641, original_variables=1957, rank=779,
                 free_coordinates=445, parent_source_rebuilds=0, full_elimination_replayed=False,
                 uniform_or_RH_admission=False, objective_preserved=False,
                 gradient_or_merit_certified=False, column_norms_independently_verified=False,
                 scaled_trace_bound_certified=False)
    for key, value in fixed.items():
        require(type(review.get(key)) is type(value) and review[key] == value,
                'unchanged balanced cone scope ' + key)
    work = review.get('joint_work', {})
    require(work.get('max_work') == 450000000 and work.get('whole_archive_audit_allocation') == 25000000,
            'one joint worker and archive work ceiling')
    worker_work, audit_work = work.get('worker_reserved_work'), work.get('whole_archive_audit_operations')
    require(type(worker_work) is int and 0 <= worker_work <= 425000000
            and type(audit_work) is int and 0 <= audit_work <= 25000000
            and work.get('joint_reserved_plus_actual_work') == worker_work + audit_work
            and worker_work + audit_work <= 450000000, 'all required verification included in work total')
    require(len(execution.get('results', [])) == 1, 'one fixed balanced cone transport')
    transport, job = execution['results'][0], review.get('job')
    scope(job)
    require(job.get('transport_status') == transport.get('status')
            and job.get('worker_status') == (record.get('status') if record else None),
            'bound terminal balanced cone status')
    available = (transport.get('status') == 'available' and record is not None
                 and record.get('status') == 'endpoint_verified')
    require(job.get('endpoint_verified') is available, 'strict endpoint availability')
    for value in (record, proposal, endpoint, check):
        if value is not None:
            scope(value)
    if check is not None:
        require(check == review.get('search_check'), 'same independent search receipt')
    if not available:
        require(job.get('finite_candidate_feasible') is None, 'incomplete run has no finite verdict')
        return False
    require(record.get('deadline_exceeded') is False and record.get('endpoint_verified') is True,
            'complete endpoint within declared deadline')
    require(type(proposal) is dict and proposal.get('status') == 'proposed'
            and proposal.get('complete') is True, 'one complete bounded numerical proposal')
    require(type(endpoint) is dict and endpoint.get('complete') is True, 'one complete exact endpoint')
    require(type(check) is dict and check.get('verified') is True and check.get('complete') is True
            and check.get('endpoint_verified') is True, 'independent endpoint checked')
    exact = check.get('endpoint_check', {})
    require(exact.get('all_original_equations_checked') == 5641 and exact.get('original_variables') == 1957
            and exact.get('candidate_hash') == endpoint.get('candidate_hash')
            and exact.get('licensed_affine_uniqueness') is True and exact.get('full_elimination_replayed') is False,
            'original source domain and licensed affine endpoint')
    require(job.get('lifecycle', {}).get('ledger', {}).get('all_stages_committed') is True,
            'complete conservative balanced cone ledger')
    feasibility = exact.get('exact_candidate_checks', {})
    require(feasibility.get('equality_complete') is True and feasibility.get('equality_mismatch_count') == 0
            and feasibility.get('scalar_signs_complete') is True, 'every exact equation and sign checked')
    blocks = feasibility.get('psd_blocks', {})
    require(set(blocks) == {'full_child', 'full_parent', 'storage_K'}
            and all(type(v.get('psd')) is bool for v in blocks.values()), 'all original PSD cones checked')
    negatives = feasibility.get('negative_scalar_count')
    require(type(negatives) is int and negatives >= 0, 'exact negative scalar count')
    feasible = negatives == 0 and all(v['psd'] for v in blocks.values())
    for value in (feasibility, exact, check, record, job):
        require(value.get('finite_candidate_feasible') is feasible, 'finite verdict follows complete checks')
    return True


def completed_archive():
    protocol, sources = read(RUN / 'protocol.json', 65536), read(RUN / 'source_seal.json', 65536)
    CHECK.verify_protocol(protocol, protocol['parent_license'])
    require(set(sources) == set(CHECK.source_names()), 'complete frozen source closure')
    bind(ROOT, sources)
    bind(RUN / 'frozen_source', sources)
    actual_sources = {str(p.relative_to(RUN / 'frozen_source'))
                      for p in (RUN / 'frozen_source').rglob('*') if p.is_file()}
    require(actual_sources == set(sources), 'complete frozen source inventory')
    seal, inputs = read(RUN / 'seal.json'), read(RUN / 'input.json')
    for name in ('protocol', 'source_seal', 'input'):
        require(seal.get(name + '_sha256') == sha(RUN / (name + '.json')), 'frozen run seal ' + name)
    require(set(inputs.get('input_sha256', {})) == set(CHECK.INPUTS), 'complete numerical inputs')
    bind(ROOT, inputs['input_sha256'])
    terminal = read(RUN / 'receipt.json')
    CHECK.verify_inventory(RUN, terminal)
    require(terminal.get('source_count') == len(sources), 'terminal source count')
    execution = read(RUN / 'execution.json')
    CHECK.verify_runtime(execution)
    require(read(RUN / 'run_started.json') == dict(protocol_sha256=sha(RUN / 'protocol.json')),
            'exclusive frozen execution')
    tests = read(RUN / 'tests.json')
    match = re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$', tests.get('stdout', '') + tests.get('stderr', ''))
    require(tests.get('returncode') == 0 and match is not None, 'passed prescore tests')
    review = read(RUN / 'independent_verification.json')
    names = {'protocol', 'source_seal', 'input', 'seal', 'tests', 'execution', 'receipt'}
    require(set(review.get('input_sha256', {})) == names, 'complete stem-based review bindings')
    bind(RUN, {name + '.json': value for name, value in review['input_sha256'].items()})
    require(review.get('source_count') == len(sources) and review.get('tests_passed') == int(match.group(1)),
            'complete audited calibration')
    values = {key: read(RUN / 'jobs' / name, cap) if (RUN / 'jobs' / name).exists() else None
              for key, name, cap in [('record', 'search-job.json', 65536),
                                     ('proposal', 'proposal.json', CHECK.ARTIFACT_CAPS['proposal']),
                                     ('endpoint', 'endpoint.json', CHECK.ARTIFACT_CAPS['endpoint']),
                                     ('check', 'check.json', CHECK.ARTIFACT_CAPS['check'])]}
    available = validate_outcome(review, execution, **values)
    return dict(protocol=protocol, sources=sources, review=review, execution=execution,
                available=available, **values)


def load_inputs():
    for folder, schema, count in ((PREVIOUS, 20, 291), (SEED_PUBLICATION, 18, 317)):
        manifest = read(folder / 'manifest.json', 1048576)
        require(len(manifest['files']) == count and read(folder / 'report.json').get('schema') == schema,
                'completed immutable publication ' + str(schema))
        bind(ROOT, manifest['files'])
    return completed_archive()


def finite_mp_approx(record):
    if record is None:
        return None
    require(type(record) is list and len(record) == 3, 'bounded finite record for display')
    sign, mantissa, exponent = record
    require(type(sign) is int and sign in (0, 1) and type(mantissa) is str and 0 < len(mantissa) <= 68
            and type(exponent) is int and abs(exponent) <= 4096, 'bounded display conversion')
    value = Fraction((-1 if sign else 1) * int(mantissa, 16))
    value = value * 2**exponent if exponent >= 0 else value / 2**(-exponent)
    return float(value)


def merit_summary(proposal):
    if not proposal or proposal.get('complete') is not True:
        return None
    initial = proposal.get('initial_block_penalties', [])
    final = initial
    accepted = 0
    for item in proposal.get('iterations', []):
        for trial in item.get('trials', []):
            if trial.get('armijo_passed') is True:
                final = trial.get('block_penalties', [])
                accepted += 1
    require(len(initial) == len(final) == len(proposal.get('normalizers', [])) == 3,
            'all three raw cone penalties remain visible')
    require(len(proposal.get('initial_normalized_blocks', [])) == 3
            and len(proposal.get('final_normalized_blocks', [])) == 3,
            'all three normalized cone penalties remain visible')
    result = dict(initial_objective=finite_mp_approx(proposal.get('initial_objective')),
                  final_objective=finite_mp_approx(proposal.get('final_objective')),
                  accepted_iterations=accepted,
                  normalizers=proposal['normalizers'],
                  gradient_or_merit_certified=False, model_optimality_certified=False,
                  blocks={})
    for i, name in enumerate(('scalar', 'C', 'H')):
        result['blocks'][name] = dict(
            initial=finite_mp_approx(initial[i]), final=finite_mp_approx(final[i]),
            initial_normalized=finite_mp_approx(proposal['initial_normalized_blocks'][i]),
            final_normalized=finite_mp_approx(proposal['final_normalized_blocks'][i]))
    result['initial_unweighted_total'] = sum(v['initial'] for v in result['blocks'].values())
    result['final_unweighted_total'] = sum(v['final'] for v in result['blocks'].values())
    return result


def report(stage):
    review, proposal, endpoint, check, record = [stage[k] for k in ('review', 'proposal', 'endpoint', 'check', 'record')]
    return dict(schema=21, previous_research_publication='publication-020',
                previous_manifest_sha256=sha(PREVIOUS / 'manifest.json'),
                previous_report_sha256=sha(PREVIOUS / 'report.json'),
                base_center_publication='publication-018', numerical_warm_start_publication='publication-020',
                affine_chart_publication='publication-017',
                numerical_seed_manifest_sha256=sha(SEED_PUBLICATION / 'manifest.json'),
                independent_receipt_sha256=sha(RUN / 'independent_verification.json'),
                terminal_receipt_sha256=sha(RUN / 'receipt.json'),
                source_count=review['source_count'], tests_passed=review['tests_passed'],
                seed018binding=review['seed018binding'], warm020binding=review['warm020binding'],
                joint_work=review['joint_work'],
                job=review['job'], endpoint_available=stage['available'],
                finite_candidate_feasible=review['job']['finite_candidate_feasible'],
                search_check=check, balanced_defects=merit_summary(proposal),
                proposal_stop_reason=proposal.get('stop_reason') if proposal else None,
                proposal_reason=proposal.get('reason') if proposal else None,
                proposal_counts=proposal.get('counts') if proposal else None,
                candidate_hash=endpoint.get('candidate_hash') if endpoint and stage['available'] else None,
                worker_cost=record.get('cost') if record else None,
                worker_ledger=record.get('ledger') if record else None,
                execution_cost=stage['execution'].get('cost'),
                independent_replay_operations=review['independent_replay_operations'],
                total_independent_audit_operations=review['total_independent_audit_operations'],
                total_independent_audit_cells=review['total_independent_audit_cells'],
                exact_endpoint_rule='f0 + D*z as exact rational sum, then original affine restore and canonical lift',
                coordinate_change='reused strictly positive dyadic diagonal; same feasible set',
                balancing_rule='max of three cone penalties divided by fixed positive initial normalizers',
                new_column_responses=0,
                gradient_or_merit_certified=False, uniform_or_RH_admission=False,
                original_objective_preserved=False, parent_source_rebuilds=0, full_elimination_replayed=False,
                remaining_obligations=['candidate satisfying all finite original nonnegativity and PSD constraints',
                                       'universal nonconstant identity for the fixed candidate',
                                       'uniform arithmetic inequality and ordinary-zeta recovery premises'],
                limits=CHECK.LIMITS, resources=CHECK.PARALLEL,
                analyses=[dict(file=name, sha256=sha(ROOT / name)) for name in ANALYSES],
                handoff=NOTE, **FLAGS)


def publish():
    require(not OUT.exists(), 'exclusive publication021')
    stage = load_inputs()
    latest = read(BASE / 'latest.json')
    require(latest.get('publication') == 'publication-020'
            and latest.get('manifest_sha256') == sha(PREVIOUS / 'manifest.json')
            and latest.get('report_sha256') == sha(PREVIOUS / 'report.json'), 'latest completed publication020')
    files = {ROOT / NOTE, PREVIOUS / 'manifest.json', PREVIOUS / 'report.json',
             SEED_PUBLICATION / 'manifest.json', SEED_PUBLICATION / 'report.json'}
    files.update(ROOT / name for name in ANALYSES + publisher_sources() + CHECK.INPUTS)
    files.update(ROOT / name for name in stage['sources'])
    files.update(path for path in RUN.rglob('*') if path.is_file())
    hashes = {str(path.relative_to(ROOT)): sha(path) for path in sorted(files)}
    result = report(stage)
    OUT.mkdir()
    (OUT / 'frozen_source').mkdir()
    for name in (SELF, TEST, NOTE):
        path = OUT / ('frozen_source/' + name if name.endswith('.py') else name)
        with path.open('xb') as handle:
            handle.write((ROOT / name).read_bytes())
        hashes[str(path.relative_to(ROOT))] = sha(path)
    write(OUT / 'report.json', result)
    hashes[str((OUT / 'report.json').relative_to(ROOT))] = sha(OUT / 'report.json')
    write(OUT / 'manifest.json', dict(schema=1, files=hashes, **FLAGS))
    bind(ROOT, hashes)
    require(read(BASE / 'latest.json') == latest, 'no intervening publication')
    write(BASE / 'latest-021.tmp', dict(publication='publication-021', manifest_sha256=sha(OUT / 'manifest.json'),
                                      report_sha256=sha(OUT / 'report.json'), **FLAGS))
    (BASE / 'latest-021.tmp').replace(BASE / 'latest.json')
    return dict(publication='publication-021', bound_files=len(hashes), **FLAGS)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['validate', 'publish'])
    args = parser.parse_args()
    print(json.dumps(publish() if args.action == 'publish' else report(load_inputs()), sort_keys=True))
