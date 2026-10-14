"""Publish checked free-coordinate search evidence and a separate scalar diagnostic."""
import argparse
import ast
import json
from pathlib import Path
import re
import subprocess
import sys

import publish_cancellation_primitive_state_triangular_restoration as OLD
import check_primitive_state_free_cone_search_run as CHECK
import primitive_state_uniform_scalar_diagnostic as SCALAR

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
RUN = BASE / 'primitive-state-free-cone-search-001'
PREVIOUS = BASE / 'publication-017'
NOTE = 'PRIMITIVE_STATE_FREE_CONE_SEARCH_HANDOFF.txt'
ANALYSES = ['primitive_state_free_search_uniform_bridge_analysis_v1.txt',
            'primitive_state_universal_identity_backend_analysis_v1.txt']
SELF = 'publish_cancellation_primitive_state_free_cone_search.py'
TEST = 'test_publish_cancellation_primitive_state_free_cone_search.py'
SCALAR_FILES = ['primitive_state_uniform_scalar_diagnostic.py',
                'test_primitive_state_uniform_scalar_diagnostic.py']
FLAGS = dict(CHECK.FLAGS)
read, sha, require, bind, write = OLD.read, OLD.sha, OLD.require, OLD.bind, OLD.write


def publisher_sources():
    pending = [n[:-3] for n in [SELF, TEST, *SCALAR_FILES]]
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


def validate_outcome(review, execution, record, proposal, endpoint, check):
    CHECK.scope(review)
    require(review.get('schema') == 'primitive-state-free-cone-search-independent-review-v1'
            and review.get('all_passed') is True, 'completed independent free search audit')
    for key, value in dict(original_finite_equations=5641, original_variables=1957,
                           rank=779, free_coordinates=445, parent_source_rebuilds=0,
                           full_elimination_replayed=False, uniform_or_RH_admission=False,
                           objective_preserved=False, gradient_or_merit_certified=False).items():
        require(type(review.get(key)) is type(value) and review[key] == value,
                'unchanged free search scope ' + key)
    require(len(execution.get('results', [])) == 1, 'one fixed free search transport')
    transport = execution['results'][0]
    job = review.get('job')
    require(type(job) is dict, 'explicit audited search outcome')
    CHECK.scope(job)
    require(job.get('transport_status') == transport.get('status')
            and job.get('worker_status') == (record.get('status') if record else None),
            'bound terminal search status')
    available = transport.get('status') == 'available' and record is not None and record.get('status') == 'endpoint_verified'
    require(job.get('endpoint_verified') is available, 'strict completed endpoint availability')
    if record is not None:
        CHECK.scope(record)
    if check is not None:
        CHECK.scope(check)
        require(check == review.get('search_check'), 'same independent search receipt')
    if available:
        require(record.get('deadline_exceeded') is False and record.get('endpoint_verified') is True,
                'complete endpoint within declared deadline')
        require(type(proposal) is dict and proposal.get('status') == 'proposed' and proposal.get('complete') is True,
                'one complete preregistered numerical proposal')
        require(type(endpoint) is dict and endpoint.get('complete') is True, 'one complete exact endpoint')
        CHECK.scope(proposal)
        CHECK.scope(endpoint)
        require(type(check) is dict and check.get('verified') is True and check.get('complete') is True
                and check.get('endpoint_verified') is True, 'independent exact endpoint verified')
        exact = check.get('endpoint_check', {})
        require(exact.get('all_original_equations_checked') == 5641 and exact.get('original_variables') == 1957
                and exact.get('candidate_hash') == endpoint.get('candidate_hash')
                and exact.get('licensed_affine_uniqueness') is True and exact.get('full_elimination_replayed') is False,
                'original source domain and licensed affine endpoint')
        require(job.get('lifecycle', {}).get('ledger', {}).get('all_stages_committed') is True,
                'complete conservative search ledger')
        feasibility = exact.get('exact_candidate_checks', {})
        require(feasibility.get('equality_complete') is True and feasibility.get('equality_mismatch_count') == 0
                and feasibility.get('scalar_signs_complete') is True,
                'every exact equality and scalar sign checked')
        blocks = feasibility.get('psd_blocks', {})
        require(set(blocks) == {'full_child', 'full_parent', 'storage_K'}
                and all(type(v.get('psd')) is bool for v in blocks.values()), 'every original PSD cone checked')
        negatives = feasibility.get('negative_scalar_count')
        require(type(negatives) is int and negatives >= 0, 'exact negative scalar count')
        feasible = negatives == 0 and all(v['psd'] for v in blocks.values())
        for value in (feasibility, exact, check, record, job):
            require(value.get('finite_candidate_feasible') is feasible, 'finite outcome follows complete original cone checks')
    else:
        require(job.get('finite_candidate_feasible') is None, 'incomplete transport admits no candidate')
    return available


def completed_archive():
    protocol = CHECK.read(RUN / 'protocol.json', 65536)
    CHECK.verify_protocol(protocol, protocol['parent_license'])
    sources = CHECK.read(RUN / 'source_seal.json', 65536)
    require(set(sources) == set(CHECK.source_names()), 'complete frozen search source closure')
    bind(ROOT, sources)
    bind(RUN / 'frozen_source', sources)
    require({str(p.relative_to(RUN / 'frozen_source')) for p in (RUN / 'frozen_source').rglob('*') if p.is_file()} == set(sources),
            'complete frozen search source inventory')
    seal = read(RUN / 'seal.json')
    for name in ('protocol', 'source_seal', 'input'):
        require(seal.get(name + '_sha256') == sha(RUN / (name + '.json')), 'preregistered search seal ' + name)
    inputs = read(RUN / 'input.json')
    require(set(inputs.get('input_sha256', {})) == set(CHECK.INPUTS), 'complete search parent bindings')
    bind(ROOT, inputs['input_sha256'])
    terminal = read(RUN / 'receipt.json')
    CHECK.verify_inventory(RUN, terminal)
    require(terminal.get('source_count') == len(sources), 'complete terminal source count')
    execution = read(RUN / 'execution.json')
    CHECK.verify_runtime(execution)
    require(read(RUN / 'run_started.json') == dict(protocol_sha256=sha(RUN / 'protocol.json')), 'exclusive frozen search execution')
    tests = read(RUN / 'tests.json')
    match = re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$', tests.get('stdout', '') + tests.get('stderr', ''))
    require(tests.get('returncode') == 0 and match is not None, 'passed frozen search calibration')
    review = read(RUN / 'independent_verification.json')
    names = {'protocol', 'source_seal', 'input', 'seal', 'tests', 'execution', 'receipt'}
    require(set(review.get('input_sha256', {})) == names, 'complete stem-only independent review inputs')
    bind(RUN, {name + '.json': value for name, value in review['input_sha256'].items()})
    require(review.get('source_count') == len(sources) and review.get('tests_passed') == int(match.group(1))
            and review.get('parent_bound_files') == 297, 'published parent and calibration dimensions')
    values = {key: CHECK.read(RUN / 'jobs' / name) if (RUN / 'jobs' / name).exists() else None
              for key, name in [('record', 'search-job.json'), ('proposal', 'proposal.json'),
                                ('endpoint', 'endpoint.json'), ('check', 'check.json')]}
    available = validate_outcome(review, execution, **values)
    return dict(protocol=protocol, sources=sources, review=review, execution=execution,
                available=available, **values)


def load_inputs():
    prior = OLD.load_inputs()
    manifest = read(PREVIOUS / 'manifest.json')
    bind(ROOT, manifest['files'])
    require(len(manifest['files']) == 297 and read(PREVIOUS / 'report.json').get('schema') == 17,
            'completed publication017 parent')
    priors = dict(prior['priors'])
    priors['publication-017'] = dict(manifest_sha256=sha(PREVIOUS / 'manifest.json'), bound_files=297)
    return dict(priors=priors, stage=completed_archive())


def report(inputs):
    stage = inputs['stage']
    review, record, proposal, endpoint, check = [stage[k] for k in ('review', 'record', 'proposal', 'endpoint', 'check')]
    feasible = review['job']['finite_candidate_feasible'] if stage['available'] else None
    scalar = SCALAR.analyze(endpoint['candidate_original_vector']) if stage['available'] else None
    return dict(schema=18, previous_research_publication='publication-017', prior_manifests=inputs['priors'],
                independent_receipt_sha256=sha(RUN / 'independent_verification.json'), terminal_receipt_sha256=sha(RUN / 'receipt.json'),
                source_count=review['source_count'], tests_passed=review['tests_passed'], job=review['job'],
                original_finite_equations=5641, original_variables=1957, projected_variables=1224, rank=779, free_coordinates=445,
                one_fixed_seed=True, endpoint_available=stage['available'], finite_candidate_feasible=feasible,
                proposal_status=proposal.get('status') if proposal else None,
                proposal_stop_reason=proposal.get('stop_reason') if proposal else None,
                proposal_reason=proposal.get('reason') if proposal else None,
                proposal_counts=proposal.get('counts') if proposal else None,
                proposal_initial_merit=proposal.get('initial_merit') if proposal else None,
                proposal_final_merit=proposal.get('final_merit') if proposal else None,
                proposal_check=check.get('proposal_check') if check else None,
                exact_checks=check.get('endpoint_check', {}).get('exact_candidate_checks') if check and check.get('endpoint_check') else None,
                candidate_hash=endpoint.get('candidate_hash') if endpoint and stage['available'] else None,
                worker_cost=record.get('cost') if record else None, worker_ledger=record.get('ledger') if record else None,
                execution_cost=stage['execution'].get('cost'),
                independent_replay_operations=review['independent_replay_operations'], independent_replay_cells=review['independent_replay_cells'],
                total_independent_audit_operations=review['total_independent_audit_operations'],
                total_independent_audit_cells=review['total_independent_audit_cells'],
                original_objective_preserved=False, parent_source_rebuilds=0, full_elimination_replayed=False,
                gradient_or_merit_certified=False, mathematical_cone_feasibility='finite candidate awaiting typed admission' if feasible is True else 'UNKNOWN',
                uniform_scalar_diagnostic=scalar, scalar_diagnostic_scope='separate optional sufficient route; does not constrain the frozen search',
                diagnostic_sources={name: sha(ROOT / name) for name in SCALAR_FILES},
                accepted_proposal=False, uniform_innovation_bound_proved=False,
                next_action='prove the all-scale nonconstant identity and complete arithmetic inequality premises' if feasible is True else
                    'use the finite cone defects to improve numerical search; implement universal source identity rules separately',
                followup_analyses=[dict(file=name, sha256=sha(ROOT / name)) for name in ANALYSES],
                limits=CHECK.LIMITS, resources=CHECK.PARALLEL, handoff=NOTE, **FLAGS)


def publish():
    out = BASE / 'publication-018'
    require(not out.exists(), 'exclusive publication018')
    inputs = load_inputs()
    previous = read(BASE / 'latest.json')
    require(previous.get('publication') == 'publication-017' and previous.get('manifest_sha256') == sha(PREVIOUS / 'manifest.json')
            and previous.get('report_sha256') == sha(PREVIOUS / 'report.json'), 'latest completed publication017')
    tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', 'test_primitive_state_uniform_scalar_diagnostic'],
                           cwd=ROOT, capture_output=True, text=True, timeout=60)
    require(tests.returncode == 0 and re.search(r'Ran 9 tests .*\n\s*OK\s*$', tests.stderr), 'passed separate scalar diagnostic calibration')
    result = report(inputs)
    files = {ROOT / NOTE, PREVIOUS / 'manifest.json', PREVIOUS / 'report.json'}
    files.update(ROOT / name for name in ANALYSES + publisher_sources() + CHECK.INPUTS)
    files.update(ROOT / name for name in inputs['stage']['sources'])
    files.update(path for path in RUN.rglob('*') if path.is_file() and '__pycache__' not in path.parts)
    hashes = {str(path.relative_to(ROOT)): sha(path) for path in sorted(files)}
    out.mkdir()
    (out / 'frozen_source').mkdir()
    for name in (NOTE, SELF, TEST, *SCALAR_FILES):
        path = out / ('frozen_source/' + name if name.endswith('.py') else name)
        path.write_bytes((ROOT / name).read_bytes())
        hashes[str(path.relative_to(ROOT))] = sha(path)
    write(out / 'diagnostic-tests.json', dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr,
                                            charged_work_reserve=2000000, **FLAGS))
    hashes[str((out / 'diagnostic-tests.json').relative_to(ROOT))] = sha(out / 'diagnostic-tests.json')
    write(out / 'report.json', result)
    hashes[str((out / 'report.json').relative_to(ROOT))] = sha(out / 'report.json')
    write(out / 'manifest.json', dict(schema=1, files=hashes, **FLAGS))
    bind(ROOT, hashes)
    load_inputs()
    bind(ROOT, hashes)
    require(read(BASE / 'latest.json') == previous, 'no intervening publication')
    write(BASE / 'latest-018.tmp', dict(publication='publication-018', manifest_sha256=sha(out / 'manifest.json'),
                                      report_sha256=sha(out / 'report.json'), **FLAGS))
    (BASE / 'latest-018.tmp').replace(BASE / 'latest.json')
    return dict(publication='publication-018', bound_files=len(hashes), **FLAGS)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['validate', 'publish'])
    args = parser.parse_args()
    print(json.dumps(publish() if args.action == 'publish' else report(load_inputs()), sort_keys=True))
