"""Fixed inputs and resource limits for a direct chart dual search."""
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
BASE = 'cancellation-arithmetic-results/'
PARENT = BASE + 'primitive-state-augmented-cone-search-001'
PUBLICATION = BASE + 'publication-028'
CHART = PARENT + '/jobs/chart.json'
ENDPOINT = PARENT + '/jobs/endpoint.json'
REVIEW = PARENT + '/independent_verification.json'
REPORT = PUBLICATION + '/report.json'
SCOPE = 'primitive_state_chart_dual_search_resource_scope.txt'
NOTE = 'primitive_state_chart_dual_diagnostic_analysis_v1.txt'
FLAGS = dict(global_bound_proved=False, RH_proved=False,
             universal_identity_proved=False, candidate_admitted=False,
             exact_admission=False, primal_feasibility_proved=False)
ALLOCATIONS = dict(preparation=50000000, assembly=100000000,
                   native=190000000, restoration=60000000,
                   final_independent=50000000)
LIMITS = dict(max_work=450000000, allocations=ALLOCATIONS,
              synthetic_test_reserve_within_preparation=20000000,
              independent_io_reserve_within_preparation=10000000,
              cooperative_seconds=3600, independent_cooperative_seconds=3600,
              max_bits=4096, max_temporary_bits=8193, max_cells=6000000,
              max_proposal_bytes=8388608, max_check_bytes=8388608,
              max_metadata_bytes=65536, max_source_snapshot_bytes=8388608)
PARALLEL = dict(workers=1, worker_memory_bytes=6*1024**3,
                memory_budget_bytes=6*1024**3, timeout_seconds=7200,
                max_jobs=1, max_result_bytes=65536)
CAPS = {CHART:8388608, ENDPOINT:2097152, REVIEW:8388608, REPORT:1048576}
TESTS = ['test_primitive_state_chart_dual_search',
         'test_check_primitive_state_chart_dual_search',
         'test_primitive_state_chart_dual_soundness',
         'test_primitive_state_chart_dual_workflow']
SEARCH = dict(fixed_scalar_rays=371, fixed_matrix_rays=450,
              endpoint_matrix_rays=30, total_rays=851,
              vector_denominator=2**20, matrix_dimension=15,
              native_method='highs-ds', native_presolve=False,
              native_max_iterations=100, native_attempts=1,
              exact_support='all strictly positive native coordinates',
              max_support=443, exact_restoration_attempts=1,
              underdetermined_free_values='zero',
              certificate_normalization='lambda*b=-1')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def runtime():
    require(not sys.flags.optimize and os.environ.get('PYTHONOPTIMIZE', '') in ('', '0'),
            'verified workflows require assertions enabled')


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'),
                       allow_nan=False)+'\n').encode()


def read(path, cap=65536):
    with Path(path).open('rb') as handle:
        data = handle.read(cap+1)
    if len(data) > cap:
        raise OverflowError('bounded input bytes: '+str(path))
    return json.loads(data)


def write(path, value, cap=65536):
    data = encoded(value)
    if len(data) > cap:
        raise OverflowError('bounded output bytes: '+str(path))
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name+'.tmp')
    temporary.write_bytes(data)
    temporary.replace(path)


def parent():
    return dict(publication=PUBLICATION, report=REPORT, chart=CHART,
                endpoint=ENDPOINT, review=REVIEW)


def ledger():
    return dict(max_work=450000000, allocations=ALLOCATIONS,
                total_work_reserve=sum(ALLOCATIONS.values()),
                final_independent_reserved=True, retries=0)


def protocol():
    return dict(schema='primitive-state-chart-dual-run-v1', parent=parent(),
                input_caps=CAPS, limits=LIMITS, parallel=PARALLEL,
                search=SEARCH, tests=TESTS, original_width=1957,
                projected_width=1224, rank=782, free_count=442,
                original_equations=5641, learned_equations=3,
                independent_audits=1, no_hashes=True,
                source_rebuilds=0, old_elimination_replays=0,
                finite_scope='the complete augmented publication028 cone',
                **FLAGS)


def license_parent(report, review):
    require(report.get('schema') == 28 and report.get('status') == 'SCALAR_REJECTED'
            and report.get('coefficient_rank') == 782 and report.get('free_count') == 442
            and report.get('full_equations_checked') == 5644,
            'designated completed publication028')
    require(review.get('schema') == 'primitive-state-augmented-cone-search-independent-review-v1'
            and review.get('status') == 'SCALAR_REJECTED'
            and review.get('resource_failure') is None,
            'designated independent publication028 review')
    for key in ('chart_verified', 'center_verified', 'endpoint_verified',
                'candidate_equations_verified'):
        require(report.get(key) is True and review.get(key) is True,
                'licensed parent '+key)
    require(report.get('independent_audit_complete') is True
            and review.get('all_passed') is True,
            'completed parent independent audit')
    for value in (report, review):
        for key in ('RH_proved', 'global_bound_proved', 'candidate_admitted'):
            require(value.get(key) is False, 'parent finite scope')
