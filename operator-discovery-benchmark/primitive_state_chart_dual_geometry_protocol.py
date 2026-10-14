"""Fixed complete allocation and premises for exact cone geometry discovery."""
import primitive_state_chart_dual_protocol as OLD

ROOT, BASE = OLD.ROOT, OLD.BASE
FLAGS = dict(OLD.FLAGS)
encoded, read, write, require, runtime = OLD.encoded, OLD.read, OLD.write, OLD.require, OLD.runtime
CHART, REVIEW, REPORT = OLD.CHART, OLD.REVIEW, OLD.REPORT
RAYS = BASE+'primitive-state-chart-dual-search-001/jobs/proposal.json'
PREVIOUS_REPORT = BASE+'publication-029/report.json'
PREVIOUS_REVIEW = BASE+'primitive-state-chart-dual-search-001/independent_verification.json'
SCOPE = 'primitive_state_chart_dual_geometry_resource_scope.txt'
NOTE = 'primitive_state_chart_dual_geometry_soundness_v1.txt'
CAPS = {CHART:8388608, REVIEW:8388608, REPORT:1048576,
        RAYS:8388608, PREVIOUS_REPORT:1048576, PREVIOUS_REVIEW:8388608}
ALLOCATIONS = dict(preparation=80000000, geometry=70000000, native=150000000,
                   restoration=80000000, final_independent=70000000)
LIMITS = dict(max_work=450000000, allocations=ALLOCATIONS,
              synthetic_test_reserve_within_preparation=65000000,
              synthetic_work=dict(earlier_and_root_tests_reserve=20000000,
                                  completed_checker_tests=29849297,
                                  frozen_combined_suite_reserve=15000000),
              independent_io_reserve_within_preparation=10000000,
              cooperative_seconds=3600, independent_cooperative_seconds=3600,
              max_bits=4096, max_temporary_bits=8193, max_cells=6000000,
              max_geometry_bytes=16777216, max_proposal_bytes=8388608,
              max_check_bytes=8388608, max_metadata_bytes=65536,
              max_source_snapshot_bytes=8388608)
PARALLEL = dict(OLD.PARALLEL)
TESTS = ['test_primitive_state_chart_dual_geometry_search',
         'test_check_primitive_state_chart_dual_geometry_search',
         'test_primitive_state_chart_dual_geometry_soundness',
         'test_primitive_state_chart_dual_geometry_workflow']
SEARCH = dict(total_rays=851, new_eigensolves=0,
              normal_forms='complete1224 coordinate affine map; exact reverse substitution',
              faces='zero complete responses and opposite signed proportional complete responses',
              column_compression='drop zero; first representative in each positive proportional class',
              row_compression='drop zero augmented; first representative in each nonzero proportional augmented class',
              first_negative_constant='exact singleton separator before any native call',
              objective='positive L1 of retained representative coefficients',
              native_method='highs-ds', native_presolve=False,
              native_iteration_hard_cap=10000,
              native_iteration_rule='dimension-only preparation reserve and dense-proxy reservation before scaling',
              native_attempts=1, exact_restoration_attempts=1,
              underdetermined_free_values='zero',
              max_support=443, certificate_normalization='lambda*b=-1')


def parent():
    return dict(chart=CHART, chart_report=REPORT, chart_review=REVIEW,
                rays=RAYS, previous_report=PREVIOUS_REPORT, previous_review=PREVIOUS_REVIEW)


def ledger():
    return dict(max_work=450000000, allocations=ALLOCATIONS,
                total_work_reserve=sum(ALLOCATIONS.values()),
                final_independent_reserved=True, retries=0)


def protocol():
    return dict(schema='primitive-state-chart-dual-geometry-run-v1', parent=parent(),
                input_caps=CAPS, limits=LIMITS, parallel=PARALLEL, search=SEARCH,
                tests=TESTS, original_width=1957, projected_width=1224,
                rank=782, free_count=442, original_equations=5641,
                learned_equations=3, independent_audits=1,
                separately_verifiable_geometry=True, no_hashes=True,
                source_rebuilds=0, old_elimination_replays=0, **FLAGS)


def license_parent(report, review, previous, previous_review):
    OLD.license_parent(report, review)
    require(previous.get('schema') == 29 and previous.get('status') == 'UNKNOWN'
            and previous.get('finite_augmented_cone_infeasibility_certified') is False,
            'designated completed029 numerical diagnostic')
    require(previous_review.get('schema') == 'primitive-state-chart-dual-independent-review-v1'
            and previous_review.get('workflow_verified') is True
            and previous_review.get('certificate_verified') is False,
            '029 nonadmission, not a new mathematical premise')
