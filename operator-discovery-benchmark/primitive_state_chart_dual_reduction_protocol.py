"""Frozen premises and one complete allocation for stronger exact LP reduction."""
import primitive_state_chart_dual_geometry_protocol as OLD
import re

ROOT, BASE = OLD.ROOT, OLD.BASE
FLAGS = dict(OLD.FLAGS)
encoded, read, write, require, runtime = OLD.encoded, OLD.read, OLD.write, OLD.require, OLD.runtime
CHART, CHART_REVIEW, CHART_REPORT = OLD.CHART, OLD.REVIEW, OLD.REPORT
RAYS = OLD.RAYS
GEOMETRY = BASE+'primitive-state-chart-dual-geometry-search-001/jobs/geometry.json'
REVIEW = BASE+'primitive-state-chart-dual-geometry-search-001/independent_verification.json'
REPORT = BASE+'publication-030/report.json'
CAPS = {CHART:8388608, CHART_REVIEW:8388608, CHART_REPORT:1048576,
        RAYS:8388608, GEOMETRY:16777216, REVIEW:8388608, REPORT:1048576}
ALLOCATIONS = dict(preparation=40000000, reduction=100000000, native=160000000,
                   restoration=70000000, final_independent=80000000)
SYNTHETIC_WORK = dict(development_operations=1403519, root_and_scaffolding_reserve=1000000)
LIMITS = dict(max_work=450000000, allocations=ALLOCATIONS,
              synthetic_test_reserve_within_preparation=25000000,
              synthetic_work=SYNTHETIC_WORK,
              independent_io_reserve_within_preparation=10000000,
              cooperative_seconds=3600, independent_cooperative_seconds=3600,
              max_bits=4096, max_temporary_bits=8193, max_cells=6000000,
              max_reduction_bytes=67108864, max_proposal_bytes=8388608,
              max_check_bytes=8388608, max_metadata_bytes=65536,
              max_source_snapshot_bytes=8388608)
PARALLEL = dict(OLD.PARALLEL)
TESTS = ['test_primitive_state_chart_dual_reduction',
         'test_check_primitive_state_chart_dual_reduction',
         'test_primitive_state_chart_dual_reduction_workflow']
POLICY = dict(max_elimination_rounds=8,
              propagation='all same-sign nonzero coefficients of a homogeneous row force their nonnegative weights zero',
              components='discard only closed components with zero target; extend by zero',
              pivot='minimum Markowitz product, then row size, column count, column index, row index',
              elimination='exact forward row operations on augmented equations',
              round='propagate and discard components; eliminate; propagate and discard components',
              termination='unchanged active columns or eight rounds; maximality is not a proof claim',
              lift='retained original representative weights, zero on every omitted ray',
              native_method='highs-ds', native_presolve=False, native_attempts=1,
              native_iteration_hard_cap=10000,
              native_iteration_rule='dimension-only preparation and dense proxy before scaling',
              exact_restoration_attempts=1, max_support=443,
              support='all strictly positive successful native coordinates',
              free_support_values='zero', normalization='lambda*b=-1')


def parent():
    return dict(chart=CHART, chart_review=CHART_REVIEW, chart_report=CHART_REPORT,
                rays=RAYS, geometry=GEOMETRY, geometry_review=REVIEW, geometry_report=REPORT)


def ledger():
    return dict(max_work=450000000, allocations=ALLOCATIONS,
                total_work_reserve=sum(ALLOCATIONS.values()),
                final_independent_reserved=True, retries=0)


def synthetic_receipt(stdout):
    records = re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$', stdout, re.M)
    names = TESTS[:2]
    require(len(records) == 2 and sorted(name for name, _ in records) == sorted(names),
            'both metered synthetic modules report once')
    modules = {name:int(value) for name, value in records}
    frozen = sum(modules.values())
    total = frozen+sum(SYNTHETIC_WORK.values())
    require(total <= 25000000, 'all development and frozen synthetic work shares25m')
    return dict(SYNTHETIC_WORK, module_operations=modules,
                frozen_suite_operations=frozen, total_charged=total, max_work=25000000)


def protocol():
    return dict(schema='primitive-state-chart-dual-reduction-run-v1', parent=parent(),
                input_caps=CAPS, limits=LIMITS, parallel=PARALLEL, policy=POLICY,
                tests=TESTS, independent_audits=1, no_hashes=True,
                source_rebuilds=0, old_elimination_replays=0,
                source_lp_rows=317, source_lp_columns=695, original_rays=851,
                separately_verifiable_reduction=True, **FLAGS)


def license_parent(chart_report, chart_review, report, review):
    OLD.OLD.license_parent(chart_report, chart_review)
    require(report.get('schema') == 30 and report.get('status') == 'GEOMETRY_VERIFIED'
            and report.get('geometry_verified') is True
            and report.get('independent_audit_complete') is True,
            'designated completed030 geometry proof')
    check = review.get('independent_check') or {}
    require(review.get('schema') == 'primitive-state-chart-dual-geometry-independent-review-v1'
            and review.get('status') == 'GEOMETRY_VERIFIED'
            and review.get('all_passed') is True and review.get('geometry_verified') is True
            and review.get('resource_failure') is None
            and check.get('schema') == 'primitive-state-chart-dual-geometry-independent-check-v1'
            and check.get('verified') is True and check.get('complete') is True
            and check.get('exact_compression_verified') is True,
            'complete independent exact-compression premise')
    for value in (report, review):
        require(value.get('finite_augmented_cone_infeasibility_certified') is False,
                'parent supplies no separator')
        for key in FLAGS:
            require(value.get(key) is False, 'parent finite scope '+key)
