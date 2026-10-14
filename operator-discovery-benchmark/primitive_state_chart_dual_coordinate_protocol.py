"""One bounded sparse coordinate proposal on the licensed031 exact system."""
import re
import primitive_state_chart_dual_reduction_protocol as OLD

ROOT, BASE = OLD.ROOT, OLD.BASE
FLAGS = dict(OLD.FLAGS)
encoded, read, write, require, runtime = OLD.encoded, OLD.read, OLD.write, OLD.require, OLD.runtime
CHART, CHART_REVIEW, CHART_REPORT = OLD.CHART, OLD.CHART_REVIEW, OLD.CHART_REPORT
RAYS, GEOMETRY = OLD.RAYS, OLD.GEOMETRY
REDUCTION = BASE+'primitive-state-chart-dual-reduction-001/jobs/reduction.json'
REVIEW = BASE+'primitive-state-chart-dual-reduction-001/independent_verification.json'
REPORT = BASE+'publication-031/report.json'
CAPS = {CHART:8388608, CHART_REVIEW:8388608, CHART_REPORT:1048576,
        RAYS:8388608, GEOMETRY:16777216, REDUCTION:67108864,
        REVIEW:8388608, REPORT:1048576}
ALLOCATIONS = dict(preparation=40000000, model=40000000, numerical=190000000,
                   restoration=90000000, final_independent=90000000)
SYNTHETIC_WORK = dict(development_operations=2019371, root_and_scaffolding_reserve=1000000)
LIMITS = dict(max_work=450000000, allocations=ALLOCATIONS,
              synthetic_test_reserve_within_preparation=25000000,
              synthetic_work=SYNTHETIC_WORK,
              independent_io_reserve_within_preparation=10000000,
              cooperative_seconds=3600, independent_cooperative_seconds=3600,
              max_bits=4096, max_temporary_bits=8193, max_cells=6000000,
              max_proposal_bytes=8388608, max_check_bytes=8388608,
              max_metadata_bytes=65536, max_source_snapshot_bytes=8388608)
PARALLEL = dict(OLD.PARALLEL)
TESTS = ['test_primitive_state_chart_dual_coordinate',
         'test_check_primitive_state_chart_dual_coordinate',
         'test_primitive_state_chart_dual_coordinate_workflow']
POLICY = dict(method='cyclic nonnegative coordinate descent on squared residual plus positive L1',
              penalty_exponents=list(range(1,32,2)), final_penalty_zero=True,
              penalty_reference='max(0,max_j dot(scaled_column_j,scaled_rhs))',
              penalty_weights='unit cost in positively scaled coordinates; new heuristic objective',
              initial_vector='all zero', coordinate_order='ascending retained column position',
              coordinate_update='max(0,x_j-(dot(column_j,residual)+penalty)/squared_column_norm)',
              scaling='old029 positive exact row and column infinity scaling before finite conversion',
              refresh_interval_sweeps=16, refresh_at_each_phase_end=True,
              residual_refresh='math.fsum per row of -rhs and sparse coefficient products',
              max_sweeps_per_phase=10000,
              sweep_allowance='largest common S fitting explicit numerical reservation before coefficient scores',
              early_phase_stop='one full sweep changes no stored coordinate; no convergence theorem',
              checkpoint='every completed penalty phase after a fresh residual computation',
              selection='minimum (relative L2 residual,support size,phase index) among finite checkpoints with1..443 positive coordinates',
              support='all strictly positive selected coordinates; no threshold or trimming',
              numerical_attempts=1, exact_restoration_attempts=1, max_support=443,
              free_support_values='zero', normalization='lambda*b=-1')


def parent():
    return dict(chart=CHART, chart_review=CHART_REVIEW, chart_report=CHART_REPORT,
                rays=RAYS, geometry=GEOMETRY, reduction=REDUCTION,
                reduction_review=REVIEW, reduction_report=REPORT)


def ledger():
    return dict(max_work=450000000, allocations=ALLOCATIONS,
                total_work_reserve=sum(ALLOCATIONS.values()),
                final_independent_reserved=True, retries=0)


def synthetic_receipt(stdout):
    records = re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$', stdout, re.M)
    require(len(records) == 2 and sorted(name for name,_ in records) == sorted(TESTS[:2]),
            'both metered synthetic modules report once')
    modules = {name:int(value) for name,value in records}
    frozen = sum(modules.values()); total = frozen+sum(SYNTHETIC_WORK.values())
    require(total <= 25000000, 'cumulative development and frozen synthetic25m')
    return dict(SYNTHETIC_WORK, module_operations=modules,
                frozen_suite_operations=frozen, total_charged=total, max_work=25000000)


def protocol():
    return dict(schema='primitive-state-chart-dual-coordinate-run-v1', parent=parent(),
                input_caps=CAPS, limits=LIMITS, parallel=PARALLEL, policy=POLICY,
                tests=TESTS, independent_audits=1, no_hashes=True,
                source_rebuilds=0, old_elimination_replays=0, reduction_replays=0,
                source_rows=302, source_columns=687, original_rays=851, **FLAGS)


def license_parent(chart_report, chart_review, report, review):
    OLD.OLD.OLD.license_parent(chart_report, chart_review)
    check = review.get('independent_check') or {}
    require(report.get('schema') == 31 and report.get('status') == 'REDUCTION_VERIFIED'
            and report.get('reduction_verified') is True
            and report.get('independent_audit_complete') is True,
            'designated completed031 exact reduction')
    require(review.get('schema') == 'primitive-state-chart-dual-reduction-independent-review-v1'
            and review.get('status') == 'REDUCTION_VERIFIED'
            and review.get('all_passed') is True and review.get('reduction_verified') is True
            and review.get('resource_failure') is None and review.get('validation_failure') is None
            and check.get('schema') == 'primitive-state-chart-dual-reduction-independent-check-v1'
            and check.get('verified') is True and check.get('complete') is True
            and check.get('reduction_verified') is True
            and check.get('restricted_system_inconsistent') is False,
            'complete independently licensed reduction premise')
    for value in (report, check):
        require(value.get('reduced_rows') == 302 and value.get('reduced_columns') == 687,
                'licensed302x687 numerical source')
    for value in (report, review):
        require(value.get('finite_augmented_cone_infeasibility_certified') is False,
                'parent supplies no separator')
        for key in FLAGS:
            require(value.get(key) is False, 'parent finite scope '+key)
