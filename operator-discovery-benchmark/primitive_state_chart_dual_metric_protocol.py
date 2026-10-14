"""One diagonally balanced proposal on the licensed031 exact equations."""
import re
import primitive_state_chart_dual_coordinate_protocol as OLD

ROOT, BASE = OLD.ROOT, OLD.BASE
FLAGS = dict(OLD.FLAGS)
encoded, read, write, require, runtime = OLD.encoded, OLD.read, OLD.write, OLD.require, OLD.runtime
CHART, CHART_REVIEW, CHART_REPORT = OLD.CHART, OLD.CHART_REVIEW, OLD.CHART_REPORT
RAYS, GEOMETRY, REDUCTION = OLD.RAYS, OLD.GEOMETRY, OLD.REDUCTION
REVIEW, REPORT = OLD.REVIEW, OLD.REPORT
CAPS = dict(OLD.CAPS)
ALLOCATIONS = dict(preparation=40000000, model=40000000, numerical=190000000,
                   restoration=90000000, final_independent=90000000)
SYNTHETIC_WORK = dict(development_operations=2713988, root_and_scaffolding_reserve=1000000)
LIMITS = dict(OLD.LIMITS, allocations=ALLOCATIONS, synthetic_work=SYNTHETIC_WORK)
PARALLEL = dict(OLD.PARALLEL)
TESTS = ['test_primitive_state_chart_dual_metric',
         'test_check_primitive_state_chart_dual_metric',
         'test_primitive_state_chart_dual_metric_workflow']
POLICY = dict(method='diagonal-metric accelerated nonnegative projected gradient',
              objective='one half squared L2 residual; no L1 penalty',
              initial_vector='all zero', initial_momentum=1,
              initial_lipschitz=1,
              diagonal_metric='squared scaled column L2 norms; positive finite numerical values',
              scaling='old029 positive exact row and column infinity scaling before finite conversion',
              matrix_products='sparse math.fsum row and column products with finite guards',
              projection='max(0,y-gradient/(L*D)) coordinatewise',
              line_test='squared norm of A*(z-y) <= L*squared norm of sqrt(D)*(z-y)',
              backtrack_factor=2, max_backtracking_trials=32,
              carry_lipschitz=True,
              momentum='t_new=(1+sqrt(1+4*t*t))/2; y=z+(t-1)/t_new*(z-x)',
              restart_interval=64, max_iterations=10000,
              boundary='start a step only if gradient+32*trial+commit+final diagnostic reserve fits',
              completion='accepted boundary work stop, iteration limit, or zero reported residual; no convergence claim',
              checkpoint='every accepted step after fresh residual and momentum computation',
              selection='minimum (relative L2 residual,support size,iteration) among checkpoints with1..443 positive coordinates',
              support='all strictly positive selected coordinates; no threshold or trimming',
              final_diagnostic='fresh residual and L*norm(sqrt(D)*(x-max(0,x-gradient/(L*D)))) at last accepted x',
              numerical_attempts=1, exact_restoration_attempts=1, max_support=443,
              free_support_values='zero', normalization='lambda*b=-1')

parent, license_parent = OLD.parent, OLD.license_parent


def ledger():
    return dict(max_work=450000000, allocations=ALLOCATIONS,
                total_work_reserve=sum(ALLOCATIONS.values()),
                final_independent_reserved=True, retries=0)


def synthetic_receipt(stdout):
    records = re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$', stdout, re.M)
    require(len(records) == 2 and sorted(name for name,_ in records) == sorted(TESTS[:2]),
            'both accelerated synthetic modules report once')
    modules = {name:int(value) for name,value in records}
    frozen = sum(modules.values()); total = frozen+sum(SYNTHETIC_WORK.values())
    require(total <= 25000000, 'cumulative development and frozen synthetic25m')
    return dict(SYNTHETIC_WORK, module_operations=modules,
                frozen_suite_operations=frozen, total_charged=total, max_work=25000000)


def protocol():
    return dict(schema='primitive-state-chart-dual-metric-run-v1', parent=parent(),
                input_caps=CAPS, limits=LIMITS, parallel=PARALLEL, policy=POLICY,
                tests=TESTS, independent_audits=1, no_hashes=True,
                source_rebuilds=0, old_elimination_replays=0, reduction_replays=0,
                source_rows=302, source_columns=687, original_rays=851, **FLAGS)
