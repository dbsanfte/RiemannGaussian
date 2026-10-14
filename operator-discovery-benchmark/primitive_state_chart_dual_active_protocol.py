"""One sparse active-set proposal on the licensed031 exact equations."""
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
SYNTHETIC_WORK = dict(development_operations=2573512, root_and_scaffolding_reserve=1000000)
LIMITS = dict(OLD.LIMITS, allocations=ALLOCATIONS, synthetic_work=SYNTHETIC_WORK)
PARALLEL = dict(OLD.PARALLEL)
TESTS = ['test_primitive_state_chart_dual_active',
         'test_check_primitive_state_chart_dual_active',
         'test_primitive_state_chart_dual_active_workflow']
POLICY = dict(method='nonnegative active-set with sparse preconditioned CGLS face solves',
              objective='one half squared L2 residual; no penalty',
              initial_vector='publication032 selected vector, fresh residual; no imported score',
              diagonal_metric='positive finite squared scaled column L2 norms',
              scaling='old029 positive exact row and column infinity scaling before finite conversion',
              entry='maximum strictly positive inactive correlation divided by column norm; index breaks ties',
              first_face='strictly positive initial support',
              after_boundary='refine surviving face before entering another column',
              inner='preconditioned CGLS from current face values, fresh residual each step',
              inner_limit='min(128,2*active_size)',
              boundary='smallest x_j/(x_j-z_j) over z_j<=0; bothzero gives0; explicitly zero all minimizers',
              max_faces=1000,
              products='finite guarded sparse math.fsum; stable L2 norms',
              completion='reserved work boundary, zero reported residual, no positive inactive correlation, Krylov breakdown or face limit',
              selection='minimum (relative residual,support size,iteration) over initial and complete face checkpoints with1..443 positive entries',
              support='all strictly positive selected coordinates; no threshold or trimming',
              final_diagnostic='fresh residual and norm(sqrt(D)*(x-max(0,x+correlation/D)))',
              numerical_attempts=1, exact_restoration_attempts=1, max_support=443,
              free_support_values='zero', normalization='lambda*b=-1')

SEED = BASE+'primitive-state-chart-dual-coordinate-001/jobs/proposal.json'
CAPS[SEED] = 8388608
license_parent = OLD.license_parent


def parent():
    return dict(OLD.parent(), warm_seed=SEED)


def ledger():
    return dict(max_work=450000000, allocations=ALLOCATIONS,
                total_work_reserve=sum(ALLOCATIONS.values()),
                final_independent_reserved=True, retries=0)


def synthetic_receipt(stdout):
    records = re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$', stdout, re.M)
    require(len(records) == 2 and sorted(name for name,_ in records) == sorted(TESTS[:2]),
            'both active-set synthetic modules report once')
    modules = {name:int(value) for name,value in records}
    frozen = sum(modules.values()); total = frozen+sum(SYNTHETIC_WORK.values())
    require(total <= 25000000, 'cumulative development and frozen synthetic25m')
    return dict(SYNTHETIC_WORK, module_operations=modules,
                frozen_suite_operations=frozen, total_charged=total, max_work=25000000)


def protocol():
    return dict(schema='primitive-state-chart-dual-active-run-v1', parent=parent(),
                input_caps=CAPS, limits=LIMITS, parallel=PARALLEL, policy=POLICY,
                tests=TESTS, independent_audits=1, no_hashes=True,
                source_rebuilds=0, old_elimination_replays=0, reduction_replays=0,
                source_rows=302, source_columns=687, original_rays=851, **FLAGS)
