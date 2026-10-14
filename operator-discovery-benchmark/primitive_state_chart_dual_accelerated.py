"""Cold-start sparse accelerated NNLS proposal with one exact restoration.

Sparse products and line tests provide numerical proposals only. Completion
means the bounded trajectory and its final diagnostic finished; admission
still requires the independent full original-coordinate Farkas identity.
"""
from fractions import Fraction as F
import math
import time

import primitive_state_chart_dual_coordinate as MODEL
import primitive_state_chart_dual_search as OLD
import primitive_state_chart_dual_reduction as REUSE
import primitive_state_chart_dual_accelerated_protocol as PROTOCOL

Budget = OLD.Budget
build_model = MODEL.build_model
encoded = OLD.encoded
FLAGS = dict(PROTOCOL.FLAGS)
POLICY = PROTOCOL.POLICY
LIMITS = PROTOCOL.LIMITS
SCHEMA = 'primitive-state-chart-dual-accelerated-search-v1'
NUMERICAL_SCHEMA = 'primitive-state-chart-dual-accelerated-proposal-v1'


def numerical_work_model(m, n, nnz):
    """Dimension-only sparse work proxies, including a final diagnostic."""
    if (any(type(v) is not int for v in (m, n, nnz))
            or not 1 <= m <= 443 or not 1 <= n <= 851 or not n <= nnz <= m * n):
        raise ValueError('bounded nonempty sparse numerical dimensions')
    setup = 8 * nnz + 32 * (m + n) + 65536
    gradient = 8 * nnz + 32 * (m + n) + 512
    trial = 16 * nnz + 64 * (m + n) + 1024
    commit = 32 * (m + n) + 512
    final = 12 * nnz + 64 * (m + n) + 2048
    iteration = gradient + 32 * trial + commit
    return dict(setup=setup, gradient=gradient, trial=trial, commit=commit, final=final,
                iteration_reserve=iteration, minimum_attempt=setup + iteration + final,
                max_iterations=10000, max_backtracking_trials=32)


def _finite(value, reason):
    if not math.isfinite(value):
        raise OverflowError(reason)
    return value


def accelerated_proposal(model, *, deadline, max_operations=190000000, resident_cells=0):
    budget = Budget(deadline, max_operations); budget.resident_cells = resident_cells
    start = time.monotonic()
    out = dict(schema=NUMERICAL_SCHEMA, complete=False, attempted=False,
               max_operations=max_operations, rows=model.get('rows'), columns=model.get('columns_count'),
               nonzeros=model.get('nonzeros'), work_model={}, initial_lipschitz=None,
               checkpoints=[], selected=None, setup_charged=False, final_charged=False,
               gradient_blocks=0, trial_blocks=0, commit_blocks=0,
               stop_reason=None, final_diagnostic=None, **FLAGS)

    def block(kind):
        amount = out['work_model'][kind]; before = budget.operations
        try:
            budget.charge(amount)
        finally:
            # A deadline check can raise after the full block was charged.
            if budget.operations - before == amount:
                if kind in ('setup', 'final'):
                    out[kind + '_charged'] = True
                else:
                    out[kind + '_blocks'] += 1

    def live(extra=0):
        budget.charge(0)
        # The nnz+m sparse product buckets are included in this peak, even
        # though only one fresh product retains its buckets at a time.
        cells = resident_cells + 3 * nnz + 16 * n + 12 * m + 10 * len(out['checkpoints']) + extra
        budget.peak_cells = max(budget.peak_cells, cells)
        if cells > budget.max_cells:
            raise OverflowError('accelerated numerical live cell cap')

    try:
        m, n, nnz = out['rows'], out['columns'], out['nonzeros']
        work = numerical_work_model(m, n, nnz); out['work_model'] = work
        if max_operations < work['minimum_attempt']:
            raise OverflowError('no complete first-step and final diagnostic reservation fits')
        out['attempted'] = True; block('setup'); live()
        columns = model['columns']; rhs = model['rhs']
        if (type(columns) is not list or len(columns) != n or type(rhs) is not list or len(rhs) != m
                or any(type(column) is not dict for column in columns)
                or sum(map(len, columns)) != nnz
                or any(type(q) not in (int, float) or not math.isfinite(q) for q in rhs)):
            raise ValueError('complete finite sparse numerical model')
        target_norm = _finite(math.hypot(*rhs), 'nonfinite target norm')
        if target_norm <= 0:
            raise ValueError('nonzero numerical target required')
        lipschitz = 0.0
        for column in columns:
            budget.charge(0)
            if any(type(i) is not int or not 0 <= i < m or type(q) not in (int, float)
                   or not math.isfinite(q) or q == 0 for i, q in column.items()):
                raise ValueError('nonzero finite sparse column domain')
            norm = _finite(math.hypot(*column.values()), 'nonfinite column norm')
            square = _finite(norm * norm, 'nonfinite squared column norm')
            if square <= 0:
                raise ValueError('positive squared column norm required')
            lipschitz = max(lipschitz, square)
        out['initial_lipschitz'] = lipschitz
        x = [0.0] * n; y = [0.0] * n; momentum = 1.0
        iteration = 0; best = None

        def multiply(vector, *, residual=False):
            live()
            buckets = [[-float(q)] if residual else [] for q in rhs]
            for j, column in enumerate(columns):
                budget.charge(0)
                if vector[j] == 0:
                    continue
                for i, q in column.items():
                    product = _finite(vector[j] * q, 'nonfinite sparse matrix product')
                    buckets[i].append(product)
            values = []
            for terms in buckets:
                budget.charge(0)
                values.append(_finite(math.fsum(terms), 'nonfinite compensated matrix sum'))
            return values

        def transpose(vector):
            values = []
            for column in columns:
                budget.charge(0)
                value = math.fsum(_finite(q * vector[i], 'nonfinite transpose product')
                                  for i, q in column.items())
                values.append(_finite(value, 'nonfinite compensated gradient sum'))
            return values

        def norm_squared(vector):
            norm = _finite(math.hypot(*vector), 'nonfinite line-test norm')
            return _finite(norm * norm, 'nonfinite line-test squared norm')

        while True:
            budget.charge(0)
            if max_operations - budget.operations < work['iteration_reserve'] + work['final']:
                out['stop_reason'] = 'work_boundary'; break
            block('gradient')
            residual_y = multiply(y, residual=True); gradient = transpose(residual_y)
            accepted = False
            for trial_index in range(1, work['max_backtracking_trials'] + 1):
                block('trial'); z = []; direction = []
                for j in range(n):
                    budget.charge(0)
                    ratio = _finite(gradient[j] / lipschitz, 'nonfinite projected gradient ratio')
                    candidate = _finite(y[j] - ratio, 'nonfinite trial coordinate before projection')
                    value = max(0.0, candidate); z.append(value)
                    direction.append(_finite(value - y[j], 'nonfinite trial direction'))
                matrix_direction = multiply(direction)
                residual_z = multiply(z, residual=True)
                left = norm_squared(matrix_direction); direction_squared = norm_squared(direction)
                right = _finite(lipschitz * direction_squared, 'nonfinite line-test right hand side')
                if left <= right:
                    accepted = True; break
                lipschitz = _finite(2 * lipschitz, 'nonfinite doubled Lipschitz estimate')
            if not accepted:
                raise RuntimeError('all32 backtracking trials rejected')
            block('commit')
            residual_norm = _finite(math.hypot(*residual_z), 'nonfinite accepted residual norm')
            relative = _finite(residual_norm / target_norm, 'nonfinite accepted relative residual')
            support = [j for j, value in enumerate(z) if value > 0]
            next_iteration = iteration + 1
            restarted = next_iteration % POLICY['restart_interval'] == 0
            if restarted:
                next_momentum = 1.0; next_y = list(z)
            else:
                square = _finite(momentum * momentum, 'nonfinite momentum square')
                radicand = _finite(1 + _finite(4 * square, 'nonfinite momentum product'),
                                  'nonfinite momentum radicand')
                root = _finite(math.sqrt(radicand), 'nonfinite momentum square root')
                next_momentum = _finite((1 + root) / 2, 'nonfinite next momentum')
                numerator = _finite(momentum - 1, 'nonfinite momentum numerator')
                factor = _finite(numerator / next_momentum, 'nonfinite momentum ratio')
                next_y = []
                for j in range(n):
                    budget.charge(0)
                    difference = _finite(z[j] - x[j], 'nonfinite momentum difference')
                    extrapolation = _finite(factor * difference, 'nonfinite momentum extrapolation')
                    next_y.append(_finite(z[j] + extrapolation, 'nonfinite momentum coordinate'))
            live(10)
            checkpoint = dict(iteration=next_iteration, backtracking_trials=trial_index,
                lipschitz=lipschitz, residual_norm=residual_norm, relative_residual=relative,
                support_size=len(support), momentum_restarted=restarted,
                cumulative_operations=budget.operations)
            out['checkpoints'].append(checkpoint)
            x = z; y = next_y; momentum = next_momentum; iteration = next_iteration
            if 1 <= len(support) <= POLICY['max_support']:
                score = (relative, len(support), iteration)
                if best is None or score < best:
                    best = score
                    out['selected'] = dict(iteration=iteration, scaled_vector=list(x),
                                          support=support, relative_residual=relative)
            if residual_norm == 0:
                out['stop_reason'] = 'zero_reported_residual'; break
            if iteration == work['max_iterations']:
                out['stop_reason'] = 'iteration_limit'; break

        block('final')
        final_residual = multiply(x, residual=True); final_gradient = transpose(final_residual)
        differences = []
        for j in range(n):
            budget.charge(0)
            ratio = _finite(final_gradient[j] / lipschitz, 'nonfinite final gradient ratio')
            candidate = _finite(x[j] - ratio, 'nonfinite final coordinate before projection')
            projected = max(0.0, candidate)
            differences.append(_finite(x[j] - projected, 'nonfinite projected-gradient difference'))
        mapping_norm = _finite(math.hypot(*differences), 'nonfinite projected-gradient norm')
        projected_gradient = _finite(lipschitz * mapping_norm, 'nonfinite scaled projected-gradient norm')
        residual_norm = _finite(math.hypot(*final_residual), 'nonfinite final residual norm')
        relative = _finite(residual_norm / target_norm, 'nonfinite final relative residual')
        diagnostic = dict(iteration=iteration, lipschitz=lipschitz, residual_norm=residual_norm,
                          relative_residual=relative, projected_gradient_norm=projected_gradient)
        budget.charge(0); out['final_diagnostic'] = diagnostic; out['complete'] = True
    except Exception as error:
        out.update(selected=None, reason=str(error) or type(error).__name__,
                   resource_failure=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        out['counts'] = budget.counts(); out['elapsed_seconds'] = time.monotonic() - start
    return out


def search(chart, rays, geometry, reduction, *, deadline, checkpoint=None):
    out = dict(schema=SCHEMA, status='UNKNOWN', route='accelerated_gradient', numerical=None,
               model_stats={}, certificate=None, stage_counts={}, policy=POLICY, limits=LIMITS, **FLAGS)
    model_budget = Budget(deadline, PROTOCOL.ALLOCATIONS['model']); restoration = None

    def progress(phase):
        if checkpoint:
            checkpoint(dict(phase=phase, status=out['status'], stage_counts=out['stage_counts'], **FLAGS))

    try:
        progress('model_started')
        retained = (REUSE._geometry_cells(geometry, model_budget)
                    + REUSE._artifact_cells(reduction, model_budget)
                    + 2 * sum(len(r['terms']) for r in chart.get('normalized_rows', []))
                    + 16 * len(rays.get('records', [])))
        model_budget.resident_cells = retained
        model = build_model(reduction, model_budget)
        if model['rows'] != 302 or model['columns_count'] != 687:
            raise ValueError('designated licensed031 numerical302x687 model')
        out['model_stats'] = dict(rows=model['rows'], columns=model['columns_count'],
            nonzeros=model['nonzeros'], active_columns=model['active_columns'],
            row_ids=model['row_ids'], scaling=model['scaling'])
        out['stage_counts']['model'] = model_budget.counts(); progress('model_complete')
        numerical = accelerated_proposal(model, deadline=deadline,
            max_operations=PROTOCOL.ALLOCATIONS['numerical'], resident_cells=retained)
        out['numerical'] = numerical; out['stage_counts']['numerical'] = numerical['counts']
        progress('numerical_returned')
        if not numerical['complete']:
            out.update(status='UNKNOWN', reason=numerical.get('reason', 'incomplete accelerated trajectory'))
        elif numerical['selected'] is None:
            out.update(status='NONCERTIFIED', reason='complete trajectory has no eligible positive support')
        else:
            selected = numerical['selected']; support = selected['support']
            originals = [geometry['compression']['column_representatives'][model['active_columns'][j]]
                         for j in support]
            restoration = Budget(deadline, PROTOCOL.ALLOCATIONS['restoration'])
            restoration.resident_cells = retained + 2 * model['nonzeros'] + 8 * (
                model['rows'] + model['columns_count']) + 10 * len(numerical['checkpoints'])
            out['restoration_stats'] = dict(support=originals, support_size=len(originals), complete=False)
            progress('restoration_started')
            columns = REUSE._responses(geometry, restoration)
            restoration.resident_cells += sum(map(len, columns))
            rows, free, projection = OLD.decode_chart(chart, restoration)
            restoration.resident_cells += 2 * sum(map(len, rows.values())) + 4 * 851
            alpha, stats = OLD.exact_support_solve(columns, {1224: F(-1)}, 1224, originals, restoration)
            out['restoration_stats'] = stats
            certificate = OLD.certify(rows, 1224, free, projection, rays, alpha, restoration)
            data = encoded(certificate); restoration.charge(len(data))
            if len(data) > LIMITS['max_proposal_bytes']:
                raise OverflowError('bounded complete full Farkas certificate')
            out.update(status='CERTIFICATE_PROPOSED', certificate=certificate)
            progress('certificate_proposed')
    except Exception as error:
        out.update(status='NONCERTIFIED' if isinstance(error, ValueError) and restoration is not None else 'UNKNOWN',
                   reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        out['stage_counts']['model'] = model_budget.counts()
        if restoration is not None:
            out['stage_counts']['restoration'] = restoration.counts()
    if len(encoded(out)) > LIMITS['max_proposal_bytes']:
        raise OverflowError('bounded complete accelerated outcome')
    return out
