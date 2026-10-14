"""One bounded sparse coordinate proposal and one full exact restoration.

The numerical trajectory changes a nonnegative vector using sparse column
updates. Its residual scores are diagnostics; only a separately checked full
old029 Farkas identity can prove finite-template infeasibility.
"""
from fractions import Fraction as F
import math
import time

import primitive_state_chart_dual_search as OLD
import primitive_state_chart_dual_reduction as REUSE
import primitive_state_chart_dual_coordinate_protocol as PROTOCOL

Budget = OLD.Budget
encoded = OLD.encoded
FLAGS = dict(PROTOCOL.FLAGS)
POLICY = PROTOCOL.POLICY
LIMITS = PROTOCOL.LIMITS
SCHEMA = 'primitive-state-chart-dual-coordinate-search-v1'
NUMERICAL_SCHEMA = 'primitive-state-chart-dual-coordinate-proposal-v1'


def build_model(reduction, budget):
    """Decode retained original columns and scale their equations exactly."""
    if (reduction.get('schema') != REUSE.REDUCTION_SCHEMA
            or reduction.get('complete') is not True or reduction.get('status') != 'REDUCED'):
        raise ValueError('complete consistent licensed031 reduction')
    active = reduction.get('active_columns'); records = reduction.get('final_rows')
    initial_n = reduction.get('input_columns')
    if (type(initial_n) is not int or not 1 <= initial_n <= 851
            or type(active) is not list or not active or active != sorted(set(active))
            or any(type(j) is not int or not 0 <= j < initial_n for j in active)
            or type(records) is not list or not 1 <= len(records) <= 443):
        raise ValueError('bounded retained reduction dimensions')
    columns = [{} for _ in active]; position = {j: k for k, j in enumerate(active)}
    target = {}; row_ids = []; last = -1; cells = 0
    for i, record in enumerate(records):
        budget.charge()
        row_id = record.get('row_id')
        if type(row_id) is not int or not last < row_id < reduction.get('input_rows', 0):
            raise ValueError('ordered stable original row IDs')
        last = row_id; row_ids.append(row_id)
        row = REUSE._sparse(record['terms'], position, budget)
        for j, q in row.items():
            budget.charge(); columns[position[j]][i] = q; cells += 1
        rhs = budget.q(record['rhs'])
        if rhs:
            target[i] = rhs
        budget.cells(cells + len(row) + len(target) + 4 * len(active))
    m = len(records); n = len(active)
    budget.cells(4 * cells + 8 * n + 8 * m)
    keys, exact_columns, exact_rhs, row_scales, column_scales = OLD.scaled_model(
        dict(width=m - 1, free=list(range(m - 1)), columns=columns, target=target), budget)
    if keys != list(range(m)):
        raise ValueError('complete row-position scaling domain')
    floating = []; nnz = 0
    for column in exact_columns:
        converted = {}
        for i, q in sorted(column.items()):
            budget.charge(); converted[i] = OLD.finite_float(q)
        floating.append(converted); nnz += len(converted)
        budget.cells(2 * cells + nnz + 8 * (m + n))
    rhs = []
    for q in exact_rhs:
        budget.charge(); rhs.append(OLD.finite_float(q))
    scaling = dict(row_scale_min=str(min(row_scales.values())),
                   row_scale_max=str(max(row_scales.values())),
                   column_scale_min=str(min(column_scales)),
                   column_scale_max=str(max(column_scales)),
                   positive_exact=True, finite_nonunderflowing_conversion=True)
    return dict(columns=floating, rhs=rhs, rows=m, columns_count=n, nonzeros=nnz,
                active_columns=list(active), row_ids=row_ids, scaling=scaling)


def numerical_reservation(m, n, nnz, available):
    """Largest common sweep allowance using dimensions and sparsity only."""
    if (any(type(v) is not int for v in (m, n, nnz, available))
            or not 1 <= m <= 443 or not 1 <= n <= 851
            or not 0 <= nnz <= m * n or available < 0):
        raise ValueError('bounded numerical reservation dimensions')
    setup = 8 * nnz + 32 * (m + n) + 65536
    sweep = 8 * nnz + 32 * n + 2 * m + 64
    refresh = 8 * nnz + 16 * (m + n) + 256
    phases = 17
    def total(s):
        return setup + phases * (s * sweep + ((s + 15) // 16 + 1) * refresh)
    low = 0; high = POLICY['max_sweeps_per_phase']
    while low < high:
        middle = (low + high + 1) // 2
        if total(middle) <= available:
            low = middle
        else:
            high = middle - 1
    return dict(setup=setup, sweep=sweep, refresh=refresh, phases=phases,
                sweeps_per_phase=low, total=total(low))


def _finite(value, reason):
    if not math.isfinite(value):
        raise OverflowError(reason)
    return value


def coordinate_proposal(model, *, deadline, max_operations=190000000, resident_cells=0):
    budget = Budget(deadline, max_operations); budget.resident_cells = resident_cells
    start = time.monotonic()
    out = dict(schema=NUMERICAL_SCHEMA, complete=False, attempted=False, reservation={},
               max_operations=max_operations, rows=model.get('rows'), columns=model.get('columns_count'),
               nonzeros=model.get('nonzeros'), penalty_reference=None, checkpoints=[], selected=None,
               sweeps_charged=0, refreshes_charged=0, setup_charged=False,
               coordinate_visits=0, nonzero_updates=0, **FLAGS)

    def block(kind):
        amount = out['reservation'][kind]; before = budget.operations
        try:
            budget.charge(amount)
        finally:
            # Deadline exceptions happen after charging, unlike cap failures.
            if budget.operations - before == amount:
                if kind == 'setup':
                    out['setup_charged'] = True
                else:
                    out[{'sweep': 'sweeps_charged', 'refresh': 'refreshes_charged'}[kind]] += 1

    def live(cells):
        budget.charge(0)
        total = resident_cells + cells
        budget.peak_cells = max(budget.peak_cells, total)
        if total > budget.max_cells:
            raise OverflowError('numerical live cell cap')

    try:
        m, n, nnz = out['rows'], out['columns'], out['nonzeros']
        reserve = numerical_reservation(m, n, nnz, max_operations)
        out['reservation'] = reserve
        if reserve['sweeps_per_phase'] < 1:
            raise OverflowError('no complete seventeen-phase numerical reservation fits')
        out['attempted'] = True; block('setup')
        columns = model['columns']; rhs = model['rhs']
        if type(columns) is not list or len(columns) != n or type(rhs) is not list or len(rhs) != m:
            raise ValueError('complete sparse numerical model')
        if (any(type(q) not in (int, float) or not math.isfinite(q) for q in rhs)
                or any(type(col) is not dict for col in columns)
                or sum(map(len, columns)) != nnz):
            raise ValueError('finite numerical target and declared sparsity')
        live(3 * nnz + 12 * n + 9 * m + 17 * 8)
        target_norm = _finite(math.hypot(*rhs), 'nonfinite target norm')
        if target_norm <= 0:
            raise ValueError('nonzero numerical target required')
        norms = []; reference = 0.0
        for column in columns:
            budget.charge(0)
            if any(type(i) is not int or not 0 <= i < m or type(q) not in (int, float)
                   or not math.isfinite(q) or q == 0 for i, q in column.items()):
                raise ValueError('nonzero finite sparse column domain')
            norm = _finite(math.hypot(*column.values()), 'nonfinite column norm')
            square = _finite(norm * norm, 'nonfinite squared column norm')
            if square <= 0:
                raise ValueError('positive squared numerical column norm required')
            norms.append(square)
            score = _finite(math.fsum(q * rhs[i] for i, q in column.items()), 'nonfinite penalty score')
            reference = max(reference, score)
        out['penalty_reference'] = reference
        x = [0.0] * n; residual = [-float(q) for q in rhs]
        penalties = [math.ldexp(reference, -e) for e in POLICY['penalty_exponents']] + [0.0]
        best = None

        def refresh():
            block('refresh')
            # The declared refresh proxy includes these temporary sparse
            # product buckets and compensated row sums.
            live(3 * nnz + 12 * n + 9 * m + 17 * 8)
            contributions = [[-float(q)] for q in rhs]
            for j, column in enumerate(columns):
                budget.charge(0)
                if x[j] == 0:
                    continue
                for i, q in column.items():
                    product = _finite(x[j] * q, 'nonfinite refreshed product')
                    contributions[i].append(product)
            fresh = []
            for terms in contributions:
                budget.charge(0)
                fresh.append(_finite(math.fsum(terms), 'nonfinite refreshed residual'))
            return fresh

        for phase, penalty in enumerate(penalties):
            completed_sweeps = 0
            for _ in range(reserve['sweeps_per_phase']):
                block('sweep'); changed = False
                for j, column in enumerate(columns):
                    budget.charge(0); out['coordinate_visits'] += 1
                    dot = _finite(math.fsum(q * residual[i] for i, q in column.items()),
                                  'nonfinite coordinate dot product')
                    gradient = _finite(dot + penalty, 'nonfinite coordinate gradient')
                    candidate = _finite(x[j] - gradient / norms[j], 'nonfinite coordinate candidate')
                    new = max(0.0, candidate)
                    delta = _finite(new - x[j], 'nonfinite coordinate delta')
                    if new == x[j]:
                        continue
                    changed = True; x[j] = new
                    for i, q in column.items():
                        out['nonzero_updates'] += 1
                        product = _finite(delta * q, 'nonfinite coordinate residual product')
                        residual[i] = _finite(residual[i] + product, 'nonfinite coordinate residual update')
                completed_sweeps += 1
                if completed_sweeps % POLICY['refresh_interval_sweeps'] == 0:
                    residual = refresh()
                if not changed:
                    break
            residual = refresh()
            residual_norm = _finite(math.hypot(*residual), 'nonfinite residual norm')
            relative = _finite(residual_norm / target_norm, 'nonfinite relative residual')
            support = [j for j, q in enumerate(x) if q > 0]
            out['checkpoints'].append(dict(phase=phase, penalty=penalty,
                completed_sweeps=completed_sweeps, residual_norm=residual_norm,
                relative_residual=relative, support_size=len(support)))
            if 1 <= len(support) <= POLICY['max_support']:
                score = (relative, len(support), phase)
                if best is None or score < best:
                    best = score
                    out['selected'] = dict(phase=phase, scaled_vector=list(x),
                                          support=support, relative_residual=relative)
        budget.charge(0); out['complete'] = True
    except Exception as error:
        out.update(selected=None, reason=str(error) or type(error).__name__,
                   resource_failure=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        out['counts'] = budget.counts(); out['elapsed_seconds'] = time.monotonic() - start
    return out


def search(chart, rays, geometry, reduction, *, deadline, checkpoint=None):
    out = dict(schema=SCHEMA, status='UNKNOWN', route='coordinate_descent', numerical=None,
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
        numerical = coordinate_proposal(model, deadline=deadline,
            max_operations=PROTOCOL.ALLOCATIONS['numerical'], resident_cells=retained)
        out['numerical'] = numerical; out['stage_counts']['numerical'] = numerical['counts']
        progress('numerical_returned')
        if not numerical['complete']:
            out.update(status='UNKNOWN', reason=numerical.get('reason', 'incomplete numerical trajectory'))
        elif numerical['selected'] is None:
            out.update(status='NONCERTIFIED', reason='complete trajectory has no eligible positive support')
        else:
            selected = numerical['selected']; support = selected['support']
            originals = [geometry['compression']['column_representatives'][model['active_columns'][j]]
                         for j in support]
            restoration = Budget(deadline, PROTOCOL.ALLOCATIONS['restoration'])
            restoration.resident_cells = retained + 2 * model['nonzeros'] + 8 * (
                model['rows'] + model['columns_count']) + 8 * len(numerical['checkpoints'])
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
        raise OverflowError('bounded complete coordinate outcome')
    return out
