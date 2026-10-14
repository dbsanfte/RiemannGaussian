"""Warm-start coupled active-face proposals with bounded sparse PCGLS.

Face directions are unconstrained numerical iterates. Guarded interpolation
returns a nonnegative vector; all scores remain diagnostics until a full
original-coordinate Farkas identity receives independent exact admission.
"""
from fractions import Fraction as F
import math
import time

import primitive_state_chart_dual_coordinate as MODEL
import primitive_state_chart_dual_search as OLD
import primitive_state_chart_dual_reduction as REUSE
import primitive_state_chart_dual_active_protocol as PROTOCOL

Budget = OLD.Budget
build_model = MODEL.build_model
encoded = OLD.encoded
FLAGS = dict(PROTOCOL.FLAGS)
POLICY = PROTOCOL.POLICY
LIMITS = PROTOCOL.LIMITS
SCHEMA = 'primitive-state-chart-dual-active-search-v1'
NUMERICAL_SCHEMA = 'primitive-state-chart-dual-active-proposal-v1'


def numerical_work_model(m, n, nnz):
    if (any(type(v) is not int for v in (m, n, nnz))
            or not 1 <= m <= 443 or not 1 <= n <= 851 or not n <= nnz <= m * n):
        raise ValueError('bounded nonempty sparse numerical dimensions')
    setup = 12 * nnz + 64 * (m + n) + 65536
    gradient = 8 * nnz + 32 * (m + n) + 512
    face_setup = 8 * nnz + 48 * (m + n) + 1024
    cg_step = 12 * nnz + 64 * (m + n) + 1024
    commit = 8 * nnz + 48 * (m + n) + 1024
    final = 12 * nnz + 64 * (m + n) + 2048
    limit = min(128, 2 * n)
    reserve = gradient + face_setup + limit * cg_step + commit
    return dict(setup=setup, gradient=gradient, face_setup_full=face_setup,
                cg_step_full=cg_step, commit=commit, final=final,
                cg_limit_full=limit, max_faces=1000, iteration_reserve=reserve,
                minimum_attempt=setup + reserve + final)


def face_work_model(m, k, z):
    if (any(type(v) is not int for v in (m, k, z))
            or not 1 <= m <= 443 or not 1 <= k <= 851 or not k <= z <= m * k):
        raise ValueError('bounded nonempty sparse face dimensions')
    return dict(setup=8 * z + 48 * (m + k) + 1024,
                cg_step=12 * z + 64 * (m + k) + 1024,
                cg_limit=min(128, 2 * k))


def _finite(value, reason):
    if not math.isfinite(value):
        raise OverflowError(reason)
    return value


def active_set_proposal(model, initial_vector=None, *, deadline,
                        max_operations=190000000, resident_cells=0):
    budget = Budget(deadline, max_operations); budget.resident_cells = resident_cells
    start = time.monotonic()
    out = dict(schema=NUMERICAL_SCHEMA, complete=False, attempted=False,
               max_operations=max_operations, rows=model.get('rows'), columns=model.get('columns_count'),
               nonzeros=model.get('nonzeros'), work_model={}, initial_vector=None,
               metric_diagonal=None, setup_charged=False, final_charged=False,
               gradient_blocks=0, faces=[], checkpoints=[], selected=None,
               stop_reason=None, final_diagnostic=None, **FLAGS)
    metadata_cells = 0

    def global_block(kind):
        amount = out['work_model'][kind]; before = budget.operations
        try:
            budget.charge(amount)
        finally:
            if budget.operations - before == amount:
                if kind == 'gradient':
                    out['gradient_blocks'] += 1
                else:
                    out[kind + '_charged'] = True

    def face_block(face, face_work, kind):
        amount = out['work_model']['commit'] if kind == 'commit' else face_work[kind]
        before = budget.operations
        try:
            budget.charge(amount)
        finally:
            if budget.operations - before == amount:
                if kind == 'cg_step':
                    face['cg_blocks'] += 1
                else:
                    face[kind + '_charged'] = True

    def live(extra=0):
        budget.charge(0)
        cells = resident_cells + 3 * nnz + 20 * n + 12 * m + metadata_cells + extra
        budget.peak_cells = max(budget.peak_cells, cells)
        if cells > budget.max_cells:
            raise OverflowError('active-set numerical live cell cap')

    try:
        m, n, nnz = out['rows'], out['columns'], out['nonzeros']
        work = numerical_work_model(m, n, nnz); out['work_model'] = work
        if max_operations < work['minimum_attempt']:
            raise OverflowError('no complete first face and final diagnostic reservation fits')
        out['attempted'] = True; global_block('setup'); live()
        columns = model['columns']; rhs = model['rhs']
        if (type(columns) is not list or len(columns) != n or type(rhs) is not list or len(rhs) != m
                or any(type(column) is not dict for column in columns)
                or sum(map(len, columns)) != nnz
                or any(type(q) not in (int, float) or not math.isfinite(q) for q in rhs)):
            raise ValueError('complete finite sparse numerical model')
        target_norm = _finite(math.hypot(*rhs), 'nonfinite target norm')
        if target_norm <= 0:
            raise ValueError('nonzero numerical target required')
        diagonal = []; roots = []
        for column in columns:
            budget.charge(0)
            if any(type(i) is not int or not 0 <= i < m or type(q) not in (int, float)
                   or not math.isfinite(q) or q == 0 for i, q in column.items()):
                raise ValueError('nonzero finite sparse column domain')
            norm = _finite(math.hypot(*column.values()), 'nonfinite column norm')
            square = _finite(norm * norm, 'nonfinite squared column norm')
            if square <= 0:
                raise ValueError('positive squared column norm required')
            diagonal.append(square)
            roots.append(_finite(math.sqrt(square), 'nonfinite curvature root'))
        if initial_vector is None:
            x = [0.0] * n
        elif (type(initial_vector) is not list or len(initial_vector) != n
              or any(type(q) not in (int, float) or not math.isfinite(q) or q < 0 for q in initial_vector)):
            raise ValueError('complete finite nonnegative initial vector')
        else:
            x = [float(q) for q in initial_vector]
        out['initial_vector'] = list(x); out['metric_diagonal'] = list(diagonal)
        passive = {j for j, q in enumerate(x) if q > 0}
        all_indices = list(range(n)); iteration = 0; best = None

        def multiply(values, indices, *, residual=False):
            live()
            buckets = [[float(q)] if residual else [] for q in rhs]
            for j, value in zip(indices, values):
                budget.charge(0)
                if value == 0:
                    continue
                for i, q in columns[j].items():
                    product = _finite(value * q, 'nonfinite sparse matrix product')
                    buckets[i].append(-product if residual else product)
            result = []
            for terms in buckets:
                budget.charge(0)
                result.append(_finite(math.fsum(terms), 'nonfinite compensated matrix sum'))
            return result

        def transpose(residual, indices):
            result = []
            for j in indices:
                budget.charge(0)
                value = math.fsum(_finite(q * residual[i], 'nonfinite transpose product')
                                  for i, q in columns[j].items())
                result.append(_finite(value, 'nonfinite compensated correlation'))
            return result

        def normal_state(residual, active):
            s = transpose(residual, active)
            h = [_finite(q / diagonal[j], 'nonfinite preconditioned normal residual')
                 for q, j in zip(s, active)]
            gamma = _finite(math.fsum(_finite(a * b, 'nonfinite normal product')
                                      for a, b in zip(s, h)), 'nonfinite normal residual energy')
            if gamma < 0:
                raise ValueError('nonnegative normal residual energy required')
            return s, h, gamma

        def metrics(vector):
            residual = multiply(vector, all_indices, residual=True)
            norm = _finite(math.hypot(*residual), 'nonfinite checkpoint residual norm')
            relative = _finite(norm / target_norm, 'nonfinite checkpoint relative residual')
            return residual, norm, relative

        def checkpoint(vector, index, norm, relative):
            nonlocal metadata_cells, best
            support = [j for j, value in enumerate(vector) if value > 0]
            live(8)
            out['checkpoints'].append(dict(iteration=index, residual_norm=norm,
                relative_residual=relative, support_size=len(support), cumulative_operations=budget.operations))
            metadata_cells += 8
            if 1 <= len(support) <= POLICY['max_support']:
                score = (relative, len(support), index)
                if best is None or score < best:
                    best = score
                    out['selected'] = dict(iteration=index, scaled_vector=list(vector),
                                          support=support, relative_residual=relative)

        _, residual_norm, relative = metrics(x)
        checkpoint(x, 0, residual_norm, relative)
        if residual_norm == 0:
            out['stop_reason'] = 'zero_reported_residual'

        while out['stop_reason'] is None:
            budget.charge(0)
            if max_operations - budget.operations < work['iteration_reserve'] + work['final']:
                out['stop_reason'] = 'work_boundary'; break
            global_block('gradient')
            residual = multiply(x, all_indices, residual=True); correlations = transpose(residual, all_indices)
            entered = None; entry_score = None
            if not out['faces'] and passive:
                mode = 'initial_face'
            elif out['faces'] and out['faces'][-1]['damped'] and passive:
                mode = 'refine_face'
            else:
                mode = 'enter_column'
                for j in range(n):
                    budget.charge(0)
                    if j in passive:
                        continue
                    score = _finite(correlations[j] / roots[j], 'nonfinite inactive entry score')
                    if score > 0 and (entry_score is None or score > entry_score):
                        entered = j; entry_score = score
                if entered is None:
                    out['stop_reason'] = 'no_positive_inactive_correlation'; break
                passive.add(entered)
            active = sorted(passive); face_nnz = sum(len(columns[j]) for j in active)
            face_work = face_work_model(m, len(active), face_nnz)
            face = dict(iteration=iteration + 1, mode=mode, entered=entered, entry_score=entry_score,
                active=active, nonzeros=face_nnz, cg_limit=face_work['cg_limit'], setup_charged=False,
                cg_blocks=0, cg_steps_completed=0, cg_stop=None, commit_charged=False, complete=False,
                damped=None, step_fraction=None, boundary_hits=None, surviving_support=None,
                cumulative_operations=None)
            live(len(active) + 24); out['faces'].append(face); metadata_cells += len(active) + 24
            face_block(face, face_work, 'setup')
            z = [x[j] for j in active]; residual = multiply(z, active, residual=True)
            _, h, gamma = normal_state(residual, active); direction = list(h)
            if gamma == 0:
                face['cg_stop'] = 'zero_normal_residual'
            else:
                for _ in range(face_work['cg_limit']):
                    face_block(face, face_work, 'cg_step')
                    q = multiply(direction, active)
                    q_norm = _finite(math.hypot(*q), 'nonfinite Krylov curvature norm')
                    curvature = _finite(q_norm * q_norm, 'nonfinite Krylov squared curvature')
                    if curvature == 0:
                        face['cg_stop'] = 'zero_curvature'; break
                    fraction = _finite(gamma / curvature, 'nonfinite Krylov step ratio')
                    next_z = []
                    for value, p in zip(z, direction):
                        budget.charge(0)
                        product = _finite(fraction * p, 'nonfinite Krylov step product')
                        next_z.append(_finite(value + product, 'nonfinite unconstrained face coordinate'))
                    z = next_z; residual = multiply(z, active, residual=True)
                    _, h, next_gamma = normal_state(residual, active)
                    face['cg_steps_completed'] += 1
                    if next_gamma == 0:
                        face['cg_stop'] = 'zero_normal_residual'; break
                    beta = _finite(next_gamma / gamma, 'nonfinite Krylov direction ratio')
                    next_direction = []
                    for normal, p in zip(h, direction):
                        budget.charge(0)
                        product = _finite(beta * p, 'nonfinite Krylov direction product')
                        next_direction.append(_finite(normal + product, 'nonfinite Krylov direction'))
                    direction = next_direction; gamma = next_gamma
                if face['cg_stop'] is None:
                    face['cg_stop'] = 'iteration_limit'

            face_block(face, face_work, 'commit')
            new_x = [0.0] * n
            if all(value > 0 for value in z):
                damped = False; alpha = 1.0; boundary_hits = []
                for j, value in zip(active, z):
                    new_x[j] = value
            else:
                damped = True; ratios = []
                for j, value in zip(active, z):
                    budget.charge(0)
                    if value > 0:
                        continue
                    denominator = _finite(x[j] - value, 'nonfinite boundary denominator')
                    ratio = 0.0 if x[j] == 0 and value == 0 else _finite(
                        x[j] / denominator, 'nonfinite boundary ratio')
                    if not 0 <= ratio <= 1:
                        raise ValueError('unit interval boundary ratio required')
                    ratios.append((j, ratio))
                alpha = min(ratio for _, ratio in ratios)
                boundary_hits = [j for j, ratio in ratios if ratio == alpha]
                for j, value in zip(active, z):
                    budget.charge(0)
                    difference = _finite(value - x[j], 'nonfinite boundary direction')
                    product = _finite(alpha * difference, 'nonfinite boundary interpolation product')
                    candidate = _finite(x[j] + product, 'nonfinite boundary coordinate before projection')
                    new_x[j] = max(0.0, candidate)
                for j in boundary_hits:
                    new_x[j] = 0.0
            survivors = [j for j, value in enumerate(new_x) if value > 0]
            _, residual_norm, relative = metrics(new_x)
            live(len(boundary_hits) + len(survivors) + 8)
            # Append only a fully computed nonnegative state and checkpoint.
            checkpoint(new_x, iteration + 1, residual_norm, relative)
            face.update(complete=True, damped=damped, step_fraction=alpha, boundary_hits=boundary_hits,
                        surviving_support=survivors, cumulative_operations=budget.operations)
            metadata_cells += len(boundary_hits) + len(survivors)
            x = new_x; passive = set(survivors); iteration += 1
            if residual_norm == 0:
                out['stop_reason'] = 'zero_reported_residual'
            elif face['cg_stop'] == 'zero_curvature':
                out['stop_reason'] = 'krylov_breakdown'
            elif iteration == work['max_faces']:
                out['stop_reason'] = 'face_limit'

        global_block('final')
        residual, residual_norm, relative = metrics(x)
        correlations = transpose(residual, all_indices); mapping = []
        for j in range(n):
            budget.charge(0)
            ratio = _finite(correlations[j] / diagonal[j], 'nonfinite final mapping ratio')
            candidate = _finite(x[j] + ratio, 'nonfinite final coordinate before projection')
            projected = max(0.0, candidate)
            difference = _finite(x[j] - projected, 'nonfinite final mapping difference')
            mapping.append(_finite(roots[j] * difference, 'nonfinite metric mapping product'))
        mapping_norm = _finite(math.hypot(*mapping), 'nonfinite projected-gradient diagnostic')
        diagnostic = dict(iteration=iteration, residual_norm=residual_norm, relative_residual=relative,
            projected_gradient_norm=mapping_norm, mapping_metric='diagonal column curvature, unit step')
        budget.charge(0); out['final_diagnostic'] = diagnostic; out['complete'] = True
    except Exception as error:
        out.update(selected=None, reason=str(error) or type(error).__name__,
                   resource_failure=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        out['counts'] = budget.counts(); out['elapsed_seconds'] = time.monotonic() - start
    return out


def _seed_vector(seed, n, budget):
    if (type(seed) is not dict or seed.get('schema') != MODEL.SCHEMA
            or type(seed.get('numerical')) is not dict
            or seed['numerical'].get('schema') != MODEL.NUMERICAL_SCHEMA
            or seed['numerical'].get('complete') is not True
            or type(seed['numerical'].get('selected')) is not dict):
        raise ValueError('complete designated032 selected vector seed')
    vector = seed['numerical']['selected'].get('scaled_vector')
    budget.charge(n)
    if (type(vector) is not list or len(vector) != n
            or any(type(q) not in (int, float) or not math.isfinite(q) or q < 0 for q in vector)):
        raise ValueError('complete finite nonnegative032 seed vector')
    return list(vector)


def search(chart, rays, geometry, reduction, seed, *, deadline, checkpoint=None):
    out = dict(schema=SCHEMA, status='UNKNOWN', route='active_set', numerical=None,
               model_stats={}, certificate=None, stage_counts={}, policy=POLICY, limits=LIMITS, **FLAGS)
    model_budget = Budget(deadline, PROTOCOL.ALLOCATIONS['model']); restoration = None

    def progress(phase):
        if checkpoint:
            checkpoint(dict(phase=phase, status=out['status'], stage_counts=out['stage_counts'], **FLAGS))

    try:
        progress('model_started')
        seed_bytes = len(encoded(seed)); model_budget.charge(seed_bytes // 64 + 1)
        retained = (REUSE._geometry_cells(geometry, model_budget)
                    + REUSE._artifact_cells(reduction, model_budget)
                    + 2 * sum(len(r['terms']) for r in chart.get('normalized_rows', []))
                    + 16 * len(rays.get('records', [])) + seed_bytes // 8 + 1)
        model_budget.resident_cells = retained
        model = build_model(reduction, model_budget)
        if model['rows'] != 302 or model['columns_count'] != 687:
            raise ValueError('designated licensed031 numerical302x687 model')
        initial = _seed_vector(seed, model['columns_count'], model_budget)
        model_budget.cells(2 * model['nonzeros'] + 8 * (model['rows'] + model['columns_count']))
        out['model_stats'] = dict(rows=model['rows'], columns=model['columns_count'],
            nonzeros=model['nonzeros'], active_columns=model['active_columns'],
            row_ids=model['row_ids'], scaling=model['scaling'])
        out['stage_counts']['model'] = model_budget.counts(); progress('model_complete')
        numerical = active_set_proposal(model, initial, deadline=deadline,
            max_operations=PROTOCOL.ALLOCATIONS['numerical'], resident_cells=retained)
        out['numerical'] = numerical; out['stage_counts']['numerical'] = numerical['counts']
        progress('numerical_returned')
        if not numerical['complete']:
            out.update(status='UNKNOWN', reason=numerical.get('reason', 'incomplete active-face trajectory'))
        elif numerical['selected'] is None:
            out.update(status='NONCERTIFIED', reason='complete trajectory has no eligible positive support')
        else:
            selected = numerical['selected']; support = selected['support']
            originals = [geometry['compression']['column_representatives'][model['active_columns'][j]]
                         for j in support]
            restoration = Budget(deadline, PROTOCOL.ALLOCATIONS['restoration'])
            face_cells = sum(24 + len(f['active']) + len(f['boundary_hits'] or [])
                             + len(f['surviving_support'] or []) for f in numerical['faces'])
            restoration.resident_cells = retained + 2 * model['nonzeros'] + 8 * (
                model['rows'] + model['columns_count']) + face_cells + 8 * len(numerical['checkpoints'])
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
        raise OverflowError('bounded complete active-face outcome')
    return out
