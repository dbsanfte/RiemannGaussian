"""Bounded exact equivalence reductions and one fixed-generator separator search.

Every deletion has a nonnegative zero-extension proof. Forward elimination
changes equations only; it never substitutes unrestricted pivot coordinates
for the original nonnegative variables. The saved trace is independently
replayable before a native proposal is considered.
"""
from fractions import Fraction as F
import math

import primitive_state_chart_dual_geometry_search as NATIVE
import primitive_state_chart_dual_search as OLD
import primitive_state_chart_dual_reduction_protocol as PROTOCOL

Budget = OLD.Budget
encoded = OLD.encoded
FLAGS = dict(PROTOCOL.FLAGS)
POLICY = PROTOCOL.POLICY
LIMITS = PROTOCOL.LIMITS
SCHEMA = 'primitive-state-chart-dual-reduction-search-v1'
REDUCTION_SCHEMA = 'primitive-state-chart-dual-reduction-v1'


def _sparse(terms, allowed, budget):
    if type(terms) is not list or len(terms) > len(allowed):
        raise ValueError('bounded sparse coefficient list')
    row = {}; previous = -1
    for term in terms:
        budget.charge()
        if type(term) is not list or len(term) != 2:
            raise ValueError('explicit sparse coefficient pair')
        j, value = term
        if type(j) is not int or j not in allowed or j <= previous:
            raise ValueError('unique ascending coefficient domain')
        q = budget.q(value)
        if not q:
            raise ValueError('sparse zero coefficients absent')
        row[j] = q; previous = j
    return row


def input_model(geometry, budget):
    """Decode the saved030 compression without response reconstruction."""
    if (geometry.get('schema') != NATIVE.GEOMETRY_SCHEMA
            or geometry.get('complete') is not True):
        raise ValueError('complete saved030 geometry premise')
    compression = geometry['compression']
    representatives = compression['column_representatives']
    row_keys = compression['row_representatives']
    if (type(representatives) is not list or len(representatives) > 851
            or representatives != sorted(set(representatives))
            or any(type(j) is not int or not 0 <= j < 851 for j in representatives)
            or type(row_keys) is not list or len(row_keys) > 443
            or row_keys != sorted(set(row_keys))
            or any(type(i) is not int or not 0 <= i <= 1224 for i in row_keys)):
        raise ValueError('ordered saved030 representative domains')
    columns = compression['compressed_columns']; n = len(representatives)
    if type(columns) is not list or len(columns) != n:
        raise ValueError('complete compressed columns')
    position = {i: r for r, i in enumerate(row_keys)}
    rows = {r: {} for r in range(len(row_keys))}; cells = 0
    for j, terms in enumerate(columns):
        column = _sparse(terms, position, budget)
        for i, q in column.items():
            budget.charge(); rows[position[i]][j] = q; cells += 1
        budget.cells(cells + len(column) + len(row_keys) + n)
    rhs = _sparse(compression['compressed_rhs'], position, budget)
    for i, q in rhs.items():
        budget.charge(); rows[position[i]][n] = q; cells += 1
    budget.cells(cells + len(rhs) + len(row_keys) + n)
    return rows, n


def _geometry_cells(geometry, budget):
    """Account saved rational text and index maps retained throughout search."""
    compression = geometry.get('compression', {}); cells = 0
    for key in ('forms', 'responses'):
        for record in geometry.get(key, []):
            budget.charge(); cells += 2 * len(record.get('terms', [])) + 3
    for column in compression.get('compressed_columns', []):
        budget.charge(); cells += 2 * len(column)
    for key in ('column_map', 'row_map', 'column_representatives', 'row_representatives', 'row_keys'):
        budget.charge(); cells += 4 * len(compression.get(key, []))
    cells += 2 * len(compression.get('compressed_rhs', []))
    return cells


def _artifact_cells(artifact, budget):
    cells = 4 * sum(len(artifact[key]) for key in (
        'active_columns', 'forced_zero_columns', 'discarded_zero_target_columns'))
    for step in artifact['steps']:
        budget.charge(); cells += 5 + sum(len(v) for v in step.values() if type(v) is list)
    for row in artifact['final_rows']:
        budget.charge(); cells += 2 * len(row['terms']) + 3
    return cells


def reduce_system(rows, column_count, budget):
    """Reduce Ax=b, x>=0 with a complete finite equivalence trace.

    Markowitz counts refer to coefficient support, excluding the RHS. A
    forward pass excludes already pivoted rows and columns; pivot equations
    remain in the system and retain their original nonnegative variables.
    """
    if (type(column_count) is not int or not 0 <= column_count <= 851
            or type(rows) is not dict or len(rows) > 443
            or set(rows) != set(range(len(rows)))
            or any(type(i) is not int for i in rows)):
        raise ValueError('bounded initial compressed system with positional row IDs')
    if any(type(row) is not dict for row in rows.values()):
        raise ValueError('sparse augmented equation dictionary')
    budget.charge(len(rows)); source = {}; initial_cells = sum(len(row) for row in rows.values())
    for i, row in sorted(rows.items()):
        if type(row) is not dict:
            raise ValueError('sparse augmented equation dictionary')
        clean = {}
        for j, value in row.items():
            budget.charge()
            if type(j) is not int or not 0 <= j <= column_count:
                raise ValueError('initial column domain including RHS')
            q = budget.q(value)
            if not q:
                raise ValueError('sparse zero coefficients absent')
            clean[j] = q
        source[i] = clean
        budget.cells(initial_cells + sum(map(len, source.values())))
    active = set(range(column_count)); forced = set(); discarded = set()
    steps = []; retained_bytes = 65536; trace_cells = 0

    def live(extra=0):
        budget.charge(len(source))
        budget.cells(initial_cells + sum(map(len, source.values()))
                     + trace_cells + 4 * (len(source) + len(active)) + extra)

    def save_step(step):
        nonlocal retained_bytes, trace_cells
        payload = encoded(step); budget.charge(len(payload) // 64 + 1)
        retained_bytes += len(payload) + 1
        if retained_bytes > LIMITS['max_reduction_bytes']:
            raise OverflowError('complete reduction trace byte cap')
        trace_cells += 5 + sum(len(v) for v in step.values() if type(v) is list)
        steps.append(step); live()

    def drop_zero_rows():
        budget.charge(len(source))
        zero = sorted(i for i, row in source.items() if not row)
        if zero:
            save_step(dict(kind='drop_zero_rows', rows=zero))
            for i in zero:
                del source[i]

    def propagate():
        # Revisit affected equations until the sign inference is closed.
        while True:
            drop_zero_rows(); selected = None
            for i, row in sorted(source.items()):
                budget.charge(len(row) + 1)
                if column_count in row:
                    continue
                positive = any(q > 0 for q in row.values())
                negative = any(q < 0 for q in row.values())
                if row and positive != negative:
                    selected = (i, sorted(row)); break
            if selected is None:
                break
            i, columns = selected
            save_step(dict(kind='force_zero', row_id=i, columns=columns))
            for row in source.values():
                budget.charge(len(columns))
                for j in columns:
                    row.pop(j, None)
            active.difference_update(columns); forced.update(columns); live()

    def remove_components():
        # Bipartite incidence components; RHS entries are targets, not edges.
        incidence = {j: [] for j in active}
        for i, row in source.items():
            for j in row:
                budget.charge()
                if j != column_count:
                    incidence[j].append(i)
        unseen = set(active); zero_columns = []; zero_rows = []
        while unseen:
            seed = min(unseen); unseen.remove(seed)
            pending = [seed]; component_columns = {seed}; component_rows = set()
            has_target = False
            while pending:
                j = pending.pop(); budget.charge()
                for i in incidence[j]:
                    budget.charge()
                    if i in component_rows:
                        continue
                    component_rows.add(i); row = source[i]
                    has_target = has_target or column_count in row
                    for k in row:
                        budget.charge()
                        if k != column_count and k not in component_columns:
                            component_columns.add(k); unseen.discard(k); pending.append(k)
            if not has_target:
                zero_columns.extend(component_columns); zero_rows.extend(component_rows)
            live(sum(map(len, incidence.values())) + len(component_columns) + len(component_rows))
        if zero_columns:
            columns = sorted(zero_columns); removed_rows = sorted(zero_rows)
            save_step(dict(kind='discard_homogeneous_components', columns=columns, rows=removed_rows))
            active.difference_update(columns); discarded.update(columns)
            for i in removed_rows:
                del source[i]
        drop_zero_rows(); live()

    def forward_eliminate():
        unused_rows = set(source); unused_columns = set(active)
        while unused_rows and unused_columns:
            degrees = {}; row_columns = {}
            for i in sorted(unused_rows):
                entries = [j for j in source[i] if j in unused_columns]
                budget.charge(len(source[i]) + 1); row_columns[i] = entries
                for j in entries:
                    degrees[j] = degrees.get(j, 0) + 1; budget.charge()
            choice = None
            for i, entries in row_columns.items():
                size = len(entries)
                for j in entries:
                    budget.charge()
                    score = ((size - 1) * (degrees[j] - 1), size, degrees[j], j, i)
                    if choice is None or score < choice:
                        choice = score
            if choice is None:
                break
            _, _, _, column, row_id = choice
            pivot = source[row_id]; factor = pivot[column]
            eliminate = sorted(i for i in unused_rows if i != row_id and column in source[i])
            budget.charge(len(unused_rows)); save_step(dict(kind='pivot', row_id=row_id,
                                                          column=column, eliminate=eliminate))
            normalized = {j: budget.div(q, factor) for j, q in pivot.items()}
            live(len(normalized) + sum(map(len, row_columns.values())) + len(degrees))
            source[row_id] = normalized
            for i in eliminate:
                row = source[i]; multiplier = row[column]
                for j, q in normalized.items():
                    value = budget.add(row.get(j, F(0)), -budget.mul(multiplier, q))
                    if value:
                        row[j] = value
                    else:
                        row.pop(j, None)
                live(len(normalized))
            unused_rows.remove(row_id); unused_columns.remove(column)

    rounds = 0; fixed_point = False
    for _ in range(POLICY['max_elimination_rounds']):
        before = set(active); rounds += 1
        propagate(); remove_components(); forward_eliminate(); propagate(); remove_components()
        contradiction = next((i for i in sorted(source)
                              if set(source[i]) == {column_count}), None)
        if contradiction is not None:
            break
        if active == before:
            fixed_point = True; break
    contradiction = next((i for i in sorted(source) if set(source[i]) == {column_count}), None)
    final = []; final_cells = 0
    for i, row in sorted(source.items()):
        budget.charge(len(row) + 1)
        final.append(dict(row_id=i, terms=[[j, str(q)] for j, q in sorted(row.items())
                                          if j != column_count],
                          rhs=str(row.get(column_count, F(0)))))
        final_cells += 2 * len(row) + 2; live(final_cells)
    artifact = dict(schema=REDUCTION_SCHEMA, complete=True, input_rows=len(rows),
                    input_columns=column_count, steps=steps, final_rows=final,
                    active_columns=sorted(active), forced_zero_columns=sorted(forced),
                    discarded_zero_target_columns=sorted(discarded), rounds=rounds,
                    fixed_point=fixed_point,
                    status='RESTRICTED_SYSTEM_INCONSISTENT' if contradiction is not None else 'REDUCED',
                    contradiction_row=contradiction, policy=POLICY, **FLAGS)
    payload = encoded(artifact); budget.charge(len(payload) // 64 + 1)
    if len(payload) > LIMITS['max_reduction_bytes']:
        raise OverflowError('complete reduction artifact byte cap')
    return artifact


def _responses(geometry, budget):
    records = geometry.get('responses')
    if type(records) is not list or len(records) != 851:
        raise ValueError('complete saved851 original responses')
    allowed = set(geometry['free_indices']) | {1224}; columns = []; cells = 0
    for j, record in enumerate(records):
        if type(record) is not dict or record.get('ray_index') != j:
            raise ValueError('ordered original851 response indices')
        column = _sparse(record['terms'], allowed, budget)
        columns.append(column); cells += len(column); budget.cells(cells + 2 * 851)
    return columns


def search(chart, rays, geometry, *, deadline, checkpoint=None, save_reduction=None):
    out = dict(schema=SCHEMA, status='UNKNOWN', reduction_complete=False, route=None,
               certificate=None, native=None, reduction_stats={}, policy=POLICY,
               limits=LIMITS, stage_counts={}, **FLAGS)
    reduction_budget = Budget(deadline, PROTOCOL.ALLOCATIONS['reduction'])
    restoration = None

    def progress(phase):
        if checkpoint:
            checkpoint(dict(phase=phase, status=out['status'],
                            reduction_complete=out['reduction_complete'],
                            stage_counts=out['stage_counts'], **FLAGS))

    try:
        progress('reduction_started')
        geometry_cells = _geometry_cells(geometry, reduction_budget)
        reduction_budget.resident_cells = geometry_cells
        rows, n = input_model(geometry, reduction_budget)
        if len(rows) != 317 or n != 695:
            raise ValueError('designated saved030 compressed317x695 input')
        reduction = reduce_system(rows, n, reduction_budget)
        out['stage_counts']['reduction'] = reduction_budget.counts()
        if save_reduction is not None:
            save_reduction(reduction)
        out.update(reduction_complete=True, reduction_stats=dict(
            input_rows=len(rows), input_columns=n, reduced_rows=len(reduction['final_rows']),
            reduced_columns=len(reduction['active_columns']), steps=len(reduction['steps']),
            rounds=reduction['rounds'], fixed_point=reduction['fixed_point'],
            forced_zero_columns=len(reduction['forced_zero_columns']),
            discarded_zero_target_columns=len(reduction['discarded_zero_target_columns']),
            restricted_system_inconsistent=reduction['contradiction_row'] is not None))
        progress('reduction_complete')
        if reduction['contradiction_row'] is not None:
            out.update(status='NONCERTIFIED', reason='restricted fixed-generator separator equations inconsistent')
        elif not reduction['active_columns'] or not reduction['final_rows']:
            out.update(status='NONCERTIFIED', reason='empty reduced separator system')
        else:
            out['route'] = 'reduced_lp'
            retained_cells = (geometry_cells + sum(map(len, rows.values()))
                              + _artifact_cells(reduction, reduction_budget))
            reduction_budget.resident_cells = retained_cells
            active = reduction['active_columns']; position = {j: k for k, j in enumerate(active)}
            compressed = [{} for _ in active]; rhs = {}; row_keys = []
            for record in reduction['final_rows']:
                i = record['row_id']; row_keys.append(i)
                for j, q in record['terms']:
                    reduction_budget.charge(); compressed[position[j]][i] = reduction_budget.q(q)
                q = reduction_budget.q(record['rhs'])
                if q:
                    rhs[i] = q
            reduction_budget.cells(sum(map(len, compressed)) + len(rhs) + len(active))
            retained_cells += sum(map(len, compressed)) + len(rhs) + len(active) + len(row_keys)
            native = NATIVE.native_proposal(compressed, rhs, row_keys, deadline=deadline,
                                           max_operations=PROTOCOL.ALLOCATIONS['native'],
                                           resident_cells=retained_cells)
            out['native'] = native; out['stage_counts']['native'] = native['counts']
            progress('native_returned')
            vector = native.get('scaled_vector')
            if not native.get('success') or vector is None:
                out.update(status='UNKNOWN' if native.get('resource_failure') or native.get('status') == 1
                           else 'NONCERTIFIED', reason=native.get('resource_failure') or 'native LP not successful')
            elif (type(vector) is not list or len(vector) != len(active)
                  or any(type(v) not in (int, float) or not math.isfinite(v) for v in vector)):
                out.update(status='NONCERTIFIED', reason='complete finite native vector required')
            else:
                support = [j for j, v in enumerate(vector) if v > 0]
                out['native_support'] = support
                originals = [geometry['compression']['column_representatives'][active[j]] for j in support]
                if len(support) > POLICY['max_support']:
                    out.update(status='NONCERTIFIED', reason='all-positive native support exceeds443')
                else:
                    restoration = Budget(deadline, PROTOCOL.ALLOCATIONS['restoration'])
                    restoration.resident_cells = retained_cells + 4 * len(vector)
                    out['restoration_stats'] = dict(support=originals, support_size=len(originals), complete=False)
                    progress('restoration_started')
                    original_columns = _responses(geometry, restoration)
                    restoration.resident_cells += sum(map(len, original_columns))
                    chart_rows, free, retained = OLD.decode_chart(chart, restoration)
                    restoration.resident_cells += 2 * sum(map(len, chart_rows.values())) + 4 * 851
                    alpha, stats = OLD.exact_support_solve(original_columns, {1224: F(-1)},
                                                         1224, originals, restoration)
                    out['restoration_stats'] = stats
                    certificate = OLD.certify(chart_rows, 1224, free, retained, rays, alpha, restoration)
                    payload = encoded(certificate); restoration.charge(len(payload))
                    if len(payload) > LIMITS['max_proposal_bytes']:
                        raise OverflowError('complete certificate byte cap')
                    out.update(status='CERTIFICATE_PROPOSED', certificate=certificate)
                    progress('certificate_proposed')
    except Exception as error:
        out.update(status='NONCERTIFIED' if isinstance(error, ValueError) and out['reduction_complete']
                   else 'UNKNOWN', reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    finally:
        out['stage_counts']['reduction'] = reduction_budget.counts()
        if restoration is not None:
            out['stage_counts']['restoration'] = restoration.counts()
    if len(encoded(out)) > LIMITS['max_proposal_bytes']:
        raise OverflowError('bounded reduction search outcome')
    return out
