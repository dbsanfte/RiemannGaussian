"""Replay saved native coordinates without CVXPY attribute projection.

The supplied canonical map is checked for a complete bijection, not independently
derived from the solver's canonical matrix. This is diagnostic evidence only.
"""
import hashlib
import json
import math

SCHEMA = 'primitive-state-native-coordinate-replay-v1'


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()).hexdigest()


def vector(value, width, label):
    if type(value) is not list or len(value) != width:
        raise ValueError('complete ' + label)
    if any(type(v) not in (int, float) or not math.isfinite(v) for v in value):
        raise ValueError('finite ' + label)
    return value


def replay(trace):
    if trace.get('kind') != 'primal' or trace.get('schema') != 'primitive-state-solver-trace-v1':
        raise ValueError('known primal diagnostic trace')
    layout = trace['original_coordinate_map']
    if layout.get('scalar_offset') != 0 or layout.get('source_column_order') != 'identity' or layout.get('upper_triangle_order') != 'row-major-a-then-b-a-through-n-minus-1':
        raise ValueError('explicit scalar and symmetric upper triangle layout')
    width = trace['original_system_metadata']['variables']
    offset = layout['scalar_count']
    if type(width) is not int or width < 1 or type(offset) is not int or not 0 <= offset <= width:
        raise ValueError('complete positive coordinate dimensions')
    native = vector(trace['raw_solution']['x'], width, 'native coordinates')
    archived = vector(trace['original_vector'], width, 'archived coordinates')
    ids = trace['original_variable_ids']
    starts = trace['canonical_variable_map']
    blocks = layout['psd_blocks']
    if type(blocks) is not list or type(starts) is not dict or type(ids) is not dict or set(ids) != {'scalar', 'matrices'}:
        raise ValueError('explicit canonical variable maps')
    if type(ids['matrices']) is not dict or len({b['name'] for b in blocks}) != len(blocks) or set(ids['matrices']) != {b['name'] for b in blocks}:
        raise ValueError('all distinct named symmetric blocks')
    permutation = [None] * width
    used_ids = []

    def assign(variable_id, original_indices):
        if type(variable_id) is not int or variable_id < 1 or variable_id in used_ids:
            raise ValueError('distinct positive canonical variable ids')
        used_ids.append(variable_id)
        start = starts.get(str(variable_id))
        if type(start) is not int or not 0 <= start <= width - len(original_indices):
            raise ValueError('bounded canonical variable slice')
        for j, i in enumerate(original_indices):
            if type(i) is not int or not 0 <= i < width or permutation[i] is not None:
                raise ValueError('disjoint original coordinate blocks')
            permutation[i] = start + j

    if offset:
        assign(ids['scalar'], list(range(offset)))
    elif ids['scalar'] is not None:
        raise ValueError('no invented scalar variable')
    expected = offset
    for block in blocks:
        n = block['size']
        if type(n) is not int or n < 1:
            raise ValueError('positive symmetric matrix size')
        count = n * (n + 1) // 2
        if block['indices'] != list(range(expected, expected + count)):
            raise ValueError('complete original row-major upper triangle')
        assign(ids['matrices'][block['name']], block['indices'])
        expected += count
    if expected != width or set(starts) != {str(i) for i in used_ids} or any(i is None for i in permutation) or sorted(permutation) != list(range(width)):
        raise ValueError('complete bijective native coordinate map')
    raw = [native[i] for i in permutation]
    projected = [max(v, 0) if i < offset else v for i, v in enumerate(raw)]
    if archived != projected:
        raise ValueError('archived vector differs from declared scalar attribute projection')
    changed = [i for i, (a, b) in enumerate(zip(archived, raw)) if a != b]
    objective = vector(trace['original_system_metadata']['objective'], width, 'objective')
    raw_objective = math.fsum(c * v for c, v in zip(objective, raw))
    mapped_objective = math.fsum(c * v for c, v in zip(objective, archived))
    if not all(math.isfinite(v) for v in (raw_objective, mapped_objective)):
        raise ValueError('finite diagnostic objectives')
    return dict(schema=SCHEMA, original_vector=raw, original_vector_sha256=digest(raw),
        canonical_vector_sha256=digest(native), archived_vector_sha256=digest(archived),
        canonical_to_original_permutation=permutation,
        changed_coordinate_indices=changed, changed_coordinate_count=len(changed),
        raw_nonnegative_min=min(raw[:offset], default=None),
        archived_nonnegative_min=min(archived[:offset], default=None),
        raw_objective=raw_objective, archived_objective=mapped_objective,
        projection='max(x,0) on scalar nonnegative attributes only',
        canonical_variable_map_independently_derived=False,
        canonical_matrix_independently_rebuilt=False,
        numerical_evidence_only=True, certified=False, exact_admission=False,
        infeasibility_proved=False, global_bound_proved=False, RH_proved=False)
