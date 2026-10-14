"""Independent, conservative structural annotations for potential states.

No source values are evaluated here. An annotation records scoped identities
and elementary envelopes, never a uniform cancellation or innovation theorem.
The unchanged independent finite checker supplies syntax validation only.
"""
from fractions import Fraction
from math import gcd

from check_potential_candidate_discovery import validate_candidate


SCHEMA = 'potential-candidate-semantics-v1'
SCOPE = 'structural identities for actual mu where original AST is defined'
CORE_SCOPE = 'unmasked_core_square'
COMPONENT_SCOPE = 'component_square_only'
SIGN_SCOPE = 'formal products only; no independent sign variation certified'


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _json_cells(value, meter, depth=0):
    """Bound complete retained metadata before comparison or publication."""
    meter.charge()
    if depth > 64:
        raise OverflowError('semantic metadata depth')
    if type(value) is dict:
        total = 1
        for key, item in value.items():
            _require(type(key) is str, 'semantic JSON object keys')
            total += _json_cells(key, meter, depth + 1)
            total += _json_cells(item, meter, depth + 1)
            if total > 50000:
                raise OverflowError('semantic metadata cell cap')
        return total
    if type(value) is list:
        total = 1
        for item in value:
            total += _json_cells(item, meter, depth + 1)
            if total > 50000:
                raise OverflowError('semantic metadata cell cap')
        return total
    _require(value is None or type(value) in (str, int, bool), 'strict semantic JSON scalar')
    if type(value) is str:
        _require(len(value) <= 20000, 'bounded semantic text')
        meter.charge(len(value) // 32)
        return 1 + len(value) // 32
    if type(value) is int:
        meter.number(value)
    return 1


def _same(left, right, meter):
    """JSON payload equality that does not identify booleans with integers."""
    meter.charge()
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(_same(left[k], right[k], meter) for k in left)
    if type(left) is list:
        return len(left) == len(right) and all(_same(a, b, meter) for a, b in zip(left, right))
    return left == right


def _factors(tree, path, meter):
    """Distribute no sums: peel only scalar scales and outer products."""
    coefficient = Fraction(1)
    points, cores = [], []
    pending = [(tree, path)]
    while pending:
        node, where = pending.pop()
        meter.charge()
        if node[0] == 'scale':
            coefficient = meter.number(coefficient * Fraction(node[1]))
            pending.append((node[2], where + [2]))
        elif node[0] == 'mul':
            pending.append((node[2], where + [2]))
            pending.append((node[1], where + [1]))
        elif node[0] == 'x':
            points.append((node, where))
        else:
            cores.append((node, where))
    return coefficient, points, cores


def _prefix(tree, path, scope, meter):
    meter.charge()
    if (tree[0] != 'sum' or tree[2] != ['int', 1]
            or tree[4] != ['x', ['v', tree[1]]]):
        return None
    endpoint = tree[3]
    divisor = None
    if endpoint == ['v', 't']:
        divisor = 1
    elif (endpoint[0] == 'idiv' and endpoint[1] == ['v', 't']
          and endpoint[2][0] == 'int' and endpoint[2][1] >= 1):
        divisor = endpoint[2][1]
    if divisor is not None:
        return ('target_copy' if divisor == 1 else 'lag', dict(
            kind='prefix_identity', path=path,
            endpoint='t' if divisor == 1 else 'floor(t/divisor)', divisor=divisor,
            normalized_core_potential='E(X)' if divisor == 1 else 'E(X/divisor)/divisor',
            domain='all integer X>=1' if divisor == 1 else 'positive X divisible by divisor',
            initial_core_potential='1' if divisor == 1 else '0', scope=scope))
    if (endpoint[0] == 'root' and endpoint[1] in (['v', 't'], ['v', 'X'])
            and 2 * endpoint[2] <= endpoint[3]):
        common = gcd(endpoint[2], endpoint[3])
        exponent = meter.number(Fraction(endpoint[2] // common, endpoint[3] // common))
        base = endpoint[1][1]
        return 'bounded_root', dict(
            kind='root_prefix_envelope', path=path, base=base,
            exponent=str(exponent), bounded=True,
            normalized_core_bound='3/2' if base == 't' else '1',
            domain='all integer X>=1', scope=scope)
    return None


def _sum_terms(tree, path, meter):
    """Additive leaves keep original paths and signed rational coefficients."""
    result = []
    pending = [(tree, path, Fraction(1))]
    while pending:
        node, where, coefficient = pending.pop()
        meter.charge()
        if node[0] == 'add':
            pending.append((node[2], where + [2], coefficient))
            pending.append((node[1], where + [1], coefficient))
        elif node[0] == 'scale':
            coefficient = meter.number(coefficient * Fraction(node[1]))
            pending.append((node[2], where + [2], coefficient))
        else:
            result.append((node, where, coefficient))
    return result


def _common_points(terms, meter):
    """Match literal source-query ASTs; infer no arithmetic index alias."""
    groups, removed = [], set()
    seen = []
    for point, _ in terms[0][3]:
        if any(_same(point, old, meter) for old in seen):
            continue
        seen.append(point)
        matches = []
        for _, _, _, points, _ in terms:
            matches.append([where for candidate, where in points if _same(candidate, point, meter)])
        multiplicity = min(len(group) for group in matches)
        if not multiplicity:
            continue
        occurrences = [where for group in matches for where in group[:multiplicity]]
        removed.update(tuple(where) for where in occurrences)
        groups.append(dict(index_path=occurrences[0] + [1], occurrence_paths=occurrences))
    return groups, removed


def _core(core, meter):
    """Return classification, structural notes and any common point masks."""
    annotations, common_masks = [], []
    if not core:
        annotations.append(dict(kind='unit_core_potential', normalized_core_potential='1/X', scope=CORE_SCOPE))
        return 'unknown', annotations, common_masks
    if len(core) > 1:
        annotations.append(dict(kind='product_square', factor_paths=[where for _, where in core], scope=CORE_SCOPE))
        for tree, path in core:
            recognized = _prefix(tree, path, COMPONENT_SCOPE, meter)
            if recognized:
                annotations.append(recognized[1])
        return 'nonlinear', annotations, common_masks
    tree, path = core[0]
    recognized = _prefix(tree, path, CORE_SCOPE, meter)
    if recognized:
        return recognized[0], [recognized[1]], common_masks
    if tree[0] == 'add':
        terms = []
        for leaf, where, additive_coefficient in _sum_terms(tree, path, meter):
            coefficient, points, factors = _factors(leaf, where, meter)
            terms.append((leaf, where, meter.number(coefficient * additive_coefficient), points, factors))
        groups, removed = _common_points(terms, meter)
        if groups:
            common_masks.append(dict(kind='common_point_masks', factors=groups,
                identity='mu(n)^2=squarefree(n)', scope='entire_state_square', retained_core_signs=True))
        annotations.append(dict(kind='signed_sum_square', terms=[dict(
            path=where, coefficient=str(coefficient), factor_paths=[p for _, p in factors],
            point_factor_paths=[p for _, p in points if tuple(p) not in removed])
            for _, where, coefficient, points, factors in terms],
            cross_terms='all 2*c_i*c_j*T_i*T_j for i<j retained',
            sign_claim=SIGN_SCOPE, scope=CORE_SCOPE))
        for _, _, _, _, factors in terms:
            for node, where in factors:
                recognized = _prefix(node, where, COMPONENT_SCOPE, meter)
                if recognized:
                    annotations.append(recognized[1])
        return 'coupled_sum', annotations, common_masks
    if tree[0] == 'sum':
        name, lower, upper, body = tree[1:]
        prime_guarded = body[0] == 'guard' and body[1] == ['prime', ['v', name]]
        annotations.append(dict(kind='sum_bank_square', path=path, binding=name,
            lower_path=path + [2], upper_path=path + [3], body_path=path + [4],
            prime_guarded=prime_guarded,
            cross_terms='all pairs of distinct summation indices retained',
            sign_claim=SIGN_SCOPE, scope=CORE_SCOPE))
        return 'coupled_bank' if prime_guarded else 'coupled_sum', annotations, common_masks
    annotations.append(dict(kind='unresolved_scalar', path=path))
    return 'unknown', annotations, common_masks


def _prime_notes(tree, meter):
    notes = []
    pending = [(tree, [], {})]
    while pending:
        node, path, prime_guards = pending.pop()
        meter.charge()
        if node[0] == 'x' and node[1][0] == 'v' and node[1][1] in prime_guards:
            name = node[1][1]
            notes.append(dict(kind='prime_guard_coefficient', path=path,
                guard_path=prime_guards[name], binding=name,
                identity='mu(prime)=-1', scope='guarded_summand'))
        children = []
        for index in range(1, len(node)):
            if type(node[index]) is list:
                context = prime_guards
                if (node[0] == 'guard' and index == 2 and node[1][0] == 'prime'
                        and node[1][1][0] == 'v'):
                    context = dict(prime_guards)
                    context[node[1][1][1]] = path + [1]
                children.append((node[index], path + [index], context))
        pending.extend(reversed(children))
    return notes


def analyze(program, meter):
    count = validate_candidate(program, meter)
    input_cells = _json_cells(program, meter)
    meter.live(input_cells + 32 * count + 128)
    states = []
    for state_index, state in enumerate(program['states']):
        coefficient, points, cores = _factors(state['tree'], [], meter)
        core_mechanism, structural, common_masks = _core(cores, meter)
        notes = []
        if points:
            notes.append(dict(kind='whole_state_point_masks', factor_paths=[path for _, path in points],
                identity='mu(n)^2=squarefree(n)', scope='entire_state_square', retained_core_signs=True))
        notes.extend(common_masks)
        notes.extend(structural)
        notes.extend(_prime_notes(state['tree'], meter))
        effective = meter.number(Fraction(state['weight']) * meter.number(coefficient * coefficient))
        if not effective:
            notes.append(dict(kind='zero_scalar', scope='where_original_state_is_defined'))
        unresolved = ['uniform_signed_innovation_estimate']
        reason = {'coupled_sum': 'mixed_term_estimate', 'coupled_bank': 'index_pair_correlation',
            'nonlinear': 'product_correlation', 'unknown': 'unclassified_scalar'}.get(core_mechanism)
        if reason and cores:
            unresolved.append(reason)
        states.append(dict(state=state_index, weight=state['weight'],
            mechanism='mask' if points or common_masks else core_mechanism,
            outer_coefficient=str(coefficient), effective_weight=str(effective),
            core_mechanism=core_mechanism, annotations=notes, unresolved=unresolved))
    result = dict(schema=SCHEMA,
        mechanism='baseline' if not states else 'multi_state' if len(states) == 2 else states[0]['mechanism'],
        states=states, scope=SCOPE, universal_estimate_verified=False,
        global_bound_proved=False, RH_proved=False)
    output_cells = _json_cells(result, meter)
    meter.live(input_cells + output_cells + 32 * count + 128)
    return result


def verify(program, annotation, meter):
    supplied_cells = _json_cells(annotation, meter)

    class RetainedAnnotation:
        def __getattr__(self, name):
            return getattr(meter, name)

        def live(self, cells):
            return meter.live(cells + supplied_cells)

    expected = analyze(program, RetainedAnnotation())
    expected_cells = _json_cells(expected, meter)
    program_cells = _json_cells(program, meter)
    meter.live(supplied_cells + expected_cells + program_cells + 128)
    _require(_same(expected, annotation, meter), 'independent semantic annotation mismatch')
    return True
