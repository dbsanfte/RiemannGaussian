"""Conservative, path-scoped structural annotations for arithmetic potentials.

These are conditional ring/actual-mu observations, not universal estimate or
compiler proof certificates. No source value or numerical response is read.
"""
from fractions import Fraction as Q
import potential_candidate_language as LANGUAGE

SCHEMA = 'potential-candidate-semantics-v1'
SCOPE = 'structural identities for actual mu where original AST is defined'
SIGN_CLAIM = 'formal products only; no independent sign variation certified'
CROSS = 'all 2*c_i*c_j*T_i*T_j for i<j retained'


def analyze(program, meter):
    LANGUAGE.validate_candidate(program, meter)
    sizes = {}

    def size(value):
        meter.charge()
        if type(value) is list:
            answer = 1 + sum(size(child) for child in value)
            sizes[id(value)] = answer
            return answer
        return 1 + (len(value) // 8 if type(value) is str else 0)

    input_cells = size([state['tree'] for state in program['states']])
    # A bounded syntax tree has at most256 nodes/depth24. This conservative
    # reserve covers term/path references and rational metadata during walks.
    meter.live(input_cells + 131072)

    def rational(text):
        meter.charge(len(text) // 32 + 1)
        return meter.number(Q(text))

    def equal(left, right):
        meter.charge(sizes.get(id(left), 1) + sizes.get(id(right), 1) + 1)
        return left == right

    def factors(node, path):
        meter.charge()
        if node[0] == 'scale':
            coefficient, found = factors(node[2], path + [2])
            return meter.number(rational(node[1]) * coefficient), found
        if node[0] == 'mul':
            left, lf = factors(node[1], path + [1])
            right, rf = factors(node[2], path + [2])
            return meter.number(left * right), lf + rf
        return Q(1), [(node, path)]

    def terms(node, path, coefficient=Q(1)):
        meter.charge()
        if node[0] == 'scale':
            return terms(node[2], path + [2], meter.number(coefficient * rational(node[1])))
        if node[0] == 'add':
            return terms(node[1], path + [1], coefficient) + terms(node[2], path + [2], coefficient)
        c, found = factors(node, path)
        return [dict(node=node, path=path, coefficient=meter.number(coefficient * c), factors=found)]

    def prefix(node, path, scope):
        meter.charge()
        if (node[0] != 'sum' or not equal(node[2], ['int', 1])
                or not equal(node[4], ['x', ['v', node[1]]])):
            return None
        endpoint = node[3]
        if equal(endpoint, ['v', 't']):
            divisor = 1
        elif (endpoint[0] == 'idiv' and equal(endpoint[1], ['v', 't'])
              and endpoint[2][0] == 'int' and endpoint[2][1] >= 1):
            divisor = endpoint[2][1]
        else:
            divisor = None
        if divisor is not None:
            kind = 'target_copy' if divisor == 1 else 'lag'
            return kind, dict(kind='prefix_identity', path=path,
                endpoint='t' if divisor == 1 else 'floor(t/divisor)', divisor=divisor,
                normalized_core_potential='E(X)' if divisor == 1 else 'E(X/divisor)/divisor',
                domain='all integer X>=1' if divisor == 1 else 'positive X divisible by divisor',
                initial_core_potential='1' if divisor == 1 else '0', scope=scope)
        if (endpoint[0] == 'root' and endpoint[1][0] == 'v'
                and endpoint[1][1] in ('X', 't') and 2 * endpoint[2] <= endpoint[3]):
            meter.charge(); exponent = meter.number(Q(endpoint[2], endpoint[3]))
            base = endpoint[1][1]
            return 'bounded_root', dict(kind='root_prefix_envelope', path=path, base=base,
                exponent=str(exponent), bounded=True,
                normalized_core_bound='1' if base == 'X' else '3/2',
                domain='all integer X>=1', scope=scope)
        return None

    def common_points(flat):
        """Extract identical point factors from EVERY complete signed term."""
        meter.charge(len(flat))
        per_term = [[(node, path) for node, path in item['factors'] if node[0] == 'x'] for item in flat]
        removed = [set() for _ in flat]; common = []; considered = []
        if not per_term:
            return common, removed
        for candidate, _ in per_term[0]:
            meter.charge()
            if any(equal(candidate, old) for old in considered):
                continue
            considered.append(candidate)
            matches = [[path for node, path in values if equal(node, candidate)] for values in per_term]
            count = min(map(len, matches))
            if not count:
                continue
            occurrences = []
            for i, paths in enumerate(matches):
                meter.charge(count)
                for path in paths[:count]:
                    occurrences.append(path); removed[i].add(tuple(path))
            common.append(dict(index_path=occurrences[0] + [1], occurrence_paths=occurrences))
        return common, removed

    def prime_constants(node, path, active=None):
        meter.charge(); active = {} if active is None else active
        found = []
        if node[0] == 'x' and node[1][0] == 'v' and node[1][1] in active:
            binding = node[1][1]
            found.append(dict(kind='prime_guard_coefficient', path=path, guard_path=active[binding],
                binding=binding, identity='mu(prime)=-1', scope='guarded_summand'))
        for i, child in enumerate(node[1:], 1):
            meter.charge()
            if type(child) is not list:
                continue
            child_active = active
            if (node[0] == 'guard' and i == 2 and node[1][0] == 'prime'
                    and node[1][1][0] == 'v'):
                child_active = dict(active, **{node[1][1][1]: path + [1]})
            found.extend(prime_constants(child, path + [i], child_active))
        return found

    output = []
    for index, state in enumerate(program['states']):
        meter.charge()
        weight = rational(state['weight']); coefficient, found = factors(state['tree'], [])
        effective = meter.number(weight * meter.number(coefficient * coefficient))
        point_paths = [path for node, path in found if node[0] == 'x']
        nonpoints = [(node, path) for node, path in found if node[0] != 'x']
        annotations = []; unresolved = ['uniform_signed_innovation_estimate']
        if point_paths:
            annotations.append(dict(kind='whole_state_point_masks', factor_paths=point_paths,
                identity='mu(n)^2=squarefree(n)', scope='entire_state_square', retained_core_signs=True))
        common = []
        if not nonpoints:
            core = 'unknown'
            annotations.append(dict(kind='unit_core_potential', normalized_core_potential='1/X',
                                    scope='unmasked_core_square'))
        elif len(nonpoints) >= 2:
            core = 'nonlinear'; unresolved.append('product_correlation')
            annotations.append(dict(kind='product_square', factor_paths=[path for _, path in nonpoints],
                                    scope='unmasked_core_square'))
            for node, path in nonpoints:
                recognized = prefix(node, path, 'component_square_only')
                if recognized:
                    annotations.append(recognized[1])
        else:
            node, path = nonpoints[0]
            recognized = prefix(node, path, 'unmasked_core_square')
            if recognized:
                core = recognized[0]; annotations.append(recognized[1])
            elif node[0] == 'add':
                core = 'coupled_sum'; unresolved.append('mixed_term_estimate')
                flat = terms(node, path); common, removed = common_points(flat)
                if common:
                    annotations.append(dict(kind='common_point_masks', factors=common,
                        identity='mu(n)^2=squarefree(n)', scope='entire_state_square', retained_core_signs=True))
                signed_terms = []
                for i, item in enumerate(flat):
                    meter.charge()
                    remaining = [(n, p) for n, p in item['factors'] if tuple(p) not in removed[i]]
                    signed_terms.append(dict(path=item['path'], coefficient=str(item['coefficient']),
                        factor_paths=[p for n, p in remaining if n[0] != 'x'],
                        point_factor_paths=[p for n, p in remaining if n[0] == 'x']))
                annotations.append(dict(kind='signed_sum_square', terms=signed_terms, cross_terms=CROSS,
                                        sign_claim=SIGN_CLAIM, scope='unmasked_core_square'))
                for item in flat:
                    for factor, factor_path in item['factors']:
                        if factor[0] == 'x':
                            continue
                        recognized = prefix(factor, factor_path, 'component_square_only')
                        if recognized:
                            annotations.append(recognized[1])
            elif node[0] == 'sum':
                body = node[4]
                prime_guarded = (body[0] == 'guard' and equal(body[1], ['prime', ['v', node[1]]]))
                core = 'coupled_bank' if prime_guarded else 'coupled_sum'
                unresolved.append('index_pair_correlation' if prime_guarded else 'mixed_term_estimate')
                annotations.append(dict(kind='sum_bank_square', path=path, binding=node[1],
                    lower_path=path + [2], upper_path=path + [3], body_path=path + [4],
                    prime_guarded=prime_guarded, cross_terms='all pairs of distinct summation indices retained',
                    sign_claim=SIGN_CLAIM, scope='unmasked_core_square'))
            else:
                core = 'unknown'; unresolved.append('unclassified_scalar')
                annotations.append(dict(kind='unresolved_scalar', path=path))
        annotations.extend(prime_constants(state['tree'], []))
        if effective == 0:
            annotations.append(dict(kind='zero_scalar', scope='where_original_state_is_defined'))
        mechanism = 'mask' if point_paths or common else core
        output.append(dict(state=index, weight=state['weight'], mechanism=mechanism,
            outer_coefficient=str(coefficient), effective_weight=str(effective), core_mechanism=core,
            annotations=annotations, unresolved=unresolved))
    result = dict(schema=SCHEMA, mechanism='baseline' if not output else
                  'multi_state' if len(output) == 2 else output[0]['mechanism'],
                  states=output, scope=SCOPE, universal_estimate_verified=False,
                  global_bound_proved=False, RH_proved=False)
    meter.live(input_cells + size_json(result, meter))
    return result


def size_json(value, meter):
    """Charge the complete compact annotation traversal without digest IDs."""
    meter.charge()
    if type(value) is dict:
        return 1 + sum(size_json(key, meter) + size_json(item, meter) for key, item in value.items())
    if type(value) is list:
        return 1 + sum(size_json(item, meter) for item in value)
    return 1 + (len(value) // 8 if type(value) is str else 0)
