"""Exact algebra and dependency hygiene for missing-bound discovery.

This layer imports no numerical scorer. It verifies polynomial identities and
conditional implications, and exposes external assumptions and open leaves.
Graph validation never promotes finite evidence, representation changes or a
review registry into an independently discharged universal bound.

All functions accept an optional shared ``meter`` with charge(n). A supplied
meter is forwarded unchanged; omitted meters are not created or reset.
Quadratic coefficients denote monomials: off-diagonal coefficient c means
c*x*y, hence its symmetric-matrix entry is c/2.
"""
from fractions import Fraction as Q
import re

SCHEMA = 'obstruction-bound-certificate-v1'
GRAPH_SCHEMA = 'obstruction-argument-graph-v1'
QUANTIFIERS = 'for every epsilon>0, exists C_epsilon independent of X'
RULES = {'obligation', 'finite_observation', 'young_split', 'dyadic_transport',
         'dyadic_recurrence', 'reviewed_implication', 'equivalent_restatement'}
KINDS = {'algebra', 'uniform_bound', 'base_bound', 'finite_evidence'}
STATUSES = {'proven', 'open', 'finite_evidence'}


def _charge(meter, n=1):
    if meter is not None: meter.charge(n)


def _number(value, meter):
    _charge(meter)
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > 4096:
        raise OverflowError('exact certificate rational bit cap4096')
    return value


def _q(value, meter, canonical=False):
    _charge(meter)
    if type(value) is int: result = Q(value)
    elif type(value) is Q: result = value
    elif type(value) is str:
        if not 1 <= len(value) <= 2500 or re.fullmatch(r'-?\d+(?:/[1-9]\d*)?', value) is None:
            raise ValueError('bounded exact rational syntax')
        result = Q(value)
    else: raise ValueError('exact rational, never float or bool')
    _number(result, meter)
    if canonical and (type(value) is not str or str(result) != value):
        raise ValueError('canonical rational coefficient string')
    return result


def _name(value):
    if type(value) is not str or not 1 <= len(value) <= 128 or re.fullmatch(r'[A-Za-z][A-Za-z0-9_.:-]*', value) is None:
        raise ValueError('bounded named atom or obligation identifier')
    return value


def quadratic_form(terms, meter=None):
    """Merge commuting sparse monomials, sort, and remove exact zero terms."""
    if type(terms) is not list or len(terms) > 512: raise ValueError('bounded quadratic terms')
    merged = {}; atoms = set()
    for term in terms:
        _charge(meter)
        if type(term) not in (list, tuple) or len(term) != 3: raise ValueError('atom,atom,coefficient term')
        a, b = sorted((_name(term[0]), _name(term[1]))); atoms.update((a, b))
        if len(atoms) > 64: raise ValueError('at most64 named atoms')
        coefficient = _q(term[2], meter)
        merged[(a, b)] = _number(merged.get((a, b), Q(0)) + coefficient, meter)
    return {'terms': [[a, b, str(c)] for (a, b), c in sorted(merged.items()) if c]}


def verify_quadratic_form(form, meter=None):
    if type(form) is not dict or set(form) != {'terms'}: raise ValueError('exact quadratic form schema')
    if type(form['terms']) is not list or len(form['terms']) > 512: raise ValueError('bounded canonical term list')
    for term in form['terms']:
        if type(term) is not list or len(term) != 3: raise ValueError('JSON quadratic triple')
        _q(term[2], meter, True)
    if quadratic_form(form['terms'], meter) != form: raise ValueError('canonical sparse quadratic form required')
    return True


def _scale(form, coefficient, meter):
    return quadratic_form([[a, b, _number(Q(c) * coefficient, meter)] for a, b, c in form['terms']], meter)


def _add(*forms, meter=None):
    return quadratic_form([term for form in forms for term in form['terms']], meter)


def _square(linear, meter):
    terms = []
    for i, (a, ca) in enumerate(linear):
        for j in range(i, len(linear)):
            b, cb = linear[j]
            factor = 1 if i == j else 2
            terms.append([a, b, _number(factor * ca * cb, meter)])
    return quadratic_form(terms, meter)


def _distinct(*atoms):
    for atom in atoms: _name(atom)
    if len(set(atoms)) != len(atoms): raise ValueError('distinct roles for named atoms')


def young_certificate(eta, U='U', D='D', R='R', meter=None):
    eta = _q(eta, meter)
    if eta <= 0: raise ValueError('strictly positive Young parameter')
    _distinct(U, D, R)
    inverse = _number(1 / eta, meter)
    upper = quadratic_form([[U, U, 1 + eta], [D, D, 1 + inverse]], meter)
    square = _square([(U, Q(1)), (D, Q(1))], meter)
    gap = _add(upper, _scale(square, Q(-1), meter), meter=meter)
    return dict(schema=SCHEMA, rule='young_split', eta=str(eta),
                atoms=dict(R=R, U=U, D=D), definition=[[U, '1'], [D, '1']],
                upper=upper, expanded_square=square, gap=gap,
                psd=dict(order=[U, D], matrix=[[str(eta), '-1'], ['-1', str(inverse)]],
                         principal_minors=[str(eta), str(inverse)], determinant='0'),
                conclusion='conditional on the stated linear identity R=U+D',
                uniform_bound_discharged=False, RH_proved=False)


def _psd2(witness, gap, meter):
    if type(witness) is not dict or set(witness) != {'order', 'matrix', 'principal_minors', 'determinant'}:
        raise ValueError('exact2x2 PSD witness')
    order, matrix = witness['order'], witness['matrix']
    if type(order) is not list or len(order) != 2 or order[0] == order[1]: raise ValueError('two distinct PSD atoms')
    for a in order: _name(a)
    if type(matrix) is not list or len(matrix) != 2 or any(type(r) is not list or len(r) != 2 for r in matrix):
        raise ValueError('rational2x2 matrix')
    a, b, c, d = [_q(matrix[i][j], meter, True) for i in range(2) for j in range(2)]
    determinant = _number(a * d - b * c, meter)
    if b != c or a < 0 or d < 0 or determinant < 0: raise ValueError('symmetric positive semidefinite matrix')
    if witness['principal_minors'] != [str(a), str(d)] or witness['determinant'] != str(determinant):
        raise ValueError('exact PSD principal minors and determinant')
    represented = quadratic_form([[order[0], order[0], a], [order[0], order[1], 2 * b], [order[1], order[1], d]], meter)
    if represented != gap: raise ValueError('PSD witness bound to the full quadratic gap')


def transport_certificate(a0, a1, R='R', D0='D0', D1='D1', meter=None):
    a0, a1 = _q(a0, meter), _q(a1, meter); _distinct(R, D0, D1)
    parent = quadratic_form([[R, R, 1]], meter)
    child = _scale(_add(_square([(R, a0), (D0, Q(1))], meter),
                        _square([(R, a1), (D1, Q(1))], meter), meter=meter), Q(1, 4), meter)
    coefficient = _number((a0 * a0 + a1 * a1) / 4, meter)
    cross = [[R, D0, str(_number(a0 / 2, meter))], [R, D1, str(_number(a1 / 2, meter))]]
    correction = quadratic_form(cross + [[D0, D0, '1/4'], [D1, D1, '1/4']], meter)
    return dict(schema=SCHEMA, rule='dyadic_transport', atoms=dict(R=R, D0=D0, D1=D1),
                coefficients=[str(a0), str(a1)], parent=parent, child=child,
                parent_coefficient=str(coefficient), correction=correction, cross_terms=cross,
                child_definitions=[[[R, str(a0)], [D0, '1']], [[R, str(a1)], [D1, '1']]],
                normalization='one quarter of both complete child squares; sum over every parent coordinate',
                conclusion='exact identity; every signed cross and defect square retained',
                uniform_bound_discharged=False, RH_proved=False)


def _base(scale):
    if type(scale) is not int or not 1 <= scale <= 2**30 or scale & (scale - 1):
        raise ValueError('positive bounded dyadic base scale')
    return scale


def recurrence_certificate(rho, C, base_scale=1, base_bound=0, *, F='F',
                           step_id='step', base_id='base', meter=None):
    rho, C, B = _q(rho, meter), _q(C, meter), _q(base_bound, meter)
    _base(base_scale); _name(F); _name(step_id); _name(base_id)
    if not 0 <= rho <= 1 or C < 0 or B < 0: raise ValueError('0<=rho<=1 and nonnegative recurrence/base constants')
    if step_id == base_id: raise ValueError('distinct recurrence step and base premises')
    bounded = rho < 1 or C == 0
    bound = (_number(max(B, _number(C / (1 - rho), meter)), meter) if rho < 1 else B) if bounded else None
    return dict(schema=SCHEMA, rule='dyadic_recurrence', rho=str(rho), constant=str(C),
                base_scale=base_scale, base_bound=str(B), atom=F,
                classification='bounded' if bounded else 'logarithmic',
                uniform_bound=str(bound) if bound is not None else None,
                iterated_bound='rho^k*base_bound+constant*sum_{j=0}^{k-1}rho^j; k>=0',
                logarithmic_bound='base_bound+constant*k; X=base_scale*2^k',
                subpower_consequence='for every epsilon>0: F(X)<=(base_bound+constant/(2^epsilon-1))*(X/base_scale)^epsilon',
                premises=dict(step=f'for every dyadic X>={base_scale}: {F}(2X)<={rho}*{F}(X)+{C}',
                              base=f'{F}({base_scale})<={B}'),
                premise_bindings=dict(step=step_id, base=base_id),
                conclusion='conditional dyadic growth; the uniform step and base premises remain required',
                premise_proved=False, uniform_bound_discharged=False, RH_proved=False)


def verify_certificate(certificate, meter=None):
    if type(certificate) is not dict or certificate.get('schema') != SCHEMA:
        raise ValueError('exact bound certificate schema')
    rule = certificate.get('rule')
    if rule == 'young_split':
        atoms = certificate['atoms']
        expected = young_certificate(certificate['eta'], atoms['U'], atoms['D'], atoms['R'], meter)
        _psd2(certificate['psd'], certificate['gap'], meter)
    elif rule == 'dyadic_transport':
        atoms = certificate['atoms']; coefficients = certificate['coefficients']
        if type(coefficients) is not list or len(coefficients) != 2: raise ValueError('two exact transport coefficients')
        expected = transport_certificate(*coefficients, atoms['R'], atoms['D0'], atoms['D1'], meter)
        rhs = _add(_scale(certificate['parent'], _q(certificate['parent_coefficient'], meter, True), meter),
                   certificate['correction'], meter=meter)
        if rhs != certificate['child']: raise ValueError('complete dyadic identity with all mixed terms')
    elif rule == 'dyadic_recurrence':
        bindings = certificate['premise_bindings']
        expected = recurrence_certificate(certificate['rho'], certificate['constant'], certificate['base_scale'],
                                          certificate['base_bound'], F=certificate['atom'],
                                          step_id=bindings['step'], base_id=bindings['base'], meter=meter)
    else: raise ValueError('unverified algebraic certificate rule')
    _charge(meter)
    if certificate != expected: raise ValueError('exact complete reconstructed certificate')
    return dict(verified_algebra=True, conditional=rule in ('young_split', 'dyadic_recurrence'),
                uniform_bound_discharged=False, RH_proved=False)


def scope(source, base_scale=1):
    _name(source); _base(base_scale)
    return dict(source=source, domain=f'all dyadic integers X>={base_scale}', quantifiers=QUANTIFIERS)


def _scope(value):
    if type(value) is not dict or set(value) != {'source', 'domain', 'quantifiers'}:
        raise ValueError('exact source/full uniform domain scope')
    _name(value['source'])
    if type(value['domain']) is not str: raise ValueError('full uniform dyadic domain')
    match = re.fullmatch(r'all dyadic integers X>=([1-9]\d{0,9})', value['domain'])
    if match is None: raise ValueError('full uniform dyadic domain, not finite scale data')
    base = _base(int(match.group(1)))
    if value['quantifiers'] != QUANTIFIERS: raise ValueError('full uniform cofinal-bound quantifiers')
    return base


def _provenance(value):
    if type(value) is not str or not 1 <= len(value) <= 4096: raise ValueError('explicit import/review provenance')


def _acyclic(adjacency, meter):
    marks = {}
    def visit(node):
        _charge(meter)
        if marks.get(node) == 1: raise ValueError('argument dependency cycle, including reviewed equivalence classes')
        if marks.get(node) == 2: return
        marks[node] = 1
        for dependency in adjacency[node]: visit(dependency)
        marks[node] = 2
    for node in adjacency: visit(node)


def verify_graph(graph, meter=None):
    """Validate claimed closure, never independently certify imported theorems.

    Premises require id/kind/statement/status/provenance/scope. Generated nodes
    require id/kind/statement/status/rule/dependencies/certificate/scope.
    Reviewed rules require id/premises/conclusion/provenance/scope; equivalences
    require id/left/right/provenance/scope and mean the same COFINAL-BOUND class.
    """
    keys = {'schema', 'scope', 'premises', 'nodes', 'reviewed_rules', 'equivalences', 'goals'}
    if type(graph) is not dict or set(graph) != keys or graph['schema'] != GRAPH_SCHEMA:
        raise ValueError('exact argument graph schema')
    base = _scope(graph['scope'])
    for key in ('premises', 'nodes', 'reviewed_rules', 'equivalences', 'goals'):
        if type(graph[key]) is not list or len(graph[key]) > 256: raise ValueError('bounded argument records')
    records = {}; external = set(); trusted = []; reviews = {}; edges = {}; verified = []
    for kind, entries in (('premise', graph['premises']), ('node', graph['nodes'])):
        expected = {'id', 'kind', 'statement', 'status', 'scope'} | ({'provenance'} if kind == 'premise' else {'rule', 'dependencies', 'certificate'})
        for item in entries:
            _charge(meter)
            if type(item) is not dict or set(item) != expected: raise ValueError('exact premise/node record')
            _name(item['id'])
            if item['id'] in records: raise ValueError('unique obligation identifiers')
            if item['scope'] != graph['scope']: raise ValueError('same source and full uniform scope for every argument node')
            if item['kind'] not in KINDS or item['status'] not in STATUSES: raise ValueError('known obligation kind/status')
            if type(item['statement']) is not str or not 1 <= len(item['statement']) <= 4096: raise ValueError('explicit bounded statement')
            if (item['kind'] == 'finite_evidence') != (item['status'] == 'finite_evidence'):
                raise ValueError('finite evidence stays finite, not proven/open uniform theorem')
            records[item['id']] = item
            if kind == 'premise':
                _provenance(item['provenance']); external.add(item['id'])
                if item['status'] == 'proven': trusted.append(dict(type='external_reviewed_assumption', record=item))
            else:
                if item['rule'] not in RULES: raise ValueError('unverified rule name')
                deps = item['dependencies']
                if type(deps) is not list or len(deps) > 64 or len(set(deps)) != len(deps): raise ValueError('distinct bounded dependency IDs')
                for dependency in deps: _name(dependency)
    if len(records) > 256: raise ValueError('total graph node cap256')
    for r in graph['reviewed_rules']:
        if type(r) is not dict or set(r) != {'id', 'premises', 'conclusion', 'provenance', 'scope'}:
            raise ValueError('exact reviewed implication record')
        _name(r['id']); _provenance(r['provenance'])
        if r['id'] in reviews or r['scope'] != graph['scope']: raise ValueError('unique same-scope reviewed rule')
        if type(r['premises']) is not list or len(r['premises']) > 64 or len(set(r['premises'])) != len(r['premises']):
            raise ValueError('reviewed rule premises')
        if r['conclusion'] not in records or any(p not in records for p in r['premises']): raise ValueError('bound reviewed rule node IDs')
        reviews[r['id']] = r
        trusted.append(dict(type='external_reviewed_implication', record=r))
    parent = {key: key for key in records}
    def find(key):
        while parent[key] != key: key = parent[key]
        return key
    for edge in graph['equivalences']:
        if type(edge) is not dict or set(edge) != {'id', 'left', 'right', 'provenance', 'scope'}:
            raise ValueError('explicit reviewed cofinal-class edge')
        _name(edge['id']); _provenance(edge['provenance'])
        a, b = edge['left'], edge['right']
        if edge['id'] in edges or a == b or a not in records or b not in records or edge['scope'] != graph['scope']:
            raise ValueError('unique same-scope reviewed equivalence endpoints')
        if records[a]['kind'] != records[b]['kind'] or records[a]['kind'] == 'finite_evidence':
            raise ValueError('cofinal equivalence cannot promote finite evidence or change claim kind')
        ra, rb = find(a), find(b); parent[max(ra, rb)] = min(ra, rb)
        edges[edge['id']] = edge; trusted.append(dict(type='external_reviewed_cofinal_equivalence', record=edge))
    classes = {key: find(key) for key in records}
    adjacency = {key: ([] if key in external else records[key]['dependencies']) for key in records}
    if any(dep not in records for deps in adjacency.values() for dep in deps): raise ValueError('every dependency recorded')
    _acyclic(adjacency, meter)
    contracted = {c: set() for c in classes.values()}
    for node in graph['nodes']:
        rule, cert, deps = node['rule'], node['certificate'], node['dependencies']
        if node['status'] == 'proven' and any(records[d]['status'] != 'proven' for d in deps):
            raise ValueError('claimed proven node depends on open or finite evidence')
        if rule in ('young_split', 'dyadic_transport', 'dyadic_recurrence'):
            if type(cert) is not dict or cert.get('rule') != rule: raise ValueError('rule/certificate binding')
            verify_certificate(cert, meter); verified.append(node['id'])
            if rule != 'dyadic_recurrence':
                if node['kind'] != 'algebra': raise ValueError('algebraic representation rule is not a uniform bound')
            else:
                if node['kind'] != 'uniform_bound' or cert['base_scale'] != base: raise ValueError('recurrence full domain/base binding')
                bindings = cert['premise_bindings']
                if set(deps) != set(bindings.values()): raise ValueError('both recurrence premises bound, including base')
                for role, expected_kind in (('step', 'uniform_bound'), ('base', 'base_bound')):
                    dependency = records[bindings[role]]
                    if dependency['kind'] != expected_kind or dependency['statement'] != cert['premises'][role]:
                        raise ValueError('recurrence step/base statement and type binding')
        elif rule == 'reviewed_implication':
            if type(cert) is not dict or set(cert) != {'review_id'} or cert['review_id'] not in reviews:
                raise ValueError('explicit reviewed implication required')
            reviewed = reviews[cert['review_id']]
            if reviewed['conclusion'] != node['id'] or reviewed['premises'] != deps: raise ValueError('reviewed implication exact binding')
        elif rule == 'equivalent_restatement':
            if type(cert) is not dict or set(cert) != {'review_id'} or cert['review_id'] not in edges or len(deps) != 1:
                raise ValueError('one explicitly reviewed representation transfer')
            if {node['id'], deps[0]} != {edges[cert['review_id']]['left'], edges[cert['review_id']]['right']}:
                raise ValueError('reviewed equivalence transfer exact binding')
        elif rule == 'obligation':
            if cert is not None or deps or node['status'] != 'open': raise ValueError('unresolved obligation remains open')
        elif rule == 'finite_observation':
            if cert is not None or deps or node['status'] != 'finite_evidence': raise ValueError('finite observation cannot prove a uniform bound')
        for dep in deps:
            a, b = classes[node['id']], classes[dep]
            if a == b:
                if rule != 'equivalent_restatement': raise ValueError('circular proof through an equivalent restatement')
            else: contracted[a].add(b)
    _acyclic(contracted, meter)
    if len(set(graph['goals'])) != len(graph['goals']) or any(g not in records for g in graph['goals']): raise ValueError('distinct existing goal IDs')
    memo = {}
    def leaves(key):
        if key in memo: return memo[key]
        item = records[key]
        if item['status'] == 'proven': result = set()
        else:
            result = set().union(*(leaves(d) for d in adjacency[key])) if adjacency[key] else set()
            if not result: result = {classes[key]}
        memo[key] = result; return result
    goals = []
    for goal in graph['goals']:
        unresolved = sorted(leaves(goal))
        goals.append(dict(id=goal, equivalence_class=classes[goal], undischarged_leaf_classes=unresolved,
                          proof_rank=len(unresolved), relatively_closed=records[goal]['status'] == 'proven',
                          independently_discharged_uniform_bound=False))
    groups = {}
    for key, representative in classes.items(): groups.setdefault(representative, []).append(key)
    unresolved_classes = sorted(set().union(*(set(g['undischarged_leaf_classes']) for g in goals)))
    return dict(validated=True, scope=graph['scope'], verified_algebra_nodes=verified,
                trusted_inputs=trusted, goals=goals,
                equivalence_classes=[dict(id=c, members=sorted(members)) for c, members in sorted(groups.items())],
                undischarged_leaves=[dict(equivalence_class=c, members=sorted(groups[c]),
                                         statuses={k: records[k]['status'] for k in sorted(groups[c])}) for c in unresolved_classes],
                known_change_of_representation=[n['id'] for n in graph['nodes'] if n['rule'] == 'equivalent_restatement'],
                discharged_uniform_bound=False, RH_proved=False)
