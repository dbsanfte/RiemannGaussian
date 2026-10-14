"""Audited symbolic recipes for a limited part of the fixed primitive grammar.

These recipes retain parameter-sized sums. Source fingerprints bind the reviewed
compiler definitions; finite correspondence tests are regression checks, never
universal proofs. Full target/source adaptation is deliberately not claimed.
"""
import copy
from fractions import Fraction as F
import hashlib
from pathlib import Path

import cancellation_primitive_state_localizers as LANGUAGE
import primitive_state_uniform_scalar_diagnostic as LEDGER

SCHEMA = 'primitive-state-parametric-source-recipes-v1'
FLAGS = dict(full_target_proved=False, global_bound_proved=False, RH_proved=False,
             inequality_proved=False, MU_EQ_proved=False, candidate_admitted=False)
digest = LEDGER.digest


def integer(n): return ['int', n]
def variable(name): return ['v', name]
def rational(q): return ['q', str(F(q))]
def plus(a, b): return ['add', a, b]
def times(a, b): return ['mul', a, b]
def scale(q, a): return ['scale', str(F(q)), a]
def minus(a, b): return plus(a, scale(-1, b))
def total(name, lo, hi, body): return ['sum', name, lo, hi, body]


def verified_sources():
    root = Path(LANGUAGE.__file__).resolve().parent
    total_bytes = 0
    for name, expected in LEDGER.SOURCE_BINDINGS.items():
        path = root / name
        total_bytes += path.stat().st_size
        if total_bytes > 1048576:
            raise OverflowError('bounded source recipe reads')
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('unreviewed symbolic source compiler ' + name)
    descriptors = LANGUAGE.descriptors()
    if digest(descriptors) != LEDGER.DESCRIPTORS_SHA256:
        raise ValueError('unreviewed symbolic source descriptor catalogue')
    return descriptors, total_bytes


def region_sum(region, body):
    X = variable('X')
    if region == 'parent':
        lo, hi = X, ['isub', ['imul', integer(2), X], integer(1)]
    elif region == 'child':
        lo, hi = ['imul', integer(2), X], ['isub', ['imul', integer(4), X], integer(1)]
    else:
        raise ValueError('complete parent or child region')
    return total('t', lo, hi, body)


def divisor_state(theta, power):
    """Exact local definitions in the existing finite compiler's named syntax."""
    if theta not in ('1/3', '1/2', '2/3') or type(power) is not int or power not in (-1, 0, 1):
        raise ValueError('current divisor-cell source parameters')
    t, a, d = variable('t'), variable('a'), variable('d')
    exponent = F(theta)
    cutoff = ['root', t, exponent.numerator, exponent.denominator]
    weight = ['ratio', integer(1), a] if power == -1 else rational(1) if power == 0 else ['embed', a]
    body = times(weight, times(['x', a], ['x', d]))
    divisor = ['divides', d, a]
    inside = ['le', d, cutoff]
    def pairs(predicate=None):
        summand = ['guard', divisor, copy.deepcopy(body)]
        if predicate is not None:
            summand = ['guard', copy.deepcopy(predicate), summand]
        return total('a', integer(1), t, total('d', integer(1), a, summand))
    B, I, O = pairs(), pairs(inside), pairs(['not', inside])
    D = scale(F(1, 2), minus(minus(I, O), rational(1)))
    Z = minus(plus(I, O), rational(1))
    P = total('a', integer(1), t, ['x', a])
    return dict(B=B, I=I, O=O, D=D, Z=Z, P=P, cutoff=cutoff)


def _cell_recipes(descriptors):
    out = []
    for region in ('parent', 'child'):
        for theta in ('1/3', '1/2', '2/3'):
            for power in (-1, 0, 1):
                state = divisor_state(theta, power)
                selected = {kind: [dict(index=j, id=d['id'], form=d['form']) for j, d in enumerate(ds)
                                   if d['family'] == 'divisor_cell_' + kind and d['region'] == region
                                   and d['theta'] == theta and d['power'] == power]
                            for kind, ds in descriptors.items()}
                if [d['form'] for d in selected['square']] != ['contrast', 'prefix_plus', 'prefix_minus'] or \
                   [d['form'] for d in selected['relation']] != ['one', 'prefix', 'contrast', 'normalization']:
                    raise ValueError('complete cell source descriptor references')
                identities = [
                    ('complete_partition', state['B'], plus(state['I'], state['O'])),
                    ('complete_normalization', state['Z'], minus(state['B'], rational(1))),
                    ('inside_contrast', state['D'], minus(minus(state['I'], rational(1)), scale(F(1, 2), state['Z']))),
                    ('outside_contrast', state['D'], plus(scale(-1, state['O']), scale(F(1, 2), state['Z']))),
                ]
                for kind, lhs, rhs in identities:
                    recipe = dict(kind=kind, family='divisor_cell_state', region=region, theta=theta, power=power,
                                  parameters=dict(X='integer >= 1'),
                                  positive_domain='t in region; 1<=d<=a<=t<=4X-1',
                                  denominator_domain='a>=1; reciprocal has no zero denominator',
                                  cutoff_semantics='floor(t^theta); equality belongs to inside; complete complement retained',
                                  descriptor_references=selected, functions=[],
                                  lhs=region_sum(region, copy.deepcopy(lhs)), rhs=region_sum(region, copy.deepcopy(rhs)))
                    recipe['id'] = digest(recipe)
                    out.append(recipe)
    return out


PRIMITIVE_DEFINITIONS = {
    'rho_norm': dict(source='grouped_arithmetic_templates.py',
                     definition='rho_norm(n)=x_n^2-1_(n squarefree), n>=1; factor-certified norm source at every n'),
    'rho_prime_power': dict(source='grouped_arithmetic_templates.py',
                            definition='rho_prime_power(n)=x_n+1 if n is prime; x_n if n=p^e with p prime and e>=2; 0 otherwise; n>=1'),
}


def _rowmass_recipes(descriptors):
    out = []
    X, n, t = variable('X'), variable('n'), variable('t')
    H = ['isub', ['imul', integer(4), X], integer(1)]
    twoX = ['imul', integer(2), X]
    for family in ('norm', 'prime_power'):
        function = 'rho_' + family
        definition = dict(PRIMITIVE_DEFINITIONS[function], source_sha256=LEDGER.SOURCE_BINDINGS['grouped_arithmetic_templates.py'])
        function_record = dict(name=function, arity=1, definition_hash=digest(definition))
        # The identity is valid for every polynomial-valued rho. Its actual
        # primitive meaning is a separately bound source substitution, not zero.
        rho = ['symbol', function, n]
        rowmass = total('t', ['max', twoX, n], H, ['embed', t])
        body = times(rowmass, rho)
        predicate = ['le', n, twoX]
        full = total('n', integer(1), H, body)
        head = total('n', integer(1), H, ['guard', predicate, copy.deepcopy(body)])
        tail = total('n', integer(1), H, ['guard', ['not', predicate], copy.deepcopy(body)])
        selected = [dict(index=j, id=d['id'], region=d['region']) for j, d in enumerate(descriptors['relation'])
                    if d['family'] == family and d.get('multiplier') == 'one' and d['weight'] == 'child_rowmass']
        if [d['region'] for d in selected] != ['all', 'head', 'tail']:
            raise ValueError('complete rowmass source descriptors')
        recipe = dict(kind='complete_partition', family='primitive_rowmass', primitive_family=family,
                      parameters=dict(X='integer >= 1'), positive_domain='1<=n<=4X-1; max(2X,n)<=t<=4X-1',
                      primitive_definition=definition, descriptor_references=selected,
                      functions=[function_record], lhs=full, rhs=plus(head, tail))
        recipe['id'] = digest(recipe)
        out.append(recipe)
    return out


def recipes():
    descriptors, source_bytes = verified_sources()
    values = _cell_recipes(descriptors) + _rowmass_recipes(descriptors)
    return dict(schema=SCHEMA, source_sha256=dict(LEDGER.SOURCE_BINDINGS),
                descriptors_sha256=LEDGER.DESCRIPTORS_SHA256, source_bytes=source_bytes,
                recipes=values, recipes_hash=digest(values), recipe_count=len(values),
                source_adapter_scope='audited divisor-cell state and two rowmass recipes only; full source adapter unavailable',
                universal_compiler_equivalence_formally_proved=False,
                finite_correspondence_is_universal_proof=False, **FLAGS)


def validate_recipe(recipe):
    """Reject altered formulas/domains/IDs against the reviewed source recipes."""
    if type(recipe) is not dict:
        raise ValueError('explicit bound source recipe')
    expected = next((r for r in recipes()['recipes'] if r['id'] == recipe.get('id')), None)
    if expected is None or recipe != expected:
        raise ValueError('recipe differs from audited fixed source definition')
    return True


def proof_tree(tree):
    """Translate the old exact floor-root spelling, retaining every argument."""
    if type(tree) is not list:
        return tree
    if tree and tree[0] == 'root':
        if len(tree) != 4:
            raise ValueError('exact legacy root arity')
        return ['scaled_root', 'floor', '1', str(F(tree[2], tree[3])), proof_tree(tree[1])]
    return [proof_tree(value) for value in tree]


def proof_context(recipe):
    return dict(integer_parameters=[dict(name=name, lower=1) for name in recipe['parameters']],
                functions=copy.deepcopy(recipe['functions']))


def produce_certificate(recipe, *, limits=None, deadline=None):
    import parametric_arithmetic_identity as P
    validate_recipe(recipe)
    producer = P.Producer(proof_context(recipe), source_bindings=LEDGER.SOURCE_BINDINGS,
                          recipe_ids=[recipe['id']], limits=limits, deadline=deadline)
    lhs = producer.from_tree(proof_tree(recipe['lhs']))
    rhs = producer.from_tree(proof_tree(recipe['rhs']))
    return producer.prove(lhs, rhs)
