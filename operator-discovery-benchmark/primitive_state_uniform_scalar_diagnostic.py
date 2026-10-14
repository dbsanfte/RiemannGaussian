"""Optional exact scalar readiness for the published full15 primitive grammar.

This does not check candidate feasibility or the universal nonconstant identity.
The rowmass gate is a sufficient route, never a necessary RH condition.
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re

import cancellation_primitive_state_localizers as LANGUAGE

SCHEMA = 'primitive-state-uniform-scalar-diagnostic-v1'
DESCRIPTORS_SHA256 = '205f229c5ce055a8599d91b83bfb22a5ce71054ad490787fb9a951c20f6471be'
# The scalar ledger was derived for these compiler sources. A later grammar
# needs a new reviewed ledger; keeping descriptor names alone is insufficient.
SOURCE_BINDINGS = {
    'arithmetic_cycle_language.py': '08524016771c787269ebbf811ec52275261d1d51bfd6ed6096c9550db6723688',
    'cancellation_affine_storage.py': 'cd67388de011a0faaa962de0973381ccda8c4225ee19e9a43f34715a46882da2',
    'cancellation_anchored_storage.py': '2086fb696741386228cc2cb9e673702437f7b3a5bb6d6dfbc56445f350184883',
    'cancellation_arithmetic_language.py': '9b598c772b9d4159768f7a48371a06ab8a53f2e4a5cde3866b049618d27d37b9',
    'cancellation_arithmetic_templates.py': 'c06877b9b03c18bd7e4965c71632f9899680a06641d0ac0781a4e0b32da2c456',
    'cancellation_cell_gram_program.py': '10f861d584c24205449c868c8e350b01797f662eb6b81fa5f713975993836823',
    'cancellation_complete_gram_program.py': 'b329b4d05b9d54da01ded94e363277ed6af88f3cf4c4d22b3a0193053a26191c',
    'cancellation_cubic_gate.py': '0c8773367650e80cba67fa224df4be27eed9c4f8084e5e29ec548ac5ad1b3bd4',
    'cancellation_divisor_cell_language.py': 'c748bb2786d6e4e0adebe2603339e79dede4d47941771b606ff415fe69b56f85',
    'cancellation_divisor_localizer_language.py': '835f547ef39aaa1d82a2b0a658d25318928c8560a485d735f070c1e03f218f73',
    'cancellation_factor_blocks.py': '364c5443fc9c02d8f84798f725f69b5e9253404f88d706bee7d52a8d271fd0c2',
    'cancellation_factor_search_language.py': 'b157d80433001fad069528f5c878120b2927e19419234b8223b1d2b16815ac46',
    'cancellation_gram_language.py': '5d62e47291be950b6c30e3ef9146c2e875683fb36b1602544611adb7fcd09584',
    'cancellation_joint_gram_program.py': 'ec3747ad827960eee1b010b09a8ccbe00de3dfc3a619d10bb8c2d5ab60a211b6',
    'cancellation_primitive_state_localizers.py': '7ffc9ee2498db6b811a69b037849d67c3022941013ed1d57a7537d7cb517d670',
    'cancellation_shared_gram_language.py': '51963efcad6518a9f0636e121ad2f46f80f243d526004c48cc1790af694ec7f5',
    'grouped_arithmetic_language.py': 'aafa824b462477852df9ceca1cdf7fb153b17ec4184575e84030dac07ac9c9df',
    'grouped_arithmetic_templates.py': '9869beef394818011885fa34521467b86ccb530d3c8bcca654906ccaed4f2b8b',
}
Z = [F(1)] + [F(0)] * 5 + [F(-1, 2)] * 9
U = [F(1), F(1), F(0), F(0), F(1)] + [F(0)] * 10
FLAGS = dict(global_bound_proved=False, RH_proved=False,
             global_nonconstant_identity_proved=False, finite_candidate_checked=False)
MAX_DERIVED_BITS = 16384


def digest(value):
    raw = json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()
    return hashlib.sha256(raw).hexdigest()


def _rational(value):
    if type(value) is str:
        if len(value) > 2470 or not re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', value):
            raise ValueError('bounded canonical rational coordinate')
        q = F(value)
        if str(q) != value:
            raise ValueError('canonical reduced rational coordinate')
    elif type(value) in (int, F):
        q = F(value)
    else:
        raise ValueError('exact rational coordinates only')
    if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > 4096:
        raise OverflowError('coordinate bit limit')
    return q


def _grammar():
    root = Path(LANGUAGE.__file__).resolve().parent
    byte_count = 0
    for name, expected in SOURCE_BINDINGS.items():
        path = root / name
        size = path.stat().st_size
        byte_count += size
        if byte_count > 1048576:
            raise OverflowError('bounded scalar-ledger source reads')
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('unsupported changed scalar-ledger source: ' + name)
    descriptors = LANGUAGE.descriptors()
    if digest(descriptors) != DESCRIPTORS_SHA256:
        raise ValueError('unsupported scalar-ledger descriptors')
    return descriptors, byte_count


def _bounded(value):
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_DERIVED_BITS:
        raise OverflowError('derived scalar-ledger bit limit')
    return value


def _sum(values):
    total = F(0)
    for value in values:
        total = _bounded(total + value)
    return total


def _quadratic(upper, vector):
    return _sum(q * vector[i] * vector[j] * (1 if i == j else 2)
                for q, (i, j) in zip(upper, ((i, j) for i in range(15) for j in range(i, 15))))


def analyze(candidate):
    """Return exact readiness/majorant data, without imposing a search constraint.

    M bounds |B0(X)|/X^2 for X>=1 when the four rowmass checks pass. B0 is
    the formal scalar of the structural body, excluding the critical constant
    square and instance slacks. Signed/negative squares can still be diagnosed:
    absolute values keep this scalar bound valid, but do not license positivity.
    """
    if type(candidate) is not list or len(candidate) != 1957:
        raise ValueError('complete original 1957-coordinate vector')
    x = [_rational(q) for q in candidate]
    descriptors, source_bytes = _grammar()
    squares, relations = descriptors['square'], descriptors['relation']
    beta = [_bounded(x[366 + 2*j] - x[367 + 2*j]) for j in range(613)]
    gate = []
    for family in ('norm', 'prime_power'):
        selected = {d['region']: (j, d) for j, d in enumerate(relations)
                    if d['family'] == family and d.get('multiplier') == 'one'
                    and d['weight'] == 'child_rowmass'}
        if set(selected) != {'all', 'head', 'tail'}:
            raise ValueError('complete rowmass partition descriptors')
        a = beta[selected['all'][0]]
        head, tail = _bounded(a + beta[selected['head'][0]]), _bounded(a + beta[selected['tail'][0]])
        gate.append(dict(family=family,
                         descriptors={r: dict(index=j, id=d['id'], beta=str(beta[j]))
                                      for r, (j, d) in selected.items()},
                         effective_head=str(head), effective_tail=str(tail),
                         entire_relation_partition_cancels=head == tail == 0))
    ready = all(row['entire_relation_partition_cancels'] for row in gate)
    parts = dict(base=F(0), cell_squares=F(0), cell_relations=F(0), matrices=F(0), primitive=F(0))
    ledger = []

    def add(kind, value, **entry):
        if value < 0:
            raise ValueError('nonnegative scalar majorant term')
        parts[kind] = _bounded(parts[kind] + value)
        if value:
            ledger.append(dict(component=kind, majorant=str(value), **entry))

    for j, d in enumerate(relations[:195]):
        if d['multiplier'] != 'one':
            continue
        if d['family'] in ('norm', 'prime_power') and d['weight'] != 'child_rowmass':
            add('base', {'one': 4, 'X': 4, 'defect_kernel': 8}[d['weight']] * abs(beta[j]),
                index=j, id=d['id'], beta=str(beta[j]))
        elif d['family'] == 'unit':
            add('base', abs(beta[j]), index=j, id=d['id'], beta=str(beta[j]))
    for j, d in enumerate(squares):
        if d['family'] == 'divisor_cell_square':
            k = {'parent': 1, 'child': 2}[d['region']]
            add('cell_squares', k * abs(x[j]) / 4, index=j, id=d['id'], weight=str(x[j]))
    for j, d in enumerate(relations):
        if d['family'] == 'divisor_cell_relation':
            k = {'parent': 1, 'child': 2}[d['region']]
            c = {'one': F(-1), 'prefix': F(0), 'contrast': F(1, 2), 'normalization': F(1)}[d['form']]
            add('cell_relations', abs(k*c*beta[j]), index=j, id=d['id'], beta=str(beta[j]))
    Gc, Gp, K = x[1597:1717], x[1717:1837], x[1837:1957]
    C, H = [_bounded(a+b) for a, b in zip(Gc, K)], [_bounded(a+4*b) for a, b in zip(Gp, Gc)]
    matrix_coefficient = _bounded(_quadratic(H, Z) - 2*_quadratic(C, Z))
    add('matrices', abs(matrix_coefficient), coefficient=str(matrix_coefficient), formula='z^T H z - 2 z^T C z')
    primitive = []
    for family in LANGUAGE.SPEC['primitive_families']:
        for region in ('parent', 'child'):
            selected = [(j, d) for j, d in enumerate(relations)
                        if d['family'] == 'primitive_state_localizer'
                        and d['primitive_family'] == family and d['region'] == region]
            if [d['atom_index'] for j, d in selected] != list(range(15)):
                raise ValueError('complete primitive scalar atom group')
            tau = _sum(Z[d['atom_index']] * beta[j] for j, d in selected)
            k, ell = {'parent': (F(1), F(3, 2)), 'child': (F(2), F(6))}[region]
            bound = (k if family == 'unit' else ell if family in ('norm', 'prime_power') else F(0)) * abs(tau)
            primitive.append(dict(family=family, region=region, tau=str(tau), majorant=str(bound),
                                  descriptor_indices=[j for j, d in selected], descriptor_ids=[d['id'] for j, d in selected]))
            add('primitive', bound, family=family, region=region, tau=str(tau))
    M = _sum(parts.values())
    return dict(schema=SCHEMA, candidate_hash=digest(list(map(str, x))),
                descriptors_sha256=DESCRIPTORS_SHA256, source_sha256=SOURCE_BINDINGS,
                source_bytes=source_bytes, charged_work_reserve=2000000,
                coordinate_bit_limit=4096, derived_bit_limit=MAX_DERIVED_BITS,
                rowmass_gate=gate, gate_is_optional_sufficient=True, imposed_on_search=False,
                elementary_scalar_ready=ready, majorant_M=str(M) if ready else None,
                non_rowmass_majorant_M=str(M), components={k: str(v) for k, v in parts.items()},
                ledger=ledger, primitive_scalar_groups=primitive,
                excluded_constant_square=dict(index=0, id=squares[0]['id'], weight=str(x[0])),
                instance_slacks_excluded=True, formal_matrix_scalar_coefficient=str(matrix_coefficient),
                canonical_anchored_initial_cost=str(_bounded(1 + _quadratic(C, U))),
                initial_cost_nonnegative_not_verified=True,
                scalar_bound_scope='|B0(X)| <= M X^2 for every integer X>=1 if the rowmass gate passes',
                unresolved_obligations=([] if ready else ['weighted norm/prime rowmass budget']) +
                    ['nonnegative square and PSD requirements', 'all-scale nonconstant coefficient identity',
                     'ordinary-zeta energy recovery bridge premises'],
                conditional_innovation='Delta(S_R)(X) <= M X^2',
                conditional_dyadic_energy='E(X) <= X^2 [S_R(1) + (M/4) log_2 X]',
                conditional_conclusions_require_all_listed_obligations=True, **FLAGS)
