"""Independent complete arithmetic reconstruction of primitive/state localizers.

Only checker modules are imported. Domains are enumerated separately at each
t; multipliers are accumulated forward, without the producer's suffix cache.
"""
import copy
from fractions import Fraction as F
from math import gcd
import check_cancellation_affine_storage as B
import check_cancellation_divisor_cells as C
import check_grouped_arithmetic as G

P = G.P
digest = B.I.digest
FLAGS = dict(global_bound_proved=False, RH_proved=False)
SPEC = dict(
    version='primitive-state-localizers-v1', base_program=B.SPEC,
    primitive_families=['unit', 'norm', 'prime_power', 'squarefree_zero',
                        'inverse_row', 'coprime_product', 'gcd_product'],
    regions=['parent', 'child'], atoms=copy.deepcopy(B.SPEC['atoms']), dimension=15,
    source_scale='N=4X-1', relation_domain='complete canonical primitive domains up to t',
    state_source='complete cancellation_affine_storage regional rows',
    group_form='sum_{t in region} U_i(t) R_f(t)',
    coefficient_sharing='one fixed signed coefficient per family, region and atom across every t and X',
    aggregation='equal primitive specs summed coefficientwise across every source t',
    primitive_order='grouped_arithmetic_templates order filtered to anchor<=t',
    formal_relation_constants=dict(unit='-1', norm='-SF(t)', prime_power='pi(t)',
                                   squarefree_zero='0', inverse_row='0',
                                   coprime_product='0', gcd_product='0'),
    formal_state_vector=copy.deepcopy(B.SPEC['constant_vector']),
    added_square_groups=0, added_relation_groups=210,
    formal_added_budget='O(X^2) for fixed signed coefficients',
    auxiliary_relation_groups='210 empty groups; new cubic coefficients zero',
    selection='all seven primitive families, both regions and all fifteen state atoms')


def additions():
    out = []
    for family in SPEC['primitive_families']:
        for region in SPEC['regions']:
            for i, atom in enumerate(SPEC['atoms']):
                d = dict(version=SPEC['version'], family='primitive_state_localizer',
                         primitive_family=family, region=region, atom_index=i,
                         atom=copy.deepcopy(atom), weight='one',
                         source_domain=SPEC['relation_domain'],
                         multiplier_source=SPEC['state_source'])
                out.append(dict(d, id=digest(d)))
    return dict(square=[], relation=out)


def descriptors():
    old, new = C.descriptors(), additions()
    return {k: old[k]+new[k] for k in old}


def gram_specs():
    return B.gram_specs()


def primitive_specs(t):
    """Canonical complete domains, constructed afresh at the given integer t."""
    P.integer(t)
    factors = {n: [[p, e] for p, e in sorted(P.factor(n).items())]
               for n in range(1, t+1)}
    out = {f: [] for f in SPEC['primitive_families']}
    out['unit'] = [dict(kind='unit')]
    for n in range(1, t+1):
        fac = factors[n]
        out['norm'].append(dict(kind='norm', n=n, factors=fac))
        if len(fac) == 1:
            out['prime_power'].append(dict(kind='prime_power', p=fac[0][0], e=fac[0][1]))
        if any(e > 1 for p, e in fac):
            out['squarefree_zero'].append(dict(kind='squarefree_zero', n=n))
        if n >= 2:
            out['inverse_row'].append(dict(kind='inverse_row', n=n))
    for a in range(1, t+1):
        for b in range(a, t+1):
            out['gcd_product'].append(dict(kind='gcd_product', a=a, b=b,
                                          factors_a=factors[a], factors_b=factors[b]))
            if a >= 2 and a*b <= t and gcd(a, b) == 1:
                out['coprime_product'].append(dict(kind='coprime_product', a=a, b=b))
    return out


def build_additions(X, *, blocks=None, max_horizon=80, max_operations=200000000,
                    max_terms=100000, max_coefficient_bits=4096):
    if any(type(v) is not int or v < 1 for v in
           (X, max_horizon, max_operations, max_terms, max_coefficient_bits)):
        raise ValueError('strict positive independent primitive-state limits')
    H = 4*X-1
    if H > max_horizon or 45*H**3+105*H**2 > max_operations:
        raise OverflowError('complete independent primitive-state preflight')
    limits = dict(max_horizon=max_horizon, max_operations=max_operations,
                  max_terms=max_terms, max_coefficient_bits=max_coefficient_bits)
    reference = B.build_blocks(X, **limits)['blocks']
    if blocks is None:
        blocks = reference
    if blocks != reference:
        raise ValueError('complete independent affine state source')
    used = 0

    def charge(n=1):
        nonlocal used
        used += n
        if used > max_operations:
            raise OverflowError('independent primitive-state work limit')

    def checked(poly):
        if len(poly) > max_terms:
            raise OverflowError('independent primitive-state terms')
        for q in poly.values():
            if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > max_coefficient_bits:
                raise OverflowError('independent primitive-state coefficient bits')
        return poly

    def add(a, b):
        charge(len(a)+len(b))
        out = dict(a)
        for m, q in b.items():
            value = out.get(m, F(0))+q
            if value:
                out[m] = value
            else:
                out.pop(m, None)
        return checked(out)

    sources, primitive_sources = {}, []
    cache = {}
    for t in range(X, H+1):
        full = primitive_specs(t)
        for family in SPEC['primitive_families']:
            specs = full[family]
            scalar = F(0)
            for spec in specs:
                key = digest(spec)
                if key not in cache:
                    cache[key] = G.relation(spec, 'mu', H)
                scalar += cache[key].get((), F(0))
                charge(1)
            row = dict(t=t, family=family, primitive_specs=specs,
                       source_count=len(specs), source_sha256=digest(specs),
                       formal_relation_constant=str(scalar), complete_source=True)
            sources[family, t] = row
            primitive_sources.append(row)
    multiplier_sources, states = [], {}
    for region in SPEC['regions']:
        ts = list(range(X, 2*X) if region == 'parent' else range(2*X, 4*X))
        for t, row in zip(ts, blocks['full_'+region]):
            states[region, t] = [checked(P.parse(p, t)) for p in row]
            charge(sum(map(len, row)))
            multiplier_sources.append(dict(region=region, t=t,
                                           state_sha256=digest(row),
                                           multiplier_sha256=list(map(digest, row)),
                                           complete_source=True))
    mult = {(r['region'], r['t']): r for r in multiplier_sources}
    groups, archive = [], []
    hash_work = 0
    for desc in additions()['relation']:
        family, region, i = desc['primitive_family'], desc['region'], desc['atom_index']
        ts = list(range(X, 2*X) if region == 'parent' else range(2*X, 4*X))
        multipliers = {}
        rows = []
        scalar = F(0)
        for t in ts:
            source = sources[family, t]
            state = states[region, t][i]
            for spec in source['primitive_specs']:
                key = digest(spec)
                multipliers[key] = add(multipliers.get(key, {}), state)
            scalar += state.get((), F(0))*F(source['formal_relation_constant'])
            rows.append(dict(t=t, primitive_source_count=source['source_count'],
                             primitive_specs_sha256=source['source_sha256'],
                             multiplier_sha256=mult[region, t]['multiplier_sha256'][i]))
        group = [dict(spec=copy.deepcopy(spec), multiplier=P.canonical(multipliers[digest(spec)]))
                 for spec in sources[family, ts[-1]]['primitive_specs']]
        sizes = {'unit': 2, 'norm': 2, 'prime_power': 2, 'squarefree_zero': 1,
                 'inverse_row': H, 'coprime_product': 2, 'gcd_product': 2}
        work = sum(len(r['multiplier'])*sizes[family] for r in group)
        polyhash = None
        if hash_work+work <= 2000000 and used+4*work <= max_operations:
            column = {}
            for row in group:
                p, q = P.parse(row['multiplier'], H), cache[digest(row['spec'])]
                charge(len(p)*len(q))
                column = add(column, P.multiply(p, q))
            if column.get((), F(0)) != scalar:
                raise ValueError('independent expanded/formal localizer constant mismatch')
            polyhash = digest(P.canonical(column))
            hash_work += work
        groups.append(group)
        archive.append(dict(descriptor=copy.deepcopy(desc), scales=ts, rows=rows,
                            source_count=sum(r['primitive_source_count'] for r in rows),
                            aggregated_spec_count=len(group), relation_group_sha256=digest(group),
                            polynomial_sha256=polyhash,
                            polynomial_hash_scope='complete exact expansion when bounded work is cheap',
                            formal_relation_scalar=str(scalar), complete_source=True))
    return dict(square_groups=[], relation_groups=groups, archive=archive,
                primitive_sources=primitive_sources, multiplier_sources=multiplier_sources,
                spec=copy.deepcopy(SPEC), construction_operations=used,
                arithmetic_sign_values_substituted=False, **FLAGS)


def build(program, X, **limits):
    if type(program) is not dict or program.get('target') != 'mu':
        raise ValueError('Mobius inverse-of-ones target only')
    bits = limits.get('max_coefficient_bits', 4096)
    if type(bits) is not int or bits < 1:
        raise ValueError('positive exact coefficient-bit limit')
    B.I.rational(program['C'], bits)
    out = B.build(program, X, **limits)
    serials = [out['instance']['lhs']]
    serials.extend(r['poly'] for g in out['instance']['square_groups'] for r in g)
    serials.extend(r['multiplier'] for g in out['instance']['relation_groups'] for r in g)
    for poly in serials:
        if len(poly) > limits.get('max_terms', 100000):
            raise OverflowError('independent retained source term limit')
        for row in poly:
            B.I.rational(row['c'], bits)
    extra = build_additions(X, blocks=out['gram_blocks'], **limits)
    out['instance']['relation_groups'].extend(extra['relation_groups'])
    ds = descriptors()
    out.update(square_ids=[d['id'] for d in ds['square']],
               relation_ids=[d['id'] for d in ds['relation']],
               dictionary_sha256=digest(ds), gram_program=copy.deepcopy(SPEC),
               primitive_state_spec=copy.deepcopy(SPEC), primitive_state_archive=extra['archive'],
               primitive_sources=extra['primitive_sources'], multiplier_sources=extra['multiplier_sources'],
               primitive_state_construction_operations=extra['construction_operations'],
               primitive_state_total_construction_operations=extra['construction_operations']+sum(
                   out.get(k, 0) for k in ('construction_cost', 'divisor_construction_operations',
                                           'cell_construction_operations', 'gram_program_operations')))
    return out


def auxiliary():
    out = B.auxiliary()
    out['instance']['relation_groups'].extend([[] for _ in range(210)])
    out['gamma_coefficients'].extend(['0']*210)
    ds = descriptors()
    out.update(square_ids=[d['id'] for d in ds['square']],
               relation_ids=[d['id'] for d in ds['relation']],
               dictionary_sha256=digest(ds), gram_program=copy.deepcopy(SPEC))
    return out


def check_builder(program, X, output, **limits):
    expected = build(program, X, **limits)
    ignored = {'construction_operations', 'gram_program_operations', 'cell_construction_operations',
               'construction_cost', 'primitive_state_construction_operations',
               'primitive_state_total_construction_operations'}
    if type(output) is not dict or set(output)-ignored != set(expected)-ignored:
        raise ValueError('primitive-state builder fields')
    for key in set(expected)-ignored:
        if key == 'primitive_state_archive':
            given = output[key]
            if type(given) is not list or len(given) != 210:
                raise ValueError('all 210 primitive-state archives')
            for actual, wanted in zip(given, expected[key]):
                if type(actual) is not dict or set(actual) != set(wanted):
                    raise ValueError('complete primitive-state archive schema')
                for field in wanted:
                    if field == 'polynomial_sha256' and actual[field] is None:
                        continue
                    if actual[field] != wanted[field]:
                        raise ValueError('independent primitive-state archive '+field)
        elif digest(output[key]) != digest(expected[key]):
            raise ValueError('independently rebuilt primitive-state source '+key)
    return dict(verified=True, complete_sources_verified=True, complete_primitive_domains_verified=True,
                all_fifteen_state_multipliers_verified=True,
                producer_operation_count_independently_verified=False, **FLAGS)


def scalar_budget(relation_weights, X, *, additions_data=None, **limits):
    if type(relation_weights) is not list or len(relation_weights) != 210:
        raise ValueError('all 210 added shared signed weights')
    weights = list(map(B.I.rational, relation_weights))
    # An optional producer archive is evidence to audit, never a scalar oracle.
    data = build_additions(X, **limits)
    if additions_data is not None:
        for key in ('relation_groups', 'primitive_sources', 'multiplier_sources'):
            if additions_data.get(key) != data[key]:
                raise ValueError('independent added scalar sources '+key)
        if len(additions_data.get('archive', [])) != 210 or any(
                a.get('formal_relation_scalar') != b['formal_relation_scalar']
                for a, b in zip(additions_data['archive'], data['archive'])):
            raise ValueError('independent added scalar ledger')
    ledger = [dict(group=d['id'], coefficient=str(w), formal_scalar=a['formal_relation_scalar'],
                   contribution=str(w*F(a['formal_relation_scalar'])))
              for d, w, a in zip(additions()['relation'], weights, data['archive'])]
    return dict(total=str(sum((F(r['contribution']) for r in ledger), F(0))),
                ledger=ledger, scope='formal exact added scalar extraction; fixed-coefficient O(X^2)', **FLAGS)


def extract_scalar_budget(instance, weights, grams, X):
    """Full constant ledger; polynomial matching remains a separate obligation."""
    if type(weights) is not dict or set(weights) != {'square_weights', 'relation_weights'}:
        raise ValueError('complete shared scalar weights')
    sw = list(map(B.I.rational, weights['square_weights']))
    rw = list(map(B.I.rational, weights['relation_weights']))
    if any(w < 0 for w in sw):
        raise ValueError('nonnegative square weights')
    ds = descriptors()
    if len(sw) != len(ds['square']) or len(rw) != len(ds['relation']):
        raise ValueError('complete old and added scalar group coverage')
    lhs, squares, relations = B.I.scalar_columns(instance, sw, rw)
    ledger = []
    for kind, coeffs, cols in [('square', sw, squares), ('relation', rw, relations)]:
        for d, w, col, group in zip(ds[kind], coeffs, cols, instance[kind+'_groups']):
            if kind == 'square':
                scalar = sum((B.I.rational(row['weight'])*
                              P.parse(row['poly'], instance['horizon']).get((), F(0))**2
                              for row in group), F(0))
            else:
                scalar = sum((P.parse(row['multiplier'], instance['horizon']).get((), F(0))*
                              G.relation(row['spec'], instance['target'], instance['horizon']).get((), F(0))
                              for row in group), F(0))
            if w and scalar != col.get((), F(0)):
                raise ValueError('expanded scalar coefficient mismatch')
            ledger.append(dict(kind=kind, group=d['id'], coefficient=str(w),
                               formal_scalar=str(scalar), contribution=str(w*scalar)))
    scalar = sum((F(r['contribution']) for r in ledger), F(0))
    added = scalar_budget(weights['relation_weights'][-210:], X)
    if any(a['formal_scalar'] != b['formal_scalar'] for a, b in zip(ledger[-210:], added['ledger'])):
        raise ValueError('independent per-group arithmetic scalar mismatch')
    if sum((F(r['contribution']) for r in ledger[-210:]), F(0)) != F(added['total']):
        raise ValueError('independent full-column and arithmetic scalar mismatch')
    matrix = B.scalar_budget(grams, X)
    budget = scalar+F(matrix['total'])
    target = lhs.get((), F(0))
    return dict(B=str(budget), D=str(target), scalar_slack=str(target-budget),
                original_scalar_budget=str(scalar-F(added['total'])),
                added_relation_scalar_budget=added, scalar_ledger=ledger,
                matrix_budget=matrix, nonconstant_identity_verified=False, **FLAGS)


def coefficient_system(instances, gram_blocks, storage_blocks, specs=None):
    return B.coefficient_system(instances, gram_blocks, storage_blocks, specs)


def _translate_result(result):
    out = copy.deepcopy(result)
    if 'grammar_hash' in out:
        if out['grammar_hash'] != digest(SPEC):
            raise ValueError('primitive-state grammar binding')
        out['grammar_hash'] = digest(B.SPEC)
    return out


def verify_primal(instances, gram_blocks, storage_blocks, specs, result):
    return B.verify_primal(instances, gram_blocks, storage_blocks, specs, _translate_result(result))


def verify_dual(instances, gram_blocks, storage_blocks, specs, result):
    return B.verify_dual(instances, gram_blocks, storage_blocks, specs, _translate_result(result))
