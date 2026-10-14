"""Complete primitive-relation closure against every affine regional state.

All coefficients are fixed shared signed group weights.  Primitive sources are
factor-certified domains, never evaluations of a Mobius sign table.  Equal
primitive specifications are aggregated only after complete source archiving.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import gcd
import copy

import cancellation_affine_storage as BASE
import cancellation_divisor_cell_language as SCALAR
import grouped_arithmetic_language as L

digest = SCALAR.digest
FLAGS = dict(global_bound_proved=False, RH_proved=False)
SPEC = dict(
    version='primitive-state-localizers-v1', base_program=BASE.SPEC,
    primitive_families=['unit', 'norm', 'prime_power', 'squarefree_zero',
                        'inverse_row', 'coprime_product', 'gcd_product'],
    regions=['parent', 'child'], atoms=copy.deepcopy(BASE.SPEC['atoms']), dimension=15,
    source_scale='N=4X-1', relation_domain='complete canonical primitive domains up to t',
    state_source='complete cancellation_affine_storage regional rows',
    group_form='sum_{t in region} U_i(t) R_f(t)',
    coefficient_sharing='one fixed signed coefficient per family, region and atom across every t and X',
    aggregation='equal primitive specs summed coefficientwise across every source t',
    primitive_order='grouped_arithmetic_templates order filtered to anchor<=t',
    formal_relation_constants=dict(unit='-1', norm='-SF(t)', prime_power='pi(t)',
                                   squarefree_zero='0', inverse_row='0',
                                   coprime_product='0', gcd_product='0'),
    formal_state_vector=copy.deepcopy(BASE.SPEC['constant_vector']),
    added_square_groups=0, added_relation_groups=210,
    formal_added_budget='O(X^2) for fixed signed coefficients',
    auxiliary_relation_groups='210 empty groups; new cubic coefficients zero',
    selection='all seven primitive families, both regions and all fifteen state atoms')


def additions():
    groups = []
    for family in SPEC['primitive_families']:
        for region in SPEC['regions']:
            for i, atom in enumerate(SPEC['atoms']):
                desc = dict(version=SPEC['version'], family='primitive_state_localizer',
                            primitive_family=family, region=region, atom_index=i,
                            atom=copy.deepcopy(atom), weight='one',
                            source_domain=SPEC['relation_domain'],
                            multiplier_source=SPEC['state_source'])
                groups.append(dict(desc, id=digest(desc)))
    return dict(square=[], relation=groups)


def descriptors():
    old, extra = SCALAR.descriptors(), additions()
    return {kind: old[kind] + extra[kind] for kind in old}


def gram_specs():
    return BASE.gram_specs()


def _limits(X, max_horizon, max_operations, max_terms, max_coefficient_bits):
    if any(type(v) is not int or v < 1 for v in
           (X, max_horizon, max_operations, max_terms, max_coefficient_bits)):
        raise ValueError('strict positive primitive-state limits')
    H = 4 * X - 1
    # Complete pair sources, all state entries, and aggregation/hash work are
    # bounded before generation. Runtime charging also covers exact expansions.
    if H > max_horizon or 45 * H ** 3 + 105 * H ** 2 > max_operations:
        raise OverflowError('complete primitive-state preflight')
    return H


def _anchor(spec):
    kind = spec['kind']
    if kind == 'unit':
        return 1
    if kind == 'prime_power':
        return spec['p'] ** spec['e']
    if kind == 'coprime_product':
        return spec['a'] * spec['b']
    if kind == 'gcd_product':
        return spec['b']
    return spec['n']


@lru_cache(maxsize=4)
def _state_source(X, max_horizon, max_operations, max_terms, max_coefficient_bits):
    # Cached values stay private. Source work is charged on every construction,
    # including a cache hit; caching does not weaken any declared limit.
    return BASE.build_blocks(X, max_horizon=max_horizon, max_operations=max_operations,
                             max_terms=max_terms, max_coefficient_bits=max_coefficient_bits)


def build_additions(X, *, blocks=None, max_horizon=80, max_operations=200000000,
                    max_terms=100000, max_coefficient_bits=4096):
    H = _limits(X, max_horizon, max_operations, max_terms, max_coefficient_bits)
    used = 0

    def charge(n):
        nonlocal used
        used += n
        if used > max_operations:
            raise OverflowError('primitive-state construction work')

    def checked(p):
        if len(p) > max_terms:
            raise OverflowError('primitive-state polynomial terms')
        if any(max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > max_coefficient_bits
               for q in p.values()):
            raise OverflowError('primitive-state coefficient bits')
        return p

    def dump(p):
        charge(len(p))
        return L.dump_poly(checked(p))

    def add(p, q):
        charge(len(p) + len(q))
        return checked(L.add(p, q))

    data = _state_source(X, max_horizon, max_operations, max_terms, max_coefficient_bits)
    if blocks is None:
        blocks = data['blocks']
    elif blocks != data['blocks']:
        raise ValueError('exact complete affine regional source required')
    charge(data['construction_operations'])
    if type(blocks) is not dict or set(blocks) != {'full_child', 'full_parent'}:
        raise ValueError('both complete affine regional state sources required')
    states, multiplier_sources, suffix = {}, [], {}
    for region in SPEC['regions']:
        ts = list(range(X, 2 * X) if region == 'parent' else range(2 * X, 4 * X))
        rows = blocks['full_' + region]
        if type(rows) is not list or len(rows) != len(ts):
            raise ValueError('complete regional state coverage')
        parsed = []
        for t, row in zip(ts, rows):
            if type(row) is not list or len(row) != 15:
                raise ValueError('all fifteen affine state atoms required')
            state = []
            for serial in row:
                p = checked(L.load_poly(serial))
                if any(a > t for m in p for a in m) or L.dump_poly(p) != serial:
                    raise ValueError('canonical state source in regional horizon')
                charge(len(p))
                state.append(p)
            if state[0] != L.constant(1):
                raise ValueError('constant unit state atom required')
            parsed.append(state)
            multiplier_sources.append(dict(region=region, t=t,
                                           state_sha256=digest(row),
                                           multiplier_sha256=[digest(p) for p in row],
                                           complete_source=True))
        states[region] = parsed
        # For a primitive admitted at anchor a, its complete multiplier is the
        # sum of U_i(t) for every regional t >= a. Cache these sums once.
        running = [{} for _ in range(15)]
        for t, state in reversed(list(zip(ts, parsed))):
            running = [add(p, q) for p, q in zip(running, state)]
            suffix[region, t] = running

    factors = {}
    for n in range(1, H + 1):
        charge(n)
        factors[n] = L.factor_witness(n, max_n=max_horizon, max_operations=max_operations)
    specs = {family: [] for family in SPEC['primitive_families']}
    specs['unit'] = [dict(kind='unit')]
    for n in range(1, H + 1):
        specs['norm'].append(dict(kind='norm', n=n, factors=factors[n]))
        if len(factors[n]) == 1:
            p, e = factors[n][0]
            specs['prime_power'].append(dict(kind='prime_power', p=p, e=e))
        if any(e > 1 for p, e in factors[n]):
            specs['squarefree_zero'].append(dict(kind='squarefree_zero', n=n))
        if n >= 2:
            specs['inverse_row'].append(dict(kind='inverse_row', n=n))
    for a in range(1, H + 1):
        for b in range(a, H + 1):
            charge(1)
            specs['gcd_product'].append(dict(kind='gcd_product', a=a, b=b,
                                              factors_a=factors[a], factors_b=factors[b]))
            if a >= 2 and a * b <= H and gcd(a, b) == 1:
                specs['coprime_product'].append(dict(kind='coprime_product', a=a, b=b))
    primitive_sources, sources = [], {}
    for t in range(X, H + 1):
        sf = sum(all(e == 1 for p, e in factors[n]) for n in range(1, t + 1))
        pi = sum(factors[n] == [[n, 1]] for n in range(2, t + 1))
        for family in SPEC['primitive_families']:
            charge(len(specs[family]))
            full = [s for s in specs[family] if _anchor(s) <= t]
            scalar = {'unit': -1, 'norm': -sf, 'prime_power': pi}.get(family, 0)
            source = dict(t=t, family=family, primitive_specs=full,
                          source_count=len(full), source_sha256=digest(full),
                          formal_relation_constant=str(scalar), complete_source=True)
            primitive_sources.append(source)
            sources[family, t] = source

    groups, archive = [], []
    multipliers = {(r['region'], r['t']): r for r in multiplier_sources}
    z = list(map(F, SPEC['formal_state_vector']))
    polynomial_hash_work = 0
    relation_cache = {}
    for desc in additions()['relation']:
        family, region, i = desc['primitive_family'], desc['region'], desc['atom_index']
        ts = list(range(X, 2 * X) if region == 'parent' else range(2 * X, 4 * X))
        group, rows = [], []
        for spec in sources[family, ts[-1]]['primitive_specs']:
            multiplier = suffix[region, max(ts[0], _anchor(spec))][i]
            group.append(dict(spec=copy.deepcopy(spec), multiplier=dump(multiplier)))
        for t in ts:
            source = sources[family, t]
            rows.append(dict(t=t, primitive_source_count=source['source_count'],
                             primitive_specs_sha256=source['source_sha256'],
                             multiplier_sha256=multipliers[region, t]['multiplier_sha256'][i]))
        scalar = z[i] * sum((F(sources[family, t]['formal_relation_constant']) for t in ts), F(0))
        # Polynomial hashes are optional and cost bounded, independently of
        # arithmetic answers. Keep complete native groups even when omitted.
        relation_sizes = {'unit': 2, 'norm': 2, 'prime_power': 2,
                          'squarefree_zero': 1, 'inverse_row': H,
                          'coprime_product': 2, 'gcd_product': 2}
        work = sum(len(term['multiplier']) * relation_sizes[family] for term in group)
        polynomial_sha256 = None
        if polynomial_hash_work + work <= 2000000 and used + 4 * work <= max_operations:
            total = {}
            for term in group:
                multiplier = L.load_poly(term['multiplier'])
                key = digest(term['spec'])
                if key not in relation_cache:
                    charge(2 * H)
                    relation_cache[key] = L.relation(term['spec'], 'mu', H,
                                                     max_operations=max_operations,
                                                     max_horizon=max_horizon)
                relation = relation_cache[key]
                charge(len(multiplier) * len(relation))
                product = checked(L.mul(multiplier, relation, max_terms=max_terms,
                                        max_operations=max_operations))
                charge(len(product))
                for monomial, value in product.items():
                    value += total.get(monomial, F(0))
                    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > max_coefficient_bits:
                        raise OverflowError('primitive-state expanded coefficient bits')
                    if value:
                        total[monomial] = value
                    else:
                        total.pop(monomial, None)
                    if len(total) > max_terms:
                        raise OverflowError('primitive-state expanded polynomial terms')
            polynomial_sha256 = digest(dump(total))
            polynomial_hash_work += work
        groups.append(group)
        archive.append(dict(descriptor=copy.deepcopy(desc), scales=ts, rows=rows,
                            source_count=sum(r['primitive_source_count'] for r in rows),
                            aggregated_spec_count=len(group), relation_group_sha256=digest(group),
                            polynomial_sha256=polynomial_sha256,
                            polynomial_hash_scope='complete exact expansion when bounded work is cheap',
                            formal_relation_scalar=str(scalar), complete_source=True))
    return dict(square_groups=[], relation_groups=groups, archive=archive,
                primitive_sources=primitive_sources, multiplier_sources=multiplier_sources,
                spec=copy.deepcopy(SPEC), construction_operations=used,
                arithmetic_sign_values_substituted=False, **FLAGS)


def build(program, X, *, max_horizon=80, max_operations=200000000,
          max_terms=100000, max_coefficient_bits=4096):
    _limits(X, max_horizon, max_operations, max_terms, max_coefficient_bits)
    if type(program) is not dict or program.get('target') != 'mu':
        raise ValueError('Mobius inverse-of-ones target only')
    C = program.get('C')
    if type(C) not in (str, int, F):
        raise ValueError('exact critical-budget coefficient required')
    if type(C) is str and len(C) > 2 * max_coefficient_bits + 3:
        raise OverflowError('critical-budget rational input text')
    coefficient = F(C)
    if max(abs(coefficient.numerator).bit_length(), coefficient.denominator.bit_length()) > max_coefficient_bits:
        raise OverflowError('critical-budget coefficient bits')
    limits = dict(max_horizon=max_horizon, max_operations=max_operations,
                  max_terms=max_terms, max_coefficient_bits=max_coefficient_bits)
    out = BASE.build(program, X, **limits)
    original_operations = sum(out.get(key, 0) for key in
                              ('construction_cost', 'divisor_construction_operations',
                               'cell_construction_operations', 'gram_program_operations'))
    # The frozen scalar builders have several different historic bit limits.
    # Apply this producer's declared limits to every retained source as well.
    serials = [out['instance']['lhs']]
    serials.extend(term['poly'] for group in out['instance']['square_groups'] for term in group)
    serials.extend(term['multiplier'] for group in out['instance']['relation_groups'] for term in group)
    for serial in serials:
        original_operations += len(serial)
        if original_operations > max_operations:
            raise OverflowError('complete retained-source validation work')
        if len(serial) > max_terms:
            raise OverflowError('retained-source polynomial terms')
        for term in serial:
            q = F(term['c'])
            if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > max_coefficient_bits:
                raise OverflowError('retained-source coefficient bits')
    remaining = max_operations - original_operations
    if remaining < 1:
        raise OverflowError('complete primitive-state combined construction work')
    extra = build_additions(X, blocks=out['gram_blocks'],
                            **dict(limits, max_operations=remaining))
    out['instance']['relation_groups'].extend(extra['relation_groups'])
    ds = descriptors()
    out.update(square_ids=[d['id'] for d in ds['square']],
               relation_ids=[d['id'] for d in ds['relation']],
               dictionary_sha256=digest(ds), gram_program=copy.deepcopy(SPEC),
               primitive_state_spec=copy.deepcopy(SPEC),
               primitive_state_archive=extra['archive'],
               primitive_sources=extra['primitive_sources'],
               multiplier_sources=extra['multiplier_sources'],
               primitive_state_construction_operations=extra['construction_operations'],
               primitive_state_total_construction_operations=original_operations + extra['construction_operations'])
    return out


def auxiliary():
    out = BASE.auxiliary()
    out['instance']['relation_groups'].extend([[] for _ in additions()['relation']])
    out['gamma_coefficients'].extend(['0'] * 210)
    ds = descriptors()
    out.update(square_ids=[d['id'] for d in ds['square']],
               relation_ids=[d['id'] for d in ds['relation']],
               dictionary_sha256=digest(ds), gram_program=copy.deepcopy(SPEC))
    return out


def scalar_budget(relation_weights, X, *, additions_data=None, **limits):
    """Exact added formal scalar ledger; signed coefficients are unrestricted."""
    if type(relation_weights) is not list or len(relation_weights) != 210:
        raise ValueError('all 210 exact shared added relation coefficients required')
    if type(X) is not int or X < 1:
        raise ValueError('positive strict scalar-budget scale')
    bits = limits.get('max_coefficient_bits', 4096)
    if type(bits) is not int or bits < 1:
        raise ValueError('strict positive coefficient bit limit')
    weights = []
    for value in relation_weights:
        if type(value) not in (str, int, F):
            raise ValueError('exact signed relation coefficients required')
        if type(value) is str:
            if len(value) > 2 * bits + 3:
                raise OverflowError('scalar-budget rational input text')
            if not value or any(c not in '-0123456789/' for c in value):
                raise ValueError('canonical scalar-budget rational required')
        q = F(value)
        if type(value) is str and str(q) != value:
            raise ValueError('canonical scalar-budget rational required')
        if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > bits:
            raise OverflowError('scalar-budget coefficient bits')
        weights.append(q)
    data = build_additions(X, **limits) if additions_data is None else additions_data
    if len(data['archive']) != 210:
        raise ValueError('complete added scalar source required')
    for desc, row in zip(additions()['relation'], data['archive']):
        region = desc['region']
        ts = list(range(X, 2 * X) if region == 'parent' else range(2 * X, 4 * X))
        if row['descriptor'] != desc or row['scales'] != ts:
            raise ValueError('scalar-budget descriptor and complete scale binding')
    ledger = [dict(group=desc['id'], coefficient=str(w),
                   formal_scalar=row['formal_relation_scalar'],
                   contribution=str(w * F(row['formal_relation_scalar'])))
              for desc, w, row in zip(additions()['relation'], weights, data['archive'])]
    return dict(total=str(sum((F(row['contribution']) for row in ledger), F(0))),
                ledger=ledger, scope='formal exact added scalar extraction; fixed-coefficient O(X^2)',
                **FLAGS)
