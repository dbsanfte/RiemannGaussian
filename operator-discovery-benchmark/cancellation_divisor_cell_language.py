"""Shared complete divisor-cell couplings; no observed arithmetic responses.

Every rational cut and integer weight program in SPEC is retained.  Partial
channels keep the full complement, and primitive inverse closures are summed
without independently fitted index coefficients.
"""
from fractions import Fraction as F
import hashlib
import json
import grouped_arithmetic_language as L
import cancellation_divisor_localizer_language as BASE
from cancellation_factor_blocks import floor_scaled_power

SPEC = dict(version='divisor-cells-v1', regions=['parent', 'child'],
            thetas=['1/3', '1/2', '2/3'], powers=[-1, 0, 1],
            square_forms=['contrast', 'prefix_plus', 'prefix_minus'],
            relation_forms=['one', 'prefix', 'contrast', 'normalization'],
            source_domain='all 1<=a<=t, d|a; inside and complete complement',
            partition='d<=floor(t^theta)', normalizer='unit_constant',
            weights='a^power', source_scale='N=4X-1')


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()).hexdigest()


def additions():
    out = dict(square=[], relation=[])
    for region in SPEC['regions']:
        for theta in SPEC['thetas']:
            for power in SPEC['powers']:
                common = {k: SPEC[k] for k in ['version', 'source_domain', 'partition', 'normalizer', 'weights', 'source_scale']}
                common.update(region=region, theta=theta, power=power)
                for kind in ['square', 'relation']:
                    for form in SPEC[kind + '_forms']:
                        d = dict(common, family='divisor_cell_' + kind, form=form)
                        out[kind].append(dict(d, id=digest(d)))
    return out


def descriptors():
    old, extra = BASE.descriptors(), additions()
    return {k: old[k] + extra[k] for k in old}


def build_additions(X, *, max_horizon=80, max_operations=200000000,
                    max_terms=100000, max_coefficient_bits=4096):
    for v in [X, max_horizon, max_operations, max_terms, max_coefficient_bits]:
        if type(v) is not int or v < 1:
            raise ValueError('strict positive limits')
    H = 4 * X - 1
    if H > max_horizon or 18 * H ** 2 > max_operations:
        raise OverflowError('complete divisor-cell preflight')
    used = 0

    def charge(n):
        nonlocal used
        used += n
        if used > max_operations:
            raise OverflowError('divisor-cell construction work')

    def checked(p):
        if len(p) > max_terms:
            raise OverflowError('divisor-cell polynomial terms')
        if any(max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > max_coefficient_bits for q in p.values()):
            raise OverflowError('divisor-cell coefficient bits')
        return p

    def add(*ps):
        charge(sum(map(len, ps)))
        return checked(L.add(*ps))

    def scale(p, q):
        charge(len(p))
        return checked(L.scale(p, q))

    def mul(p, q):
        charge(len(p) * len(q))
        return checked(L.mul(p, q, max_terms=max_terms, max_operations=max_operations))

    def dump(p):
        charge(len(p))
        return L.dump_poly(p)

    sqgroups, relgroups, archive = [], [], []
    for region in SPEC['regions']:
        ts = list(range(X, 2 * X) if region == 'parent' else range(2 * X, 4 * X))
        for theta in SPEC['thetas']:
            for power in SPEC['powers']:
                sq = {f: [] for f in SPEC['square_forms']}
                rel = {f: {} for f in SPEC['relation_forms']}
                rows = []
                for t in ts:
                    cut = floor_scaled_power(t, dict(coefficient='1', power=theta))
                    full, inside_pairs, outside_pairs = [], [], []
                    inside, outside = {}, {}
                    for a in range(1, t + 1):
                        w = F(a) ** power
                        for d in range(1, a + 1):
                            charge(1)
                            if a % d == 0:
                                full.append([a, d])
                                dest = inside if d <= cut else outside
                                (inside_pairs if d <= cut else outside_pairs).append([a, d])
                                m = tuple(sorted((a, d)))
                                dest[m] = dest.get(m, F(0)) + w
                    checked(inside); checked(outside)
                    P = {(a,): F(1) for a in range(1, t + 1)}
                    D = scale(add(inside, scale(outside, -1), L.constant(-1)), F(1, 2))
                    Z = add(inside, outside, L.constant(-1))
                    forms = dict(contrast=D, prefix_plus=add(P, D), prefix_minus=add(P, scale(D, -1)))
                    for form, poly in forms.items():
                        sq[form].append(dict(weight='1', poly=dump(poly)))
                    for form, U in [('one', L.constant(1)), ('prefix', P), ('contrast', D), ('normalization', Z)]:
                        for a in range(1, t + 1):
                            primitive = {(1,): F(1), (): F(1)} if a == 1 else {(a,): F(a) ** power}
                            rel[form][a] = add(rel[form].get(a, {}), mul(primitive, U))
                    rows.append(dict(t=t, cut=cut, source_pairs_sha256=digest(full),
                                     inside_pairs_sha256=digest(inside_pairs), complement_pairs_sha256=digest(outside_pairs),
                                     source_count=len(full), inside_count=len(inside_pairs), complement_count=len(outside_pairs),
                                     polynomials_sha256=digest({k: dump(p) for k, p in dict(P=P, I=inside, O=outside, D=D, Z=Z).items()})))
                sg = [sq[f] for f in SPEC['square_forms']]
                rg = [[dict(spec=dict(kind='unit') if a == 1 else dict(kind='inverse_row', n=a), multiplier=dump(p))
                       for a, p in sorted(rel[f].items())] for f in SPEC['relation_forms']]
                sqgroups.extend(sg); relgroups.extend(rg)
                # Independently auditable formal constants; no sign evaluation.
                sqscalars = [sum((F(s['weight']) * L.load_poly(s['poly']).get((), F(0)) ** 2 for s in g), F(0)) for g in sg]
                relscalars = [-L.load_poly(g[0]['multiplier']).get((), F(0)) for g in rg]
                if sqscalars != [F(len(ts), 4)] * 3 or relscalars != [F(-len(ts)), F(0), F(len(ts), 2), F(len(ts))]:
                    raise ValueError('normalized cell scalar ledger')
                archive.append(dict(region=region, theta=theta, power=power, scales=ts, rows=rows,
                                    square_groups_sha256=digest(sg), relation_groups_sha256=digest(rg),
                                    formal_square_scalars=list(map(str, sqscalars)), formal_relation_scalars=list(map(str, relscalars))))
    return dict(square_groups=sqgroups, relation_groups=relgroups, archive=archive, spec=SPEC,
                construction_operations=used, arithmetic_sign_values_substituted=False,
                global_bound_proved=False, RH_proved=False)


def build_instance(target, X, q, C, claim='critical', **limits):
    if target != 'mu':
        raise ValueError('Mobius inverse-of-ones target only')
    extra = build_additions(X, **limits)
    out = BASE.build_instance(target, X, q, C, claim)
    out['instance']['square_groups'].extend(extra['square_groups'])
    out['instance']['relation_groups'].extend(extra['relation_groups'])
    ds = descriptors()
    out.update(square_ids=[d['id'] for d in ds['square']], relation_ids=[d['id'] for d in ds['relation']],
               dictionary_sha256=digest(ds), cell_archive=extra['archive'], cell_spec=SPEC,
               cell_construction_operations=extra['construction_operations'])
    return out
