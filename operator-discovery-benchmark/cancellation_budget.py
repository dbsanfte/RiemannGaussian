"""Formal scalar extraction for arbitrary validated polynomial groups.

No arithmetic coefficient substitution and no nonconstant-identity claim.
"""
from fractions import Fraction as F
import grouped_arithmetic_language as L


def extract(instance, weights):
    if set(weights) != {'square_weights', 'relation_weights'}:
        raise ValueError('weight schema')
    sw, rw = [list(map(F, weights[k])) for k in ('square_weights', 'relation_weights')]
    if len(sw) != len(instance['square_groups']) or len(rw) != len(instance['relation_groups']) or any(w < 0 for w in sw):
        raise ValueError('weight dimensions/domains')
    ledger = []
    for j, (w, group) in enumerate(zip(sw, instance['square_groups'])):
        if not w: continue
        scalar = sum((F(t['weight'])*L.load_poly(t['poly']).get((), F(0))**2 for t in group), F(0))
        ledger.append(dict(kind='square', index=j, weight=str(w), group_scalar=str(scalar), contribution=str(w*scalar)))
    for j, (w, group) in enumerate(zip(rw, instance['relation_groups'])):
        if not w: continue
        scalar = F(0)
        for t in group:
            c = L.load_poly(t['multiplier']).get((), F(0))
            if c:
                scalar += c*L.relation(t['spec'], instance['target'], instance['horizon'], max_operations=200000000).get((), F(0))
        ledger.append(dict(kind='relation', index=j, weight=str(w), group_scalar=str(scalar), contribution=str(w*scalar)))
    budget = sum((F(t['contribution']) for t in ledger), F(0))
    D = L.load_poly(instance['lhs']).get((), F(0))
    return dict(B=str(budget), D=str(D), scalar_slack=str(D-budget), ledger=ledger,
                nonconstant_identity_verified=False, global_bound_proved=False, RH_proved=False)


def audit_added_zero_scalars(instance, old_square_count=52, old_relation_count=195):
    square_count = relation_count = 0
    for group in instance['square_groups'][old_square_count:]:
        for atom in group:
            square_count += 1
            if F(atom['weight'])*L.load_poly(atom['poly']).get((), F(0))**2:
                raise ValueError('new square has nonzero scalar')
    for group in instance['relation_groups'][old_relation_count:]:
        for atom in group:
            relation_count += 1
            c = L.load_poly(atom['multiplier']).get((), F(0))
            if c and L.relation(atom['spec'], instance['target'], instance['horizon']).get((), F(0)):
                raise ValueError('new relation has nonzero scalar')
    return dict(all_added_scalars_zero=True, square_atoms=square_count, relation_atoms=relation_count,
                scope='formal scalar only; full relation admission and nonconstant matching are separate')
