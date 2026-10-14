"""Exact primal instantiation without expanding zero-weight dictionary groups.

All source syntax, horizons and arithmetic premises are checked. Expansion budgets
apply to work actually performed; unused column expansion limits are intentionally
not evaluated. This is a primal verifier/producer, never a dual cone shortcut.
"""
from fractions import Fraction as F
import json
import math
import time
import grouped_arithmetic_language as L


def instantiate_details(instance, weights, *, max_columns=1024, max_monomials=10000,
                        max_operations=200000000, max_coefficient_bits=2048,
                        max_horizon=4096, max_degree=12, max_denominator=1000000,
                        time_limit=10, deadline=None, allow_constant_slack=False):
    start = time.monotonic()
    for v in (max_columns, max_monomials, max_operations, max_coefficient_bits,
              max_horizon, max_degree, max_denominator):
        if type(v) is not int or v < 1:
            raise ValueError('positive resource bounds')
    if type(time_limit) not in (int, float) or not math.isfinite(time_limit) or time_limit <= 0:
        raise ValueError('positive finite time limit')
    if type(allow_constant_slack) is not bool:
        raise ValueError('slack flag bool')
    if deadline is None:
        deadline = start + time_limit
    if type(deadline) not in (int, float) or not math.isfinite(deadline):
        raise ValueError('finite absolute deadline')
    used = expanded = 0
    relation_cache = {}

    def charge(n=1):
        nonlocal used
        used += n
        if used > max_operations or time.monotonic() > deadline:
            raise OverflowError('sparse instantiation work/time')

    def bits(q):
        if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > max_coefficient_bits:
            raise OverflowError('coefficient bits')
        return q

    def rational(v):
        # Guard before conversion, including pathological decimal/exponent strings.
        if type(v) is not str:
            raise ValueError('canonical rational string')
        if len(v) > 2 * max_coefficient_bits + 3:
            raise OverflowError('rational input length')
        if any(c not in '-0123456789/' for c in v):
            raise ValueError('canonical rational string')
        q = bits(F(v))
        if str(q) != v:
            raise ValueError('canonical rational string')
        return q

    if type(instance) is not dict or set(instance) != {'target','horizon','lhs','square_groups','relation_groups'}:
        raise ValueError('instance schema')
    H, target = instance['horizon'], instance['target']
    if type(H) is not int or H < 1 or type(target) is not str or target not in ('mu','c'):
        raise ValueError('instance domain')
    if H > max_horizon:
        raise OverflowError('horizon limit')
    if any(type(instance[k]) is not list for k in ('square_groups','relation_groups')):
        raise ValueError('group arrays')
    if len(instance['square_groups']) + 2 * len(instance['relation_groups']) > max_columns:
        raise OverflowError('column limit')

    def parse(data):
        if type(data) is not list or len(data) > max_monomials:
            raise OverflowError('polynomial terms')
        charge(len(data))
        out = {}; previous = None
        for term in data:
            if type(term) is not dict or set(term) != {'m','c'} or type(term['m']) is not list:
                raise ValueError('polynomial schema')
            m = tuple(term['m']); q = rational(term['c'])
            if any(type(i) is not int or not 1 <= i <= H for i in m):
                raise ValueError('polynomial horizon/index')
            if tuple(sorted(m)) != m or not q or (previous is not None and m <= previous):
                raise ValueError('noncanonical polynomial')
            if len(m) > max_degree:
                raise OverflowError('polynomial degree')
            out[m] = q; previous = m
        return out

    def primitive(spec):
        if type(spec) is not dict:
            raise ValueError('relation spec')
        key = json.dumps(spec, sort_keys=True, separators=(',', ':'), allow_nan=False)
        if key not in relation_cache:
            # Shared budget includes factorization/premise work. Cache is local to
            # one fixed target and horizon and is discarded after this call.
            budget = L.Budget(max_operations - used) if used < max_operations else L.Budget(1)
            p = L._relation(spec, target, H, budget)
            charge(budget.used)
            relation_cache[key] = p
        return relation_cache[key]

    def degree(p):
        return max(map(len, p), default=0)

    def product(a, b):
        nonlocal expanded
        charge(len(a) * len(b)); expanded += 1
        p = L.mul(a, b, max_terms=max_monomials, max_operations=max_operations)
        for q in p.values(): bits(q)
        return p

    rhs = {}
    def merge(poly, weight):
        charge(len(poly))
        for m, q in poly.items():
            value = bits(rhs.get(m, F(0)) + bits(weight * q))
            if value: rhs[m] = value
            else: rhs.pop(m, None)
        if len(rhs) > max_monomials:
            raise OverflowError('expanded terms')

    if type(weights) is not dict or set(weights) != {'square_weights','relation_weights'}:
        raise ValueError('shared weights schema')
    if any(type(weights[k]) is not list for k in weights):
        raise ValueError('shared weight arrays')
    sw = list(map(rational, weights['square_weights'])); rw = list(map(rational, weights['relation_weights']))
    if len(sw) != len(instance['square_groups']) or len(rw) != len(instance['relation_groups']) or any(w < 0 for w in sw):
        raise ValueError('shared weight domains')
    lhs = parse(instance['lhs']); squares = []; relations = []
    for weight, group in zip(sw, instance['square_groups']):
        if type(group) is not list: raise ValueError('square group list')
        charge(len(group))
        for term in group:
            if type(term) is not dict or set(term) != {'weight','poly'}:
                raise ValueError('square group term')
            own = rational(term['weight'])
            if own < 0: raise ValueError('nonnegative fixed square weight')
            p = parse(term['poly'])
            if 2 * degree(p) > max_degree: raise OverflowError('expanded polynomial degree')
            w = bits(weight * own)
            if w:
                merge(product(p, p), w)
                squares.append(dict(weight=str(w), poly=term['poly']))
    for weight, group in zip(rw, instance['relation_groups']):
        if type(group) is not list: raise ValueError('relation group list')
        charge(len(group))
        for term in group:
            if type(term) is not dict or set(term) != {'spec','multiplier'}:
                raise ValueError('relation group term')
            p = parse(term['multiplier']); r = primitive(term['spec'])
            if p and r and degree(p) + degree(r) > max_degree:
                raise OverflowError('expanded polynomial degree')
            if weight:
                merge(product(p, r), weight)
                scaled = {m: bits(weight*q) for m,q in p.items()}
                relations.append(dict(spec=term['spec'], multiplier=L.dump_poly(scaled)))
    residual = dict(lhs)
    for m,q in rhs.items():
        value = bits(residual.get(m,F(0))-q)
        if value: residual[m] = value
        else: residual.pop(m,None)
    if any(residual): raise ValueError('full original nonconstant residual')
    slack = residual.get((),F(0))
    if slack < 0 or (slack and not allow_constant_slack):
        raise ValueError('nonzero or negative scalar remainder')
    if slack: squares.append(dict(weight=str(slack),poly=[dict(m=[],c='1')]))
    charge()
    certificate = dict(target=target,horizon=H,lhs=instance['lhs'],squares=squares,relations=relations)
    return dict(certificate=certificate,constant_slack=str(slack),
                diagnostics=dict(elapsed_seconds=time.monotonic()-start,operations=used,
                    expanded_products=expanded,validated_unique_relations=len(relation_cache),
                    skipped_zero_groups=sum(not w for w in sw+rw)),
                global_bound_proved=False,RH_proved=False)


def instantiate_certificate(instance, weights, **limits):
    return instantiate_details(instance, weights, **limits)['certificate']
