"""Infer necessary normalization equations from a Dirichlet source AST.

These are meromorphic product identities, initially licensed to the right of
the absolute-convergence abscissa. No reciprocal-zeta Dirichlet series is
assumed to converge at an interior normalization point.
"""
from collections import defaultdict
from copy import deepcopy
from fractions import Fraction as Q

import arithmetic_prefix_relations as SOURCE


def _terms(poly):
    return [dict(coefficient=str(c),powers=[[a,e] for a,e in powers])
            for powers,c in sorted(poly.items()) if c]


def _append(poly,key,value):
    poly[key]=poly.get(key,Q(0))+value
    if not poly[key]:del poly[key]


def _divide_monomial(numerator,denominator):
    if len(denominator)!=1:return None
    (denkey,dencoeff),=denominator.items()
    result={}
    for key,value in numerator.items():
        powers=dict(key)
        for argument,exponent in denkey:
            powers[argument]=powers.get(argument,0)-exponent
        new=tuple(sorted((a,e) for a,e in powers.items() if e))
        _append(result,new,value/dencoeff)
    return _terms(result)


def inspect(source,meter=None):
    meter=SOURCE.Meter() if meter is None else meter
    SOURCE.validate_source(source,meter)
    lattice=source['lattice'];channels=[];positive_points=set();all_shifts=[]
    for channel in source['channels']:
        powers=defaultdict(int)
        for atom in channel['atoms']:
            meter.charge()
            shift=Q(atom['shift'],lattice);all_shifts.append(shift)
            powers[shift]+=1 if atom['kind']=='power' else -1
        factors=[[str(s),e] for s,e in sorted(powers.items()) if e]
        channels.append(dict(weight=channel['weight'][:],factors=factors))
        positive_points.update(1-s for s,e in powers.items() if e>0 and s<1)
    poles=[]
    for point in sorted(positive_points):
        orders=[dict((Q(s),e) for s,e in channel['factors']).get(1-point,0) for channel in channels]
        row=dict(point=str(point),channel_orders=orders)
        if max(orders)>1:
            row['status']='higher_order_unsupported';poles.append(row);continue
        if any(point+Q(s)<=0 for channel in channels for s,e in channel['factors'] if Q(s)!=1-point):
            row['status']='nonpositive_regular_argument_unsupported';poles.append(row);continue
        A={};B={}
        for channel,order in zip(channels,orders):
            meter.charge(2+len(channel['factors']))
            if order!=1:continue
            # Each remaining constant has argument different from one. Its
            # nonzero gate, when inverted, is the independent checker's duty.
            key=tuple(sorted((str(point+Q(s)),e) for s,e in channel['factors'] if Q(s)!=1-point))
            _append(A,key,Q(channel['weight'][0]));_append(B,key,Q(channel['weight'][1]))
        numerator={key:-value for key,value in A.items()}
        row.update(status='simple_affine_residue',residue=dict(constant=_terms(A),R=_terms(B)),
            cancellation=dict(numerator=_terms(numerator),denominator=_terms(B),
                              laurent_solution=_divide_monomial(numerator,B)))
        poles.append(row)
    return dict(schema='source-pole-normalization-v1',source_binding=deepcopy(source),
        initial_abscissa=str(max([Q(1)]+[1-s for s in all_shifts])),
        channels=channels,positive_poles=poles,
        scope=dict(reciprocal_zeta_zero_poles_enumerated=False,source_values_observed=False,
                   uniform_bound_proved=False,RH_proved=False))
