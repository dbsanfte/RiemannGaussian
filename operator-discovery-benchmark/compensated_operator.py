"""Standalone public entry for the signed operator and its new certified gap.

Existing frozen experiments retain their core dispatcher/source hashes. This
entry validates the new sort without changing earlier program semantics.
"""
from fractions import Fraction as Q
from compensated_shift_grammar import program_value as finite_value, parameters


def program_value(program,inputs):
    if not isinstance(program,dict) or program.get('kind')!='compensated_shift_program':
        raise ValueError('Expected a compensated_shift_program')
    u,v=parameters(program['left'],program['right'])
    family=program['family']
    if family in ('certified_global_composite_gap','certified_global_prime_separation_certificate'):
        if (u,v)!=(Q(1,3),Q(2,3)):
            raise ValueError('The globally sharp certificate is proved for left=1/3,right=2/3')
        if family=='certified_global_composite_gap': return Q(7,110)
        return {'prime_coefficient':Q(1),'composite_absolute_bound':Q(7,110),
                'domain':'zeta constant-one input, every composite positive integer',
                'sharp_supremum':True,'proof':'compensated_global_gap_proof.txt',
                'prime_size_or_integer_cutoff':None,'new_prime_distribution_estimate_proved':False,
                'RH_continuation_estimate_proved':False,'historical_novelty_established':False}
    return finite_value(program,inputs)
