"""Signed shift mixtures constrained by arithmetic and zero-order tests.

Negative weights are allowed in this explicit sort. Prime/composite bounds
concern the zeta input. Their sign and zero signatures are separately gated.
"""

from fractions import Fraction as Q
import flint

from fractional_prime_grammar import complete_prefix,power_placement
from shift_ratio_grammar import forward,recover,real


def parameters(left,right):
    u,v = Q(left),Q(right)
    if not 0<u<v<1:
        raise ValueError('The compensator requires rational 0 < left < right < 1')
    return u,v


def atoms(left,right):
    u,v = parameters(left,right)
    a,b = 1/u-u,1/v-v
    return ((-b/(a-b),u),(a/(a-b),v))


def valuation_vector(x):
    x = Q(x)
    if x<=0:
        raise ValueError('A positive rational is required')
    out = {}
    for n,sign in ((x.numerator,1),(x.denominator,-1)):
        product = 1
        for p,e in flint.fmpz(n).factor():
            p,e = int(p),int(e)
            product *= p**e
            out[p] = out.get(p,0)+sign*e
        if product!=n:
            raise ArithmeticError('The rational factorization failed reconstruction')
    return {p:e for p,e in out.items() if e}


def root_signature_certificate(left,right):
    u,v = parameters(left,right)
    r,R = v/u,(1/u-u)/(1/v-v)
    rr,RR = valuation_vector(r),valuation_vector(R)
    orders = {Q(RR.get(p,0),e) for p,e in rr.items()}
    outside = any(p not in rr for p in RR)
    order = next(iter(orders)) if len(orders)==1 else None
    vanished = (not outside and order is not None and order.denominator==1 and order>=1)
    return {'formula':'m*sum_i weight_i/v_i**m',
        'ratio_base':str(r),'ratio_target':str(R),
        'base_prime_valuations':{str(p):e for p,e in rr.items()},
        'target_prime_valuations':{str(p):e for p,e in RR.items()},
        'zero_leading_signature_orders':[int(order)] if vanished else [],
        'nonzero_leading_signature_every_positive_integer_order_proved':not vanished,
        'finite_order_testing_substituted_for_all_order_proof':False,
        'zero_leading_coefficient_means_whole_branch_erased_claimed':False,
        'domain':'the separately proved local zero corridor and locally uniform integral tail',
        'RH_regularized_continuation_criterion_certified':not vanished}


def arithmetic_certificate(left,right):
    u,v = parameters(left,right)
    A = atoms(u,v)
    a,b = 1/u-u,1/v-v
    bu,bv = (1-u)**2/u,(1-v)**2/v
    K = a*b*(bu-bv)/(a-b)
    pair_gap = K*Q(1,16)/((1+bu/4)*(1+bv/4))
    universal_gap = max(abs(w)*(1-x)/(1+x) for w,x in A)
    return {'left':str(u),'right':str(v),
        'atoms':[{'weight':str(w),'v':str(x)} for w,x in A],
        'prime_value':'1','universal_composite_upper':str(universal_gap),
        'prime_separation_certified':universal_gap<1,
        'two_distinct_prime_product_formula':{'variable':'z=t*(1-t), t=log(p)/log(p*q)',
            'negative_prefactor':str(K),'denominator_parameters':[str(bu),str(bv)],
            'formula':'-K*z^2/((1+b_left*z)*(1+b_right*z))'},
        'sharp_two_distinct_prime_product_gap':str(pair_gap),
        'two_prime_least_prime_square_envelope_constant':str(K),
        'square_envelope_domain':'only squarefree products p*q of two distinct primes',
        'universal_square_roughness_envelope_proved':False,
        'root_signature_certificate':root_signature_certificate(u,v),
        'all_scale_prime_distribution_or_signed_cancellation_estimate_proved':False,
        'historical_novelty_established':False}


def pair_bound(left,right,t):
    cert = arithmetic_certificate(left,right)
    t = Q(t)
    if not 0<t<1:
        raise ValueError('The exact pair ratio must lie in (0,1)')
    K = Q(cert['two_distinct_prime_product_formula']['negative_prefactor'])
    bu,bv = map(Q,cert['two_distinct_prime_product_formula']['denominator_parameters'])
    z = t*(1-t)
    return K*z*z/((1+bu*z)*(1+bv*z))


def program_value(program,inputs):
    u,v = parameters(program['left'],program['right'])
    family = program['family']
    if family=='compensator_certificate':
        return arithmetic_certificate(u,v)
    if family=='two_prime_product_bound':
        return pair_bound(u,v,program['log_ratio'])
    if family not in ('compensated_arithmetic_log','compensated_prime_decoder','compensated_decoder_inverse'):
        raise ValueError('Unknown signed-compensator production '+family)
    inverse = family=='compensated_decoder_inverse'
    values = complete_prefix(inputs[program['input']],normalized=not inverse)
    A = atoms(u,v)
    if inverse:
        return recover(values,A)
    R = forward(values,A)
    return R if family=='compensated_arithmetic_log' else power_placement(R,True)


PRODUCTION_CATALOGUE = {'kind':'compensated_shift_program',
    'families':['compensated_arithmetic_log','compensated_prime_decoder','compensated_decoder_inverse',
                'compensator_certificate','two_prime_product_bound'],
    'parameters':'rational 0<left<right<1; signed weights generated to cancel the learned first-order two-prime term',
    'universal_formal_laws':['triangular inverse on arbitrary normalized units','prime value one on zeta input'],
    'arithmetic_laws':['second-order suppression on squarefree two-prime products at every scale',
                       'universal composite bound from common atomic signs, with strict separation only when certified'],
    'ordinary_zero_gate':'exact rational valuation test must certify every positive integer zero order; a canceled leading term alone does not prove branch removal',
    'new_independent_prime_distribution_estimate_proved':False,
    'historical_novelty_established':False}
