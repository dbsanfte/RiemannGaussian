"""Exact fixed-kernel binding for a CONDITIONAL RH-sufficient target family.

The arithmetic leaf remains unpaid. Imported analytic implications are
reviewed in MOBIUS_RH_TARGET_AUDIT_084.txt, not formalized by this module.
"""
from fractions import Fraction as Q
import mobius_coupled_completion_083 as P


def transfer_kernel(certificate):
    if type(certificate)is not dict or set(certificate)!={'schema','base_divisor','ratios','extra'}or certificate['schema']!='two-dilation-source-inverse-v1':
        raise ValueError('exact inverse schema')
    D=certificate['base_divisor'];ratios=certificate['ratios'];extra=certificate['extra']
    if type(D)is not int or not 1<=D<=10**6 or type(ratios)is not list or len(ratios)!=2:raise ValueError('base and two dilation ratios')
    a,b=[P.OLD.rational(v)for v in ratios]
    if not 0<a<1 or not 0<b<1:raise ValueError('strict contractive dilation ratios')
    kernel={}
    for ratio,sign in [(Q(1),-1),(a,1),(b,1),(a*b,-1)]:
        v=Q(D)/ratio
        if v.denominator!=1 or v.numerator.bit_length()>4096:raise ValueError('integer source divisors required')
        kernel[int(v)]=kernel.get(int(v),Q(0))+sign
    if extra is not None:
        if type(extra)is not dict or set(extra)!={'coefficient','divisor'}:raise ValueError('extra dilation schema')
        c=P.OLD.rational(extra['coefficient']);d=extra['divisor']
        if abs(c)>=1 or type(d)is not int or not 2<=d<=10**6:raise ValueError('invertible small extra dilation')
        old=dict(kernel)
        for v,w in old.items():kernel[v*d]=kernel.get(v*d,Q(0))+c*w
    return [dict(divisor=d,weight=str(w))for d,w in sorted(kernel.items())if w]


def compile_target(program,transfer):
    p=P.parse_program(program)
    if transfer_kernel(transfer)!=program['kernel']:raise ValueError('entire fixed source kernel does not match inverse')
    r=p['drift_multiplier']
    if not 1<=r<2:raise ValueError('uniform rational contraction for q>=1 requires r<2')
    factor=Q(2)/(2-r)
    return dict(schema='epsilon-family-signed-drift-target-v1',status='VERIFIED_CONDITIONAL_RH_TARGET',
                kernel=program['kernel'],transfer_certificate=transfer,
                exponent_family=dict(parameter='j',domain='all positive integers',energy_exponent='1+1/j',source_exponent='1/2+1/(2*j)'),
                drift_multiplier=str(r),uniform_induction_factor=str(factor),zero_scale_energy='0',
                energy_domination_proved_from_schema=True,source_dilation_inverse_binding_verified=True,
                required_arithmetic_leaf='For every integer j>=1, prove existence of finite C_j>=0 such that E_j(u)-r*E_j(floor(u/2))<=C_j*u^(1+1/j) for every integer u>=1.',
                constants_may_depend_on_j=True,operator_and_energy_may_depend_on_j=True,
                no_additional_source_parameter_family_required_for_this_kernel=True,
                implication='The required leaf gives E_j(u)<=uniform_induction_factor*C_j*u^(1+1/j), hence fixed-source and Mertens bounds for every positive epsilon, hence RH.',
                conditional_analytic_dependencies=['MOBIUS_RH_TARGET_AUDIT_084.txt','https://dlmf.nist.gov/27.4.E5','https://dlmf.nist.gov/25.10'],
                finite_exponent_roster_suffices=False,arithmetic_leaf_status='UNPAID',formal_theorem_prover_checked=False,
                uniform_source_bound_proved=False,RH_proved=False)


def exponent(j):
    if type(j)is not int or not 1<=j<=10**6:raise ValueError('finite instance parameter gate')
    return Q(j+1,j)


def exact_power_comparison(price,u,j,constant='1'):
    """Finite diagnostic only: price<=constant*u^(1+1/j), no floating root."""
    q=exponent(j);b=P.OLD.rational(constant);v=P.OLD.rational(price)
    if type(u)is not int or u<1 or b<0:raise ValueError('positive scale/nonnegative comparison constant')
    if v<=0:return True
    if not b:return False
    ratio=v/b
    bits=q.denominator*(ratio.numerator.bit_length()+ratio.denominator.bit_length())+q.numerator*u.bit_length()
    if bits>P.OLD.MAX_BITS:raise P.ResourceLimit('exact exponent comparison bit gate')
    return ratio.numerator**q.denominator<=ratio.denominator**q.denominator*u**q.numerator
