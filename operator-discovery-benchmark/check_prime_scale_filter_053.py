"""Independent finite-filter arithmetic/conditional RH rule replay.

No new producer imports, data, root-location oracle or arithmetic bound solver.
Frozen052 rational/type/meter primitives are reused; the filter and all costs
and claim scopes are independently reconstructed here.
"""
from math import gcd
from check_fractional_prime_rh_bridge_052 import Meter,_rational,_same


def _expect(got,want):
    if not _same(got,want):raise ValueError('filter source, identity or proof scope mismatch')


def _keys(obj,keys):
    if type(obj) is not dict or set(obj)!=set(keys):raise ValueError('exact filter schema')


def _parse(request,meter):
    _keys(request,('alpha','q','coefficients','bound'))
    alpha=_rational(request['alpha'],meter);q=request['q'];cs=request['coefficients']
    if not 0<alpha<1 or type(q) is not int or not 2<=q<=64:raise ValueError('fixed fractional exponent and integer scale')
    if type(cs) is not list or not 2<=len(cs)<=17:raise ValueError('degree1..16')
    if any(type(c) is not int or abs(c).bit_length()>1024 for c in cs):raise ValueError('strict bounded integer coefficients')
    common=0;pq=0;jumps=0;power=1
    for c in cs:
        common=gcd(common,c);pq+=c*power;jumps+=abs(c)*power;power*=q
        meter.charge(16+abs(pq).bit_length()+abs(c).bit_length())
    if common!=1 or cs[0]==0 or cs[-1]<=0 or pq!=0:raise ValueError('primitive nonzero mean-neutral polynomial')
    bound=request['bound'];_keys(bound,('C','log_power','minimum','normalization'))
    C=_rational(bound['C'],meter);eta=_rational(bound['log_power'],meter)
    if C<=0 or eta<0 or type(bound['minimum']) is not int or bound['minimum']!=2:raise ValueError('all integer scales and fixed finite bound')
    _expect(bound['normalization'],'divide_by_alpha')
    return alpha,q,cs,C,eta,jumps


def _instance(request,alpha,q,cs,C,eta,jumps):
    degree=len(cs)-1;p1=sum(cs)
    return {
        'schema':'fractional-prime-scale-filter-proof-v1','request':request,
        'status':'PAID_ARITHMETIC_REDUCTION_AND_CONDITIONAL_RH_BOUND_OPEN',
        'kernel':{'a':'1','b':'0','alpha':str(alpha),'sign':-1},
        'polynomial':{'ascending_coefficients':cs,'degree':degree,'P_at_q':0,'P_at_one':p1,
            'nonzero':True,'no_annulus_root_exclusion_required':True},
        'source':{
            'K':'K_alpha(n)=-sum_{d|n}mu(d)*(log d)^alpha; K_alpha(1)=0',
            'A':'A_alpha(x)=sum_{2<=n<=x}K_alpha(n), every real x>=1',
            'T':'T_P(x)=sum_{j=0}^degree c_j*A_alpha(q^j*x)',
            'normalized_target':'T_P(x)/alpha',
            'finite_divisor_identity':'T_P(N)=-sum_{d<=q^degree*N}mu(d)*(log d)^alpha*sum_j c_j*floor(q^j*N/d)',
            'ordinary_mobius':True,'all_prime_and_composite_terms_retained':True,
            'rounding':'none in mathematical source; numerical enclosures must retain their error'},
        'main_term_cancellation':{
            'full_center':'M_alpha(x)=kappa_alpha*(x-1)',
            'kappa_definition':'kappa_alpha=I_alpha^(-1)*integral_0^infinity t^(-alpha-1)/zeta(1+t) dt',
            'filtered_center':'-kappa_alpha*P(1), since P(q)=0',
            'affine_center_annihilated':p1==0,'kappa_evaluation_or_fitting_required':False},
        'open_premise':{
            'status':'OPEN','C':str(C),'log_power':str(eta),
            'expression':'|T_P(N)|/alpha<=C*sqrt(N)*(1+log(N))^eta',
            'quantifiers':'for every ordinary integer N>=2; fixed alpha,q,P,C,eta',
            'finite_samples_can_pay':False,'pointwise_K_bound_can_pay':False,
            'polynomial_cancellation_can_pay':False,'arithmetic_bound_proved':False},
        'integer_to_real':{
            'integer_jump_budget':jumps,
            'formula':'|T_P(x)-T_P(floor(x))|<=sum_j |c_j|*q^j*(log(q^j*(x+1)))^alpha',
            'pointwise_dependency':'0<K_alpha(n)<=(log(n))^alpha, for all n>=2',
            'conclusion':'OPEN integer premise implies T_P(x)=O_epsilon(x^(1/2+epsilon)) for every epsilon>0'},
        'mellin_identity':{
            'initial_domain':'Re(s)>1','F':'F_alpha(s)=sum_{n>=2}K_alpha(n)/n^s',
            'head':'B_P(s)=sum_j c_j*q^(j*s)*integral_1^(q^j) A_alpha(u)*u^(-s-1) du',
            'head_entire':True,
            'formula':'integral_1^infinity T_P(x)*x^(-s-1) dx=P(q^s)*F_alpha(s)/s-B_P(s)',
            'conditional_holomorphy':'OPEN premise implies P(q^s)*F_alpha(s)/s holomorphic on Re(s)>1/2'},
        'fractional_zero_survival':{
            'dependency':'reviewed052 fixed-height rightmost-zero asymptotic, b=0, every zeta zero multiplicity',
            'F_asymptotic':'F_alpha(rho+delta)=C_rho*delta^(-alpha)+O(1), C_rho!=0, delta>0 tending to0',
            'multiplier_order':'P(q^s)/s has a finite integer zero order k>=0 at nonreal rho',
            'reason_finite':'P is nonzero finite polynomial; q^s has nonzero derivative; rho!=0',
            'product_asymptotic':'P(q^(rho+delta))*F_alpha(rho+delta)/(rho+delta)=C_prime*delta^(k-alpha)+O(delta^k), C_prime!=0',
            'k_zero':'the expression diverges, contradicting holomorphy',
            'k_positive':'k-1<k-alpha<k forces all Taylor coefficients through k-1 to vanish; holomorphy would imply O(delta^k), a contradiction',
            'all_polynomial_root_locations_allowed':True},
        'conclusion':'the exact OPEN integer arithmetic bound implies RH',
        'conditional_RH_implication_proved':True,'uniform_arithmetic_bound_proved':False,
        'centered_error_bound_proved':False,'original_floor_energy_bound_proved':False,
        'converse_proved':False,'RH_proved':False,'RH_refuted':False,'numerical_evidence_used':False,
        'proof_backend':'independently reviewed analytic and finite-divisor rules; not proof-assistant formalization'}


def verify_filter(request,certificate,meter=None):
    meter=Meter() if meter is None else meter
    alpha,q,cs,C,eta,jumps=_parse(request,meter)
    expected=_instance(request,alpha,q,cs,C,eta,jumps)
    _expect(certificate,expected);meter.charge(len(repr(expected))+300)
    return {'verified':True,'arithmetic_reduction_proved':True,
        'conditional_RH_implication_proved':True,'uniform_arithmetic_bound_proved':False,
        'open_premise_status':'OPEN','RH_proved':False,'RH_refuted':False,
        'all_polynomial_root_locations_allowed':True,'integer_jump_budget':jumps,
        'degree':len(cs)-1,'proof_scope':'reviewed finite typed rule; not proof-assistant formalization'}


verify=verify_filter
