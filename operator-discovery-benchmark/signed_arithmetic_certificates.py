"""Supplied exact kernel/discrepancy lemmas; no full signed Mobius bound.

Numerical discovery chooses rational dilates/weights. This module only certifies
those parameters against universal identities and actual-arithmetic lemmas.
No floating point arithmetic and no tests promoted to all-scale theorems.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
from math import gcd, isqrt
import json


def rational(value):
    if isinstance(value, bool) or isinstance(value, float):
        raise TypeError('exact rational required, not bool/float')
    return Q(value)


def positive_integer(value, name):
    if type(value) is not int or value < 1:
        raise ValueError(name + ' must be a positive integer')
    return value


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


@dataclass(frozen=True)
class PiecewiseLinearKernel:
    """Continuous rational polygon on [0,L], zero beyond L.

    The final ordinate must be zero to ensure continuity at the support edge.
    A nonzero first ordinate is permitted: discrepancy E(0)=0 has no left cost.
    """
    knots: tuple

    def __post_init__(self):
        knots = tuple((rational(x), rational(y)) for x, y in self.knots)
        if len(knots) < 2 or knots[0][0] != 0:
            raise ValueError('at least two knots, starting at zero, required')
        if any(b[0] <= a[0] for a, b in zip(knots, knots[1:])):
            raise ValueError('abscissae must be strictly increasing')
        if knots[-1][1] != 0:
            raise ValueError('compact support endpoint must be zero')
        object.__setattr__(self, 'knots', knots)

    @property
    def support(self):
        return self.knots[-1][0]

    def value(self, t):
        t = rational(t)
        if t < 0:
            raise ValueError('kernel domain is t >= 0')
        if t >= self.support:
            return Q(0)
        for (a, y), (b, z) in zip(self.knots, self.knots[1:]):
            if a <= t <= b:
                return y + (z-y)*(t-a)/(b-a)
        raise RuntimeError('uncovered kernel domain')

    def integral(self):
        return sum(((b-a)*(y+z)/2 for (a,y),(b,z) in zip(self.knots,self.knots[1:])), Q(0))

    def ast(self):
        return {'kind': 'continuous_piecewise_linear', 'knots': [[str(x),str(y)] for x,y in self.knots], 'zero_beyond_support': True}


def kernel_from_dilates(terms):
    """Return w(t)=sum c*(2s-max(s,t))_+ for exact positive s."""
    terms = tuple((rational(s), rational(c)) for s,c in terms)
    if not terms or any(s <= 0 for s,c in terms):
        raise ValueError('nonempty positive dilate list required')
    points = sorted({Q(0)} | {s for s,c in terms} | {2*s for s,c in terms})
    return PiecewiseLinearKernel(tuple((t, sum((c*max(Q(0),2*s-max(s,t)) for s,c in terms),Q(0))) for t in points))


def sqrt_enclosure(value, bits=48):
    """Return exact rational lower/upper brackets, proved by integer squares."""
    value = rational(value)
    if value < 0 or type(bits) is not int or not 1 <= bits <= 4096:
        raise ValueError('nonnegative radicand and bits in [1,4096] required')
    scale = 1 << bits
    integer = value.numerator * value.denominator * scale * scale
    root = isqrt(integer)
    lower = Q(root, value.denominator*scale)
    upper = lower if root*root == integer else Q(root+1,value.denominator*scale)
    return lower, upper


def certify_kernel(kernel, bits=48):
    """A rational upper bound for integral sqrt(t)|dw(t)|.

    Each segment contribution is |slope|*(2/3)*(b sqrt(b)-a sqrt(a)).
    Brackets use upper at b and lower at a, retaining rigorous subtraction.
    """
    if not isinstance(kernel, PiecewiseLinearKernel):
        raise TypeError('PiecewiseLinearKernel required')
    sqrt_enclosure(Q(0), bits)  # validate precision even for constant kernels
    segments=[]
    upper=Q(0)
    for (a,y),(b,z) in zip(kernel.knots,kernel.knots[1:]):
        slope=(z-y)/(b-a)
        alo,ahi=sqrt_enclosure(a,bits)
        blo,bhi=sqrt_enclosure(b,bits)
        cost=abs(slope)*Q(2,3)*(b*bhi-a*alo)
        upper += cost
        segments.append({'a':str(a),'b':str(b),'slope':str(slope),'sqrt_a':[str(alo),str(ahi)],'sqrt_b':[str(blo),str(bhi)],'weighted_variation_upper':str(cost)})
    ast=kernel.ast()
    return {'schema':1,'kernel':ast,'kernel_sha256':digest(ast),'exact_integral':str(kernel.integral()),'left_endpoint':str(kernel.knots[0][1]),'right_endpoint':'0','left_endpoint_zero':kernel.knots[0][1]==0,'right_endpoint_zero':True,'left_discrepancy_zero':True,'weighted_sqrt_variation_upper':str(upper),'sqrt_bits':bits,'segments':segments,'admitted_zero_moment_component':kernel.integral()==0,'supplied_lemma':'coprime_squarefree_discrepancy_plus_continuous_integration_by_parts','full_signed_bound_proved':False}


def verify_kernel_certificate(certificate):
    try:
        ast=certificate['kernel']
        if ast.get('kind')!='continuous_piecewise_linear' or ast.get('zero_beyond_support') is not True:
            return False
        kernel=PiecewiseLinearKernel(tuple(tuple(v) for v in ast['knots']))
        return certify_kernel(kernel, certificate['sqrt_bits'])==certificate
    except (KeyError,ValueError,TypeError,ZeroDivisionError):
        return False


def modulus_charge(modulus):
    """Exact 2^omega(k)+2; trial-factorization work is exposed."""
    positive_integer(modulus,'modulus')
    remaining=modulus
    factors=[]
    d=2
    divisions=0
    while d*d<=remaining:
        divisions+=1
        if remaining%d==0:
            factors.append(d)
            while remaining%d==0:
                remaining//=d
                divisions+=1
        d=3 if d==2 else d+2
    if remaining>1:
        factors.append(remaining)
    return {'modulus':modulus,'distinct_prime_factors':factors,'omega':len(factors),'charge':(1<<len(factors))+2,'trial_division_checks':divisions,'cost_not_uniform_in_modulus':True}


def component_certificate(kernel, modulus, r=1, bits=48):
    """All real X>0 bound for sum_(g>=1,(g,k)=1) mu(g)^2 X*w(rg/X)."""
    positive_integer(r,'r')
    record=certify_kernel(kernel,bits)
    charge=modulus_charge(modulus)
    coefficient=Q(record['weighted_sqrt_variation_upper'])*charge['charge']
    _,inverse_root_upper=sqrt_enclosure(Q(1,r),bits)
    return {'schema':1,'kernel_certificate':record,'modulus_certificate':charge,'r':r,'admitted':record['admitted_zero_moment_component'],'quantifiers':'every real X>0, actual mu=Dirichlet inverse of One, every integer g>=1','bound_coefficient_before_r_sqrt':str(coefficient),'bound':'coefficient * X^(3/2) / sqrt(r)','rational_coefficient_after_r_sqrt_upper':str(coefficient*inverse_root_upper),'normalization':'W_X(t)=X*w(t/X)','density_main_term_zero':record['exact_integral']=='0','global_component_bound_proved':record['admitted_zero_moment_component'],'full_signed_bound_proved':False,'inferred_parameters_only':['kernel knots or rational dilate weights'],'supplied_proof_method':['squarefree divisor expansion','coprime inclusion-exclusion','absolute tail','continuous integration by parts','integer-square radical enclosure']}


def actual_mobius(limit):
    """Complete divisor inversion, intentionally independent of prime factor oracle."""
    positive_integer(limit,'limit')
    mu=[0]*(limit+1)
    mu[1]=1
    for d in range(1,limit+1):
        for n in range(2*d,limit+1,d):
            mu[n]-=mu[d]
    return mu


def verify_actual_mobius(mu, limit):
    if type(limit) is not int or limit<1 or len(mu)<=limit:
        return False
    if any(type(mu[n]) is not int for n in range(1,limit+1)):
        return False
    sums=[0]*(limit+1)
    for d in range(1,limit+1):
        for n in range(d,limit+1,d):
            sums[n]+=mu[d]
    return sums[1]==1 and all(sums[n]==0 for n in range(2,limit+1))


def primitive_pair_partition(mu, X, B, kernel):
    """Exact finite evaluation of the FULL homogeneous quadratic kernel.

    This validates actual arithmetic locally, not an all-scale signed estimate.
    Shared cutoff B applies once to the entire scaled kernel (never per dilate).
    """
    positive_integer(X,'X')
    if type(B) is not int or B<0:
        raise ValueError('B must be a nonnegative integer')
    if not isinstance(kernel,PiecewiseLinearKernel):
        raise TypeError('PiecewiseLinearKernel required')
    endpoint=kernel.support*X
    limit=endpoint.numerator//endpoint.denominator
    if limit<1:
        return {'X':X,'B':B,'limit':limit,'diagonal':'0','retained_pairs':'0','residual_pairs':'0','full':'0','direct':'0','exact_partition_verified':True,'dense_signed_bound_proved':False}
    if not verify_actual_mobius(mu,limit):
        raise ValueError('complete actual inverse constraints fail or arithmetic missing')
    weight=lambda n: X*kernel.value(Q(n,X))
    diagonal=sum((mu[n]**2*weight(n) for n in range(1,limit+1)),Q(0))
    retained=Q(0)
    residual=Q(0)
    for r in range(2,min(B,limit)+1):
        for a in range(1,r):
            if gcd(a,r)!=1:
                continue
            inner=sum((mu[g]**2*weight(g*r) for g in range(1,limit//r+1) if gcd(g,a*r)==1),Q(0))
            term=2*mu[a]*mu[r]*inner
            retained+=term
    prefix=0
    direct=Q(0)
    for n in range(1,limit+1):
        prefix+=mu[n]
        direct+=prefix**2*(weight(n)-weight(n+1))
    residual=direct-diagonal-retained
    full=diagonal+retained+residual
    return {'X':X,'B':B,'limit':limit,'diagonal':str(diagonal),'retained_pairs':str(retained),'residual_pairs':str(residual),'full':str(full),'direct':str(direct),'exact_partition_verified':True,'arithmetic_scope':'complete actual inversion through limit only','dense_signed_bound_proved':False,'residual_obligation':'full r>B signed primitive-pair sum; no omission, no sign asserted','shared_cutoff':True,'full_evaluation':'O(limit) prefix quadratic summation by parts','residual_evaluation':'exact subtraction of diagonal and complete retained projection','full_residual_expression':'2 sum_(a<r,gcd(a,r)=1,r>B) mu(a)mu(r) sum_(g>=1,gcd(g,ar)=1) mu(g)^2 X*w(gr/X)' }


def dilate_bridge_certificate(terms, epsilon):
    """Check a CONDITIONAL positive dyadic recursion bridge, never its premise."""
    epsilon=rational(epsilon)
    if epsilon<=0:
        raise ValueError('strictly positive exponent required')
    merged={}
    for scale,coefficient in terms:
        scale=rational(scale)
        coefficient=rational(coefficient)
        if scale<=0:
            raise ValueError('positive scales required')
        merged[scale]=merged.get(scale,Q(0))+coefficient
    merged={s:c for s,c in merged.items() if c}
    if not merged:
        raise ValueError('nonzero stencil required')
    highest=max(merged)
    powers=all(s.denominator==1 and s.numerator>=1 and s.numerator & (s.numerator-1)==0 for s in merged)
    leading=merged[highest]==1
    nonpositive=all(c<=0 for s,c in merged.items() if s<highest)
    moment=sum((c*s*s for s,c in merged.items()),Q(0))
    admitted=powers and leading and nonpositive and moment==0 and highest>1
    probabilities=[[str(s),str(-c*s*s/(highest*highest))] for s,c in sorted(merged.items()) if s<highest]
    return {'schema':1,'terms':[[str(s),str(c)] for s,c in sorted(merged.items())], 'epsilon':str(epsilon),'highest_scale':str(highest),'dyadic_positive_integer_scales':powers,'leading_coefficient_one':leading,'lower_coefficients_nonpositive':nonpositive,'quadratic_moment':str(moment),'normalized_recursion_weights':probabilities,'conditional_bridge_admitted':admitted,'signed_inequality_proved':False,'RH_proved':False,'premise':'for every dyadic integer X>=1: sum c_s A(sX) <= C X^(2+epsilon), with finite C>=0 independent of X','conclusion_if_premise':'A(n)=O_epsilon(n^(2+epsilon)) for every dyadic n>=1; initial n<highest_scale retained','safe_normalized_bound':'A(n)/n^2 <= H + C*n^epsilon/[highest_scale^2*(1-2^(-epsilon))]','initial_constant':'H=max A(n)/n^2 over dyadic 1<=n<highest_scale','cofinal_RH_bridge':'requires all positive epsilon=epsilon(q) tending to zero, every integer q>=q0, finite independent-of-X C_q and all dyadic X; identity or component bounds do not supply this premise','ceil_extension':'C X^2 ceil(X^epsilon) <= 2C X^(2+epsilon) for X>=1','supplied_proof_method':'nonnegative normalized recursion plus dyadic running-maximum geometric telescope'}


def liouville_squarefloor_certificate(terms):
    """Admit a POST-DISCOVERY sparse law for a declared filtered actual target.

    terms: [(feature_dict, exact_coefficient), ...]. Supported symbolic feature
    syntax is {'kind':'floor_root','q':int,'offset':rational}. Recognition is a
    supplied theorem, not a feature vector delivered to the numeric learner.
    """
    merged={}
    syntax_ok=True
    for feature,coefficient in terms:
        coefficient=rational(coefficient)
        if not coefficient:
            continue
        if not isinstance(feature,dict) or set(feature)!={'kind','q','offset'} or feature.get('kind')!='floor_root' or type(feature.get('q')) is not int or feature['q']<1:
            syntax_ok=False
            continue
        offset=rational(feature['offset'])
        key=(feature['q'],offset)
        merged[key]=merged.get(key,Q(0))+coefficient
    merged={key:c for key,c in merged.items() if c}
    admitted=syntax_ok and merged=={(2,Q(0)):Q(1)}
    return {'schema':1,'canonical_nonzero_terms':[{'kind':'floor_root','q':q,'offset':str(o),'coefficient':str(c)} for (q,o),c in sorted(merged.items())],'recognized_after_discovery':admitted,'declared_target':'Prefix(lambda * One,x), lambda=Mu * IndicatorSquares, Mu*One=Unit globally','exact_all_scale_law_proved':admitted,'quantifiers':'every integer x>=0, actual complete Dirichlet inverse Mu of One','identity':'lambda * One = IndicatorSquares; Prefix(lambda * One,x)=floor(sqrt(x))','signed_filtered_bound':'0 <= sum_(d<=x) lambda(d)*floor(x/d)=floor(sqrt(x)) <= sqrt(x)','supplied_lemma':'convolution associativity/unit law and square indicator counting','parameter_origin':'frozen sparse response law learned numerically before analytical admission','ordinary_unsmoothed_Mobius_or_Liouville_bound_proved':False,'RH_proved':False,'scope':'filtered actual arithmetic; does not bound Prefix(lambda,x) or M(x)'}


def energy_bridge_obstruction_certificate(terms, test_exponents=(3,4)):
    """Exact obstruction to an ENERGY-ONLY critical recursion inference.

    This never refutes a full actual-arithmetic claim: countermodels need not
    satisfy Mu*One=Unit. Exponent four also violates actual trivial cubic energy
    growth, and is relevant only to an unconstrained energy recurrence.
    """
    merged={}
    for scale,coefficient in terms:
        scale=rational(scale);coefficient=rational(coefficient)
        if scale<=0:
            raise ValueError('positive scales required')
        merged[scale]=merged.get(scale,Q(0))+coefficient
    merged={s:c for s,c in merged.items() if c}
    if not merged:
        raise ValueError('nonzero stencil required')
    exponents=tuple(test_exponents)
    if not exponents or any(type(t) is not int or t<=2 for t in exponents):
        raise ValueError('integer countermodel exponents strictly above two required')
    tests=[]
    for t in exponents:
        polynomial=sum((c*s**t for s,c in merged.items()),Q(0))
        tests.append({'exponent':t,'exact_dilate_polynomial':str(polynomial),'obstruction':polynomial<=0,'countermodel':'A(X)=X^'+str(t),'stencil':'('+str(polynomial)+')*X^'+str(t),'one_sided_bound_constant_if_obstructed':'0','fails_critical_energy_for_epsilon_less_than':str(t-2),'compatible_with_actual_trivial_cubic_growth':t<=3,'cubic_prefix_realization_if_t3':'a(n)=1 gives A_block(X)=(7/3)X^3-(3/2)X^2+(1/6)X; its leading cubic growth is real but a*One is not Unit'})
    return {'schema':1,'terms':[[str(s),str(c)] for s,c in sorted(merged.items())],'quadratic_moment':str(sum((c*s*s for s,c in merged.items()),Q(0))),'tests':tests,'energy_only_critical_bridge_obstructed':any(row['obstruction'] for row in tests),'scope':'abstract nonnegative energy recurrence only; not the full complete actual Mobius arithmetic conjecture','actual_Mobius_claim_disproved':False,'sampled_actual_coefficients_used':False,'supplied_lemma':'a nonnegative monomial energy is an exact one-sided stencil countermodel whenever its dilate polynomial is nonpositive','higher_zero_moments_do_not_improve_discrepancy_exponent':True}


def positive_energy_transform_certificate(terms, epsilon, max_order=256):
    """Exact P(T)=(T-4)B(T)+P(4), and a stronger CONDITIONAL bridge.

    If all B coefficients are nonnegative, H=B(T)A is nonnegative and
    dominates one dilate of A. No actual signed inequality is supplied.
    max_order caps symbolic representation work, not the mathematical theorem.
    """
    epsilon=rational(epsilon)
    if epsilon<=0:
        raise ValueError('strictly positive exponent required')
    positive_integer(max_order,'max_order')
    merged={}
    for scale,coefficient in terms:
        scale=rational(scale);coefficient=rational(coefficient)
        if scale<=0:
            raise ValueError('positive scales required')
        merged[scale]=merged.get(scale,Q(0))+coefficient
    merged={s:c for s,c in merged.items() if c}
    if not merged:
        raise ValueError('nonzero stencil required')
    canonical=[[str(s),str(c)] for s,c in sorted(merged.items())]
    base={'schema':1,'terms':canonical,'epsilon':str(epsilon),'signed_inequality_proved':False,'RH_proved':False,'scope':'conditional nonnegative transformed-energy bridge; full actual arithmetic premise remains missing'}
    if any(s.denominator!=1 or s<1 or int(s)&(int(s)-1) for s in merged):
        return {**base,'status':'unsupported_domain','factorization_admitted':False,'conditional_bridge_admitted':False,'reason':'this shift certificate requires positive integer dyadic dilates'}
    m=max(int(s).bit_length()-1 for s in merged)
    if m>max_order:
        return {**base,'status':'missing','factorization_admitted':False,'conditional_bridge_admitted':False,'reason':'symbolic_order_budget_exhausted','requested_order':m,'max_order':max_order}
    coefficients=[merged.get(Q(1<<j),Q(0)) for j in range(m+1)]
    b=[Q(0)]*m
    if m:
        b[-1]=coefficients[-1]
        for j in range(m-1,0,-1):
            b[j-1]=coefficients[j]+4*b[j]
    remainder=coefficients[0]+(4*b[0] if b else 0)
    polynomial_at_four=sum((c*4**j for j,c in enumerate(coefficients)),Q(0))
    if remainder!=polynomial_at_four:
        raise RuntimeError('shift polynomial division failed')
    positive=bool(b) and all(value>=0 for value in b) and any(value>0 for value in b)
    admitted=remainder==0 and positive
    recovery=next((j for j,value in enumerate(b) if value>0),None) if admitted else None
    return {**base,'status':'available','shift_polynomial_coefficients':list(map(str,coefficients)),'factor_coefficients':list(map(str,b)),'factor_terms':[[1<<j,str(value)] for j,value in enumerate(b)],'exact_constant_remainder':str(remainder),'quadratic_moment':str(polynomial_at_four),'factorization_identity':'P(T)=(T-4)B(T)+P(4)','factorization_admitted':remainder==0,'factor_coefficients_nonnegative_nonzero':positive,'conditional_bridge_admitted':admitted,'transformed_energy':'H(X)=sum_j b_j A(2^j X)','exact_signed_stencil_identity':'F(X)=H(2X)-4H(X)+P(4)A(X)','unsigned_factor_coefficient_l1':str(sum(map(abs,b),Q(0))),'symbolic_cells_charged':len(coefficients)+len(b),'symbolic_order':m,'max_order':max_order,'recovery_index':recovery,'recovery_scale':1<<recovery if recovery is not None else None,'recovery_coefficient':str(b[recovery]) if recovery is not None else None,'premise':'for every dyadic X>=1: F(X)<=C X^(2+epsilon), finite C>=0 independent of X','normalized_H_bound_if_admitted':'H(n)/n^2 <= H(1)+C*(n^epsilon-1)/[4*(2^epsilon-1)] for every dyadic n>=1','recovery_if_admitted':'A(n)<=H(n/2^j)/b_j for every dyadic n>=2^j; retain every smaller dyadic A(n) as initial data','finite_initial_scales':'H(1) uses finitely many A(2^i), plus A(n) for every dyadic n<recovery_scale','cofinal_scope':'RH-strength conclusion requires positive epsilon(q)->0, every q>=q0, finite Cq and all dyadic X; none is inferred from finite fits','ceil_extension':'for X>=1, C X^2 ceil(X^epsilon)<=2C X^(2+epsilon); replace C by 2C before the geometric telescope','ordinary_defect_transfer':'if b_j>=0 and Delta(Y)<=Cq Y^2 ceil(Y^(1/q)) globally, then F(X)<=Cq X^2 ceil(X^(1/q))*sum_j b_j 4^j ceil(2^(j/q)); mixed b require additional signed/lower control'}
