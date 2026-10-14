"""Reduce prime-power filters and expose their exact unpaid recovery terms.

This is post-analysis of an immutable exact search, not another candidate sweep.
The local recurrence is a reviewed analytical input. Its polynomial application
is checked against the independently expanded, saved source multipliers.
"""
from fractions import Fraction as Q

import check_prime_slide_discovery as C

BASIS=((0,0),(0,1),(1,0),(1,1))
TARGET_SCOPE=dict(source='actual_mu_candidate10',domain='all dyadic integers X>=1',
                  quantifiers='for every epsilon>0, exists C_epsilon independent of X')
TARGET_CLASS='candidate10_complete_prime_bank_covariance'


def add(a,b,meter,scale=1):
    result=dict(a)
    for degree,c in b.items():
        meter.charge(2);result[degree]=result.get(degree,0)+scale*c
        if not result[degree]:del result[degree]
    return result


def multiply(a,b,meter):
    result={}
    for e,c in a.items():
        for f,d in b.items():
            meter.charge(4);result[e+f]=result.get(e+f,0)+c*d
    return {e:c for e,c in result.items() if c}


def prefix_modes(maximum,meter):
    """C_m=sum_{e=0}^m T(q^e), reduced to the two actions I,T(q).

For each source, the prefix local generating function has common denominator
1-(t+t^2)z+t^3*z^2 and numerator of degree at most one. Thus the recurrence
holds for every m>=2, not merely the first six sampled prime-power rows.
"""
    if type(maximum) is not int or not 0<=maximum<=6:raise ValueError('frozen exponent domain0..6')
    rows=[({0:1},{})]
    if maximum:rows.append(({0:1},{0:1}))
    for m in range(2,maximum+1):
        rows.append(tuple(add(multiply({1:1,2:1},rows[m-1][j],meter),
                              multiply({3:1},rows[m-2][j],meter),meter,-1) for j in range(2)))
    return rows


def raw_modes(maximum,meter):
    prefixes=prefix_modes(maximum,meter)
    return [prefixes[0]]+[tuple(add(prefixes[e][j],prefixes[e-1][j],meter,-1) for j in range(2))
                          for e in range(1,maximum+1)]


def reduce_program(program,meter):
    binding,_,terms=C.validate(program)
    if binding!='same_prime':raise ValueError('one free prime for this reduction')
    maximum=max(max(term['left'][0],term['right'][0]) for term in terms)
    modes=raw_modes(maximum,meter);result={pair:{} for pair in BASIS}
    for term in terms:
        for a,b in BASIS:
            product=multiply(modes[term['left'][0]][a],modes[term['right'][0]][b],meter)
            result[a,b]=add(result[a,b],product,meter,term['coefficient'])
    return [dict(left=a,right=b,polynomial=[[e,c] for e,c in sorted(result[a,b].items())])
            for a,b in BASIS if result[a,b]]


def verify_reduction(row,reduction,meter):
    """Convolve with independently constructed local rows for each tensor."""
    reconstructed=[{} for _ in range(9)];seen=[]
    for term in reduction:
        pair=term['left'],term['right']
        if pair not in BASIS or pair in seen:raise ValueError('distinct low-order basis actions')
        seen.append(pair)
        polynomial=term['polynomial']
        if (not polynomial or any(type(e) is not int or not 0<=e<=24 or type(c) is not int or c==0 for e,c in polynomial)
            or polynomial!=sorted(polynomial) or len({e for e,c in polynomial})!=len(polynomial)):
            raise ValueError('canonical nonnegative polynomial weights')
        program=dict(binding='same_prime',terms=[dict(coefficient=1,left=[pair[0]],right=[pair[1]])])
        base=C.facts(program,meter)['multipliers']
        for i,component in enumerate(base):
            product=multiply(dict(polynomial),{e[0]:c for e,c in component},meter)
            reconstructed[i]=add(reconstructed[i],product,meter)
    expected=[[[[e],c] for e,c in sorted(poly.items())] for poly in reconstructed]
    if expected!=row['multipliers']:raise ArithmeticError('complete tensor reduction mismatch')
    return True


def pullback_terms(row):
    """All original masks apply to the inverse images, never the lifted values."""
    if row['program']['binding']!='same_prime':raise ValueError('same-prime pullback')
    output=[]
    for term in row['program']['terms']:
        e,f=term['left'][0],term['right'][0]
        if e==f==0:continue
        output.append(dict(coefficient=term['coefficient'],left_power=e,right_power=f,
            substitution=dict(H=f'q^{e}*h',K=f'q^{f}*k'),
            valuation_guards=dict(v_q_H=e,v_q_K=f),
            source='beta^2*(B(H)-a_u(H)-a_v(H))*(2*B(K)-a_u(K)-a_v(K))',
            inverse_image_domain='h=H/q^e>=2 has at least two distinct prime factors; k=K/q^f>=2',
            kernel='max(0,min(2X,tau(q))-max(X,H/q^e,tau(Pplus(H/q^e)),q*K/q^f))',
            high_smooth_extra_upper_limit='(H/q^e)^2',
            theta_range='1/2<=theta<1',
            original_smooth_bank_domain='outside: q divides a lifted coordinate',
            left_prefix=('outside n-prefix on the high-smooth base' if e else 'unchanged'),
            right_prefix=('outside n-prefix' if f>=2 else 'inside n-prefix, nonsmooth' if f==1 else 'unchanged'),
            obligation_status='open'))
    return output


def analyse_row(row,meter):
    reduction=reduce_program(row['program'],meter);verify_reduction(row,reduction,meter)
    minimum=min((e for t in reduction for e,c in t['polynomial']),default=None)
    baseline=row['baseline_coefficient']
    # The lifted sum equals O-c0*I exactly. Its constant tensor coefficient is
    # retained even when O vanishes to high order at the infinite-prime limit.
    lift_constants=[]
    for component in row['multipliers']:
        meter.charge(len(component)+1)
        lift_constants.append(sum(c for e,c in component if e==[0])-baseline)
    return dict(candidate_id=row['id'],reduced_basis=reduction,
                reduction_independently_verified=True,least_basis_weight=str(Q(minimum,3)) if minimum is not None else None,
                baseline_coefficient=baseline,lifted_constant_tensor=lift_constants,
                pullbacks=pullback_terms(row),
                recovery_identity='auxiliary=baseline_coefficient*original_covariance+sum(all lifted terms)',
                reduction_scope='local source identities under original coprime masks and fixed kernel',
                original_target_recovered=False,whole_signed_bound_proved=False,RH_proved=False)


def bounded_local_recovery_obstruction(rows,meter):
    """A witness component suffices to rule out bounded scalar inversion.

If sum_j c_j(q) M_j(q)=I as an operator on all nine tensor components,
then the B,B entry equals one. With degree>=m>0 and l1 norm L_j there,
max_j |c_j(q)| >= q^(m/3)/sum_j L_j. This is a local operator statement;
it neither excludes arithmetic restrictions nor a signed integrated proof.
"""
    if not rows:raise ValueError('nonempty finite operator bank')
    orders=[];norm=0
    for row in rows:
        if row['program']['binding']!='same_prime':raise ValueError('common one-prime domain required')
        component=row['multipliers'][0];meter.charge(2*len(component)+1)
        if not component:continue
        if any(type(e) is not list or len(e)!=1 or type(e[0]) is not int or e[0]<0 or type(c) is not int or c==0 for e,c in component):
            raise ValueError('exact nonnegative one-variable polynomial')
        orders.append(min(e[0] for e,c in component));norm+=sum(abs(c) for e,c in component)
    if not orders or min(orders)==0:
        return dict(status='no_positive_order_obstruction_certified',whole_signed_bound_proved=False,RH_proved=False)
    order=min(orders)
    return dict(status='bounded_local_linear_recovery_excluded',candidate_ids=[r['id'] for r in rows],
                witness_tensor='B(h)*B(k)',prime_weight=str(Q(order,3)),polynomial_l1_sum=norm,
                necessary_coefficient_growth=f'max_j abs(c_j(q)) >= q^({Q(order,3)})/{norm}',
                premise='sum_j c_j(q)*O_j=I on all source tensor components at the same prime and base pair',
                excluded_class='finitely many filters with uniformly bounded scalar recovery coefficients',
                not_excluded=['q-dependent coefficients with recorded growth','additional arithmetic relations',
                              'signed integrated cancellation','changed kernels and complete domain compensation',
                              'well-founded coupled scale recurrences'],
                whole_signed_bound_proved=False,RH_proved=False)


def feedback(parent,analyses,local_obstruction,selected_id):
    if parent.get('schema')!='prime-slide-recovery-obligation-v1' or parent.get('status')!='open':
        raise ValueError('open exact recovery parent required')
    if parent.get('whole_signed_bound_proved') or parent.get('RH_proved'):raise ValueError('unresolved parent required')
    if parent.get('scope')!=TARGET_SCOPE or parent.get('equivalence_class')!=TARGET_CLASS:
        raise ValueError('same actual source, complete domain and quantifiers')
    match=[r for r in analyses if r['candidate_id']==selected_id]
    if len(match)!=1 or match[0]['baseline_coefficient']==0:raise ValueError('one baseline-containing candidate')
    analysis=match[0]
    return dict(schema='prime-slide-integrated-recovery-obligation-v1',status='open',
                source='actual_mu_candidate10',scope=parent['scope'],equivalence_class=parent['equivalence_class'],
                selected_candidate_id=selected_id,exact_recovery=analysis,
                local_recovery_obstruction=local_obstruction,
                required_bound=dict(expression='X^-2*sum_{X<=n<2X} complete joint square of K-L0+Lu-main',
                                    growth='for every epsilon>0: <=C_epsilon*X^epsilon',
                                    constants_uniform_in='X',all_cross_terms_retained=True),
                next_constructions=['pair complete pulled-back kernels including every outside support',
                    'use local recurrence to reduce higher prime powers to weighted I,T_q actions',
                    'couple centered smaller-cofactor states with smooth and deterministic prime-bank compensation'],
                automatic_credit_for_more_local_suppression=False,
                conditional_lemma=dict(provenance='PRIME_TRANSFER_MARTINGALE_REVIEW_001.txt equation9.5',
                    coupled_state='W0=2*J+beta*(M_u+M_v), beta=9/2; all real-pole centers retained',
                    premise='sum_{m<=T}|W0(m)|^2 <= A_epsilon*T^(2+epsilon) from the SAME closed induction',
                    conclusion='centered shared-prime square <=2^(2+epsilon)*A_epsilon*(1+1/epsilon)*X^((1-theta)*epsilon)',
                    horizon='T<=2*X^(1-theta)',closed_induction_proved=False,
                    unpaid=['centered distinct-prime covariance','smooth/common-bank covariance',
                            'deterministic pole and mixed pole terms','companion-state induction steps']),
                whole_signed_bound_proved=False,RH_proved=False)
