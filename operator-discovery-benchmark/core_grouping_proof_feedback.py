"""Generated source/support certificates that refute grouped-majorant routes.

These rules concern the complete grouping absolute sum, never the original
signed core conjecture. Proof templates are documented in review010.
"""
from fractions import Fraction as Q
from flint import arb


def scalars(Ru):return {'beta':arb(9)/2,'-beta':-arb(9)/2,'-R_u':-Ru}


def semiprime_gate(program,source,Ru,meter):
    base,post=program['base'],program['post']
    if base['valuation_step']!=1 or base['cutoff']!={'kind':'power','value':'1/2'} or post['op'] not in (
        'remove_largest_once','remove_smallest_once','remove_largest_all'):return None
    weights=scalars(Ru);distinct=repeated=arb(0);terms=[]
    for term in source['terms']:
        e=sum((Q(power) for shift,power in term['zeta_factors'] if Q(shift)==0),Q(0))
        if e.denominator!=1 or any(Q(shift)<0 for shift,power in term['zeta_factors']):
            raise ValueError('complete finite integral local asymptote')
        w=weights[term['coefficient']]
        distinct+=w*int(e)**2;repeated+=w*int(e*(e+1)/2)
        terms.append(dict(name=term['name'],first_prime_limit=str(e),second_valuation_limit=str(e*(e+1)/2)))
        meter.charge(100)
    if not distinct>0 or not repeated>0:return None
    smallest=post['op']=='remove_smallest_once'
    return dict(rule='complete_positive_fresh_semiprime_classes',local_limits=terms,
        distinct_prime_coefficient_limit=str(distinct),repeated_prime_coefficient_limit=str(repeated),
        label_prime_band=['41/20','21/10'] if smallest else ['29/20','3/2'],
        complementary_prime_band=['101/100','21/20'] if smallest else ['8/5','33/20'],
        bands_normalized_by='sqrt(X)',
        support_proof='after stripping primes<=floor(sqrtX), at most two prime factors remain; chosen prime-key classes consist ENTIRELY of semiprimes above2X; all smooth multiples exit4X',
        repeated_prime_scope='absent in smallest-removal fresh band; positive in largest-once; sent to unit by largest-all',
        required_kernel='identity-filter eta1, child2X minus parentX/2; positive on all retained classes and>=3/(40X) on displayed product bands',
        unconditional_lower_bound='grouped_absolute_sum >= c*X/(log X)^4 for all sufficiently large X, c>0',
        imported_theorems=['prime number theorem in fixed relative intervals'],
        uniform_group_bound_disproved=True,original_signed_target_disproved=False,
        whole_signed_bound_proved=False,RH_proved=False)


def residue_mask(program):
    base,post=program['base'],program['post']
    if post['op']!='residue' or post['value'] not in ('2','3','6'):return None
    primes={'2':[2],'3':[3],'6':[2,3]}[post['value']]
    cut=base['cutoff'];conditions=[]
    for p in primes:
        if cut['kind']=='none':stripped=False
        elif cut['kind']=='fixed':stripped=p<=int(cut['value'])
        elif cut['kind'] in ('power','log2'):stripped=True
        else:raise ValueError('cutoff AST')
        if stripped and base['valuation_step']==1:return None # zero label is empty
        conditions.append(dict(prime=p,valuations='odd' if stripped else 'positive'))
    return dict(group_label=0,conditions=conditions,stable_for_every_dyadic_X_at_least=1024,
        explanation='removing other prime factors preserves divisibility; removed pairs retain valuation parity; all generated growing cutoffs include primes2,3 byX1024')


def _local(term,p,z,meter):
    x=1/arb(p).root(6);out=arb(1)
    for shift,exponent in term['zeta_factors']:
        s,e=Q(shift),Q(exponent)
        if (6*s).denominator!=1 or e.denominator!=1:raise ValueError('exact local rational language')
        out*=(1-x**int(6*s)*z)**(-int(e));meter.charge(100)
    return out


def mask_pole_gate(program,source,Ru,meter):
    mask=residue_mask(program)
    if mask is None:return None
    sigma=Q(2,3);weights=scalars(Ru);residue=arb(0);terms=[]
    for term in source['terms']:
        pole=sum((Q(e) for s,e in term['zeta_factors'] if sigma+Q(s)==1),Q(0))
        if pole not in (0,1):raise ValueError('reviewed simple real pole language')
        if not pole:
            terms.append(dict(name=term['name'],simple_pole_residue='0',reason='analytic at2/3'));continue
        r=weights[term['coefficient']]
        for shift,exponent in term['zeta_factors']:
            a=sigma+Q(shift);e=Q(exponent)
            if e.denominator!=1:raise ValueError('integral zeta factor')
            if a!=1:r*=(arb(a.numerator)/a.denominator).zeta()**int(e);meter.charge(256)
        factors=[]
        for condition in mask['conditions']:
            p=condition['prime'];z=(1/arb(p).root(3))**2;L=_local(term,p,z,meter)
            if L.contains(0):raise ArithmeticError('nonzero complete local denominator')
            selected=L-1 if condition['valuations']=='positive' else (L-_local(term,p,-z,meter))/2
            factor=selected/L;r*=factor;factors.append(dict(prime=p,valuations=condition['valuations'],factor=str(factor)))
        residue+=r;terms.append(dict(name=term['name'],simple_pole_residue=str(r),local_mask_factors=factors))
    if not residue.is_finite() or residue.contains(0):return None
    return dict(rule='fixed_valuation_class_restores_supercritical_pole',mask=mask,pole='2/3',residue=str(residue),terms=terms,
        kernel_identity='Q_00(X)=W_mask(2X)-W_mask(X)/2; mask is the SAME complete coefficient sequence at everyX>=1024',
        implication_chain=['uniform grouped absolute polylog bound bounds Q_00 from above',
            'signed scalar recurrence bounds W_mask with a fixed polylog degree',
            'universal causal Volterra recovery gives critical prefix block energy of masked source',
            'dyadic Cauchy-Schwarz and Mellin integral give holomorphy of its Dirichlet series forRe(s)>1/2',
            'nonzero residue at2/3 contradicts that conclusion'],
        head_and_units='finite head retained in recovery; the mask unit is zero, not an omitted original term',
        uniform_group_bound_disproved=True,original_signed_target_disproved=False,
        whole_signed_bound_proved=False,RH_proved=False)


def evaluate(row,source,Ru,meter):
    certificate=semiprime_gate(row['program'],source,Ru,meter)
    if certificate is None:certificate=mask_pole_gate(row['program'],source,Ru,meter)
    return dict(program_id=row['id'],proof_status='grouped_polylog_bound_disproved' if certificate else 'no_new_uniform_certificate',
        certificate=certificate,uniform_group_bound_disproved=bool(certificate),
        original_signed_target_disproved=False,whole_signed_bound_proved=False,RH_proved=False)


def square_lift_head(program,Ru,log_cutoff_power,meter):
    """Pay a COMPLETE low-cell sector and emit its remaining signed obligation."""
    base,post=program['base'],program['post'];a=Q(log_cutoff_power)
    if base['valuation_step']!=2 or post['op']!='root' or post['value'] not in ('2','3','6'):
        return None
    if not a>=0 or not (Ru>0 and Ru<5):raise ValueError('uniform head parameters and complete source coefficient envelope')
    k=int(post['value']);K=Q(37,2)
    # log2<1, logL<=L, J+1<=2L^a, 1+log4X<=3L; L=1+log2X.
    constant=6*K*K*2**k*(1+k*(1+a))**2*3**4
    degree=a*k+6;meter.charge(400)
    return dict(rule='square_lift_complete_low_cell_sector',root_degree=k,log_cutoff_power=str(a),
        cutoff='J(X)=floor((1+log2X)^a)',partition_scope='the SAME label_X on all indices1..4X-1 in both parent and child',
        exact_index_decomposition='n=r*d^2; r is the valuation-mod2 residual, all prime factors ofd are in the stripping set',
        complete_coefficient_majorant='|f(n)|<=(37/2)*d2(n), using ALL four modes and0<R_u<5',
        divisor_rule='d2(r*d^2)<=d2(r)*d3(d); local difference binom(e+2,2)-(2e+1)=e(e-1)/2>=0',
        summed_rule='sum_(d<=y)d3(d)<=y*(1+log y)^2; sum_(r<=R)d2(r)/sqrt(r)<=2sqrt(R)*(1+log R)',
        prefix_mass='sum_(j<=J)sum_(n<=x,label_X(n)=j)|f(n)|<=A_J*sqrt(x)*(1+log x)^2',
        A_J='2*(37/2)*(J+1)^(k/2)*(1+k*log(J+1))',
        exact_head_envelope='sum_(j,l<=J)|Q_jl(X)|<=(3/2)*log2*A_J^2*(1+log4X)^4',
        rational_polylog_constant=str(constant),rational_polylog_degree=str(degree),
        proved_bound='sum_(j,l<=J)|Q_jl(X)|<=rational_polylog_constant*(1+log2X)^rational_polylog_degree',
        domain='every dyadic X>=1024; identity-filter eta1,rho1/2; full original core',
        low_low_sector_uniformly_paid=True,
        signed_remainder='R_J(X)=sum_(max(j,l)>J(X))Q_jl(X)',
        exact_reconstruction='Delta W_1(X)=sum_(j,l<=J(X))Q_jl(X)+R_J(X)',
        remaining_lemma='a uniform one-sided cofinal upper bound for R_J(X); any fixed polylog upper bound suffices',
        ordered_low_high_high_low_and_high_high_retained=True,
        remainder_independently_bounded=False,full_candidate_uniform_bound_proved=False,
        whole_signed_bound_proved=False,RH_proved=False)
