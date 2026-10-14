"""Exact search for recoverable divisor preconditioners and valuation gains.

The generator sees the full factored source, not a nominated winning shift.
Local simplification and paid tensor sectors do not establish signed control
of the remaining complete source.
"""
from fractions import Fraction as Q
from math import ceil, comb

SHIFTS = ('1/6','1/3','1/2','2/3','5/6','1')
POWERS = ('-2','-1','-1/2','1/2','1','2')
SOURCE_TERMS = (
    ('B','beta',{'0':Q(-2),'1/3':Q(1),'2/3':Q(1)}),
    ('U','-beta',{'0':Q(-1),'1/3':Q(1)}),
    ('V','-beta',{'0':Q(-1),'2/3':Q(1)}),
    ('power','-R_u',{'1/3':Q(1)}),
)


def recovery(shift, power):
    v,r=Q(shift),Q(power)
    if v<=0:
        raise ValueError('positive fractional shift')
    k=ceil(abs(r))
    if not r:
        return dict(cofinal=True,kind='identity',divisor_order=0,energy_power_loss='0',norm_bound='1')
    loss=max(Q(1,2)-v,Q(0))
    return dict(cofinal=loss==0,
                kind='bounded' if v>Q(1,2) else 'polylog' if v==Q(1,2) else 'unpaid_power',
                divisor_order=k,energy_power_loss=str(2*loss),
                norm_bound=('zeta('+str(v+Q(1,2))+')^'+str(k)) if v>Q(1,2)
                    else 'H^('+str(loss)+')*(1+log H)^'+str(k),
                covers_forward_and_inverse=True,
                coefficient_majorant='d_'+str(k)+'(n)*n^(-'+str(v)+')')


def generate(meter):
    rows=[]
    for shift,power in [('1','0')]+[(v,r) for v in SHIFTS for r in POWERS]:
        v,r=Q(shift),Q(power)
        terms=[]
        positive=Q(0);numerator=Q(0);max_roots=0;integral=True
        for name,coefficient,original in SOURCE_TERMS:
            factors={Q(s):e for s,e in original.items()}
            factors[v]=factors.get(v,Q(0))-r
            factors={s:e for s,e in factors.items() if e}
            positive+=sum((e for e in factors.values() if e>0),Q(0))
            numerator+=sum((-e for e in factors.values() if e<0),Q(0))
            max_roots=max(max_roots,sum(e>0 for e in factors.values()))
            integral=integral and all(e.denominator==1 for e in factors.values())
            terms.append(dict(name=name,coefficient=coefficient,
                              zeta_factors=[[str(s),str(e)] for s,e in sorted(factors.items())]))
            meter.charge(16+4*len(factors))
        rows.append(dict(id=len(rows),shift=str(v),power=str(r),
                         operator='Dirichlet convolution by coefficients of zeta(s+shift)^(-power)',
                         recovery=recovery(shift,power),terms=terms,
                         positive_factor_order=str(positive),numerator_factor_order=str(numerator),
                         max_positive_factors_in_one_term=max_roots,
                         integral_local_rational_functions=integral,
                         correction='(beta*delta-d)*preconditioner, retained with its proved global norm cost',
                         whole_signed_bound_proved=False,RH_proved=False))
    return rows


def choose(rows):
    eligible=[row for row in rows if row['recovery']['cofinal']]
    if not eligible:
        raise ValueError('at least one recoverable construction')
    # Algebraic priority, fixed before any actual-source response is evaluated.
    return min(eligible,key=lambda row:(Q(row['positive_factor_order']),
               row['max_positive_factors_in_one_term'],not row['integral_local_rational_functions'],
               Q(row['numerator_factor_order']),abs(Q(row['power'])),row['id']))


def _multiply(left,right,meter):
    out={}
    for (z,t),a in left.items():
        for (w,u),b in right.items():
            key=(z+w,t+u);out[key]=out.get(key,Q(0))+a*b
            meter.charge(4)
    return {key:value for key,value in out.items() if value}


def _divide_one_minus(poly,power,meter):
    if not poly:return None
    rest=dict(poly);quotient={}
    while rest:
        degree=max(rest);meter.charge(len(rest)+2)
        if degree<power:return None
        coefficient=-rest[degree];qdegree=degree-power
        quotient[qdegree]=quotient.get(qdegree,Q(0))+coefficient
        for j,c in ((qdegree,coefficient),(degree,-coefficient)):
            rest[j]=rest.get(j,Q(0))-c
            if not rest[j]:rest.pop(j)
    return quotient


def _bernstein(poly):
    degree=max(poly,default=0)
    return [sum((c*Q(comb(j,i),comb(degree,i)) for i,c in poly.items() if i<=j),Q(0))
            for j in range(degree+1)]


def compile_tails(row,meter):
    """Compile an exact common simple-pole recurrence if the selected AST admits it."""
    compiled=[]
    for term in row['terms']:
        factors=[(Q(s),Q(e)) for s,e in term['zeta_factors']]
        if any(e.denominator!=1 or (6*s).denominator!=1 for s,e in factors):
            return dict(status='NONINTEGRAL_LOCAL_LANGUAGE_RETAINS_GENERAL_CONVOLUTION',terms=[])
        positive=[(s,e) for s,e in factors if e>0]
        if len(positive)>1 or any(e!=1 for s,e in positive):
            return dict(status='MULTIPLE_LOCAL_POLES_RETAINED',terms=[])
        numerator={(0,0):Q(1)}
        for shift,exponent in factors:
            if exponent<0:
                for _ in range(int(-exponent)):
                    numerator=_multiply(numerator,{(0,0):Q(1),(1,int(6*shift)):Q(-1)},meter)
        degree=max(z for z,t in numerator)
        start=max(2,degree)
        if not positive:
            if degree>=2:
                return dict(status='FINITE_POLYNOMIAL_HEAD_NEEDS_SEPARATE_SECTORS',terms=[])
            compiled.append(dict(name=term['name'],zero_above_first_valuation=True,
                                 tail_start=2,tail=[],valuation_mass_power=None,
                                 cofactor_divisor_order=2))
            continue
        pole=int(6*positive[0][0])
        if pole<=0:return dict(status='UNWEIGHTED_LOCAL_POLE',terms=[])
        tail={}
        for (z,t),coefficient in numerator.items():
            if z<=start:
                exponent=t+pole*(start-z)
                tail[exponent]=tail.get(exponent,Q(0))+coefficient
                meter.charge(5)
        tail={e:c for e,c in tail.items() if c}
        if not tail:return dict(status='DEGENERATE_TAIL_NEEDS_EXPLICIT_HEAD',terms=[])
        remaining=dict(tail);multiplicity=0
        while True:
            quotient=_divide_one_minus(remaining,pole,meter)
            if quotient is None:break
            remaining=quotient;multiplicity+=1
        if len(remaining)!=1 or multiplicity<1 or start!=2:
            return dict(status='TAIL_REQUIRES_GENERAL_ENVELOPE',terms=[])
        power,constant=next(iter(remaining.items()))
        # n=p has coefficient of z; the tail is <=1 on x in[0,1]
        # once its geometric mass certificate is <=1. This pays all cofactors by d2.
        first={pole:Q(1)}
        for (z,t),coefficient in numerator.items():
            if z==1:first[t]=first.get(t,Q(0))+coefficient
        first={e:c for e,c in first.items() if c}
        bernstein=_bernstein(first)
        cofactor_ok=abs(constant)<=1 and all(abs(v)<=2 for v in bernstein)
        compiled.append(dict(name=term['name'],zero_above_first_valuation=False,
            tail_start=start,tail=[[e,str(c)] for e,c in sorted(tail.items())],
            common_ratio_power=pole,
            factorization=dict(monomial_power=power,coefficient=str(constant),
                               one_minus_power=pole,multiplicity=multiplicity),
            valuation_mass_power=str(Q(power,6)),valuation_mass_constant=str(abs(constant)),
            recurrence='coefficient(p^e)=tail(x)*x^(common_ratio_power*(e-2)), x=p^(-1/6), e>=2',
            first_valuation_bernstein=list(map(str,bernstein)),
            cofactor_divisor_order=2 if cofactor_ok else None))
    if not all(t['cofactor_divisor_order']==2 for t in compiled):
        return dict(status='COFACTOR_BOUND_UNRESOLVED',terms=compiled)
    return dict(status='COMPLETE_REPEATED_VALUATION_TAILS_CERTIFIED',terms=compiled,
                all_prime_powers_retained=True,whole_signed_bound_proved=False,RH_proved=False)


def tensor_sectors(tails,meter):
    if tails['status']!='COMPLETE_REPEATED_VALUATION_TAILS_CERTIFIED':return []
    rows=[]
    for left in tails['terms']:
        for right in tails['terms']:
            if left['zero_above_first_valuation'] or right['zero_above_first_valuation']:
                rows.append(dict(left=left['name'],right=right['name'],status='ZERO_ON_SHARED_SQUARE'))
                continue
            weight=Q(left['valuation_mass_power'])+Q(right['valuation_mass_power'])
            constant=Q(left['valuation_mass_constant'])*Q(right['valuation_mass_constant'])*(1+1/(3+weight))
            rows.append(dict(left=left['name'],right=right['name'],status='UNIFORM_ABSOLUTE_SECTOR_ENVELOPE',
                prime_weight=str(weight),cofinal_rho_threshold=str(1/(3+weight)),constant=str(constant),
                coefficient_scope='unscaled multiplicative modes; multiply by abs(c_left*c_right) from the selected full source before combining sectors',
                bound='constant*2^max(2-(3+prime_weight)*rho,0)*X^(1-(3+prime_weight)*rho)*(1+log(2X))^2',
                domain='union of pairs sharing q^2 for some actual prime q>n^rho; all q-valuations e,f>=2; n in[X,2X)',
                union_subtracted_once=True,full_target_recovered=False,whole_signed_bound_proved=False))
            meter.charge(40)
    return rows
