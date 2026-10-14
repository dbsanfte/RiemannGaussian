"""Generic joint-factor discovery on archived distinct-prime tensor words.

No source table is regenerated. Diagonal vanishing, exact kernel differences,
and the number of independently summed prime edges are separate proof inputs.
"""
from fractions import Fraction as Q
from itertools import product
from math import gcd


def linear_forms():
    forms=[]
    for row in product(range(-2,3),repeat=3):
        if not any(row[:2]) or gcd(*row)!=1:continue
        if next(c for c in row if c)<0:continue
        forms.append(list(row))
    return sorted(forms)


def decode(poly):return {tuple(e):Q(c) for e,c in poly}
def serial(poly):return [[list(e),str(c)] for e,c in sorted(poly.items()) if c]


def add(a,b,meter,scale=1):
    out=dict(a)
    for e,c in b.items():
        meter.charge(3);out[e]=out.get(e,Q(0))+scale*c
        if not out[e]:del out[e]
    return out


def divide(poly,form,meter):
    """Exact sparse long division; independent checker uses substitution."""
    a,b,c=form;axis=0 if a else 1;leading=Q(a if a else b)
    divisor={(1,0):Q(a),(0,1):Q(b),(0,0):Q(c)}
    divisor={e:v for e,v in divisor.items() if v};rest=dict(poly);quotient={}
    while rest:
        exponent=max(rest,key=lambda e:(e[axis],e[1-axis]));meter.charge(2+len(rest))
        if exponent[axis]==0:return None
        power=list(exponent);power[axis]-=1;power=tuple(power)
        coefficient=rest[exponent]/leading;quotient[power]=quotient.get(power,Q(0))+coefficient
        shifted={tuple(e[i]+power[i] for i in range(2)):v*coefficient for e,v in divisor.items()}
        rest=add(rest,shifted,meter,-1)
    return {e:c for e,c in quotient.items() if c}


def factor_tensor(original,meter):
    if len(original)!=9 or not any(original):raise ValueError('nonzero nine-component tensor')
    residual=[decode(p) for p in original];factors=[]
    for form in linear_forms():
        multiplicity=0
        while True:
            divided=[]
            for polynomial in residual:
                quotient=divide(polynomial,form,meter)
                if quotient is None:break
                divided.append(quotient)
            if len(divided)!=9:break
            residual=divided;multiplicity+=1
            if multiplicity>24:raise OverflowError('factor degree cap')
        if multiplicity:factors.append(dict(coefficients=form,multiplicity=multiplicity))
    return factors,[serial(p) for p in residual]


def ordered_factor_envelope(factors,quotients,meter):
    """On 0<x<y<1, extract powers of y, retaining every tensor component."""
    common_degree=0;constant=Q(1)
    for factor in factors:
        a,b,c=factor['coefficients'];m=factor['multiplicity']
        if c==0:
            common_degree+=m;bound=max(abs(b),abs(a+b))
        else:bound=max(abs(c),abs(b+c),abs(a+b+c))
        constant*=bound**m;meter.charge(8+m)
    orders=[];norms=[]
    for polynomial in quotients:
        orders.append(common_degree+min(sum(e) for e,c in polynomial) if polynomial else None)
        norms.append(str(constant*sum(abs(Q(c)) for e,c in polynomial)));meter.charge(4*len(polynomial)+2)
    nonzero=[e for e in orders if e is not None]
    return dict(domain='0<x<y<1; x=q^(-1/3), y=r^(-1/3), actual primes r<q',
                component_total_orders=orders,common_total_order=min(nonzero),
                component_constants=norms,prime_weight=str(Q(min(nonzero),3)),
                coefficient_envelope='each component <= component_constant*r^(-prime_weight)',
                whole_signed_bound_proved=False)


def antisymmetric_program(program):
    if program['binding']!='distinct_primes':return False
    coefficients={tuple(t['left']+t['right']):t['coefficient'] for t in program['terms']}
    if len(coefficients)!=len(program['terms']):return False
    for (a,b,c,d),value in coefficients.items():
        if coefficients.get((b,a,d,c),0)!=-value:return False
    return bool(coefficients)


def edge_bound(theta_text,weight_text,degree_text,meter):
    theta,weight,degree=map(Q,(theta_text,weight_text,degree_text))
    if not Q(1,2)<=theta<1 or weight<=0 or degree<=0:raise ValueError('positive weight and uniform outgoing degree')
    exponent=1-theta*(1+weight);meter.charge(16)
    return dict(theta=str(theta),weight=str(weight),degree=str(degree),
                energy_upper_power=str(exponent),logdegree=2,
                constant_multiplier=str(2*degree*(2+weight)/(1+weight)),
                constant_power_of_two=str(max(2-theta*(1+weight),Q(0))),cofinal=exponent<=0,
                both_orientation_supports_retained=True,growing_degree_graphs_admitted=False,
                full_domain_recovery='OPEN',whole_signed_bound_proved=False)


def record(row,meter):
    factors,quotients=factor_tensor(row['multipliers'],meter)
    envelope=ordered_factor_envelope(factors,quotients,meter)
    alternating=antisymmetric_program(row['program'])
    # The full quadratic projection here is p*p, not the old z0*z0 bank score.
    # On a cross-placement both legs have a fresh prime and base>=2, hence p=a.
    cross_placements=all(sum(t['left'])==sum(t['right'])==1 for t in row['program']['terms'])
    admissible=alternating and cross_placements
    kernel_constant=Q(81,16)*sum(Q(c) for c in envelope['component_constants'])
    edges=[]
    if admissible and Q(envelope['prime_weight'])>0:
        for degree in ('1','2','4'):
            bound=edge_bound('3/4',envelope['prime_weight'],degree,meter)
            edges.append(dict(graph='next_'+degree+'_actual_prime_neighbours',
                definition='each prime r points to its next degree larger primes; both endpoints satisfy the original cutoff',
                degree_independent_of_X=True,C=str(kernel_constant),bound=bound,
                bound_scope='signed exchange CORRECTION only; both orientation kernels retained',
                original_target_recovered=False))
    return dict(parent_id=row['id'],program=row['program'],original=row['multipliers'],
                factors=factors,quotients=quotients,envelope=envelope,
                prime_swap_antisymmetric=alternating,full_kernel_correction_admissible=admissible,
                constant_for_correction_over_four=str(kernel_constant),edge_constructions=edges,
                projection='beta^2*(B-au-av) tensor (B-au-av); units excluded',
                kernel_A='max(0,min(2X,tau_theta(r))-max(X,q*H,r*K))',
                kernel_B='max(0,min(2X,tau_theta(r))-max(X,r*H,q*K))',
                kernel_domain='r<q primes; H,K>=2; complete union of both supports; gcd(H,K) unrestricted',
                quadratic_identity='(P_A*K_A+P_B*K_B)/2 = (P_A+P_B)*(K_A+K_B)/4 + (P_A-P_B)*(K_A-K_B)/4',
                symmetric_core='OPEN',same_prime_and_cross_divisibility_sectors='OPEN',
                complete_prime_graph_recovery='OPEN',whole_signed_bound_proved=False,RH_proved=False)


def entry(prime,theta_text,meter):
    theta=Q(theta_text)
    if type(prime) is not int or prime<2 or not Q(1,2)<=theta<1 or theta.denominator>32:
        raise ValueError('positive prime argument and bounded exact cutoff')
    low=prime;high=prime*prime;target=prime**theta.denominator
    while low<high:
        middle=(low+high)//2;meter.charge(8)
        if middle**theta.numerator>=target:high=middle
        else:low=middle+1
    return low


def kernels(X,q,r,H,K,theta_text,meter):
    if any(type(v) is not int or v<1 for v in (X,q,r,H,K)) or not q>r>=2 or min(H,K)<2:
        raise ValueError('complete ordered index domain')
    top=min(2*X,entry(r,theta_text,meter));meter.charge(12)
    return (max(0,top-max(X,q*H,r*K)),max(0,top-max(X,r*H,q*K)))
