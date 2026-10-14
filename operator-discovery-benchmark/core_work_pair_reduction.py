"""Compile signed-work candidates to exact pair kernels and proof obstructions.

Profiles concern actual coefficient masses; they do not bound signed sums.
The global divisor-counting arguments are recorded in the two008 reviews.
"""
from fractions import Fraction as Q
from math import comb
from flint import arb
import check_joint_preconditioner as CHECK
import check_core_signed_work as WORK_CHECK
import joint_preconditioner_discovery as LOCAL


def clean(p):return {i:c for i,c in p.items() if c}


def multiply(a,b):
    c={}
    for i,x in a.items():
        for j,y in b.items():c[i+j]=c.get(i+j,Q(0))+x*y
    return clean(c)


def encode(p):return [[i,str(c)] for i,c in sorted(p.items())]


def source_profile(program,tails,meter):
    CHECK.verify_tails(program,tails,meter)
    rows=[]
    for term,tail in zip(program['terms'],tails['terms']):
        first={}
        for shift,e in term['zeta_factors']:
            power=6*Q(shift)
            if power.denominator!=1:raise ValueError('sixth lattice')
            first[int(power)]=first.get(int(power),Q(0))+Q(e)
        first=clean(first)
        rows.append(dict(name=term['name'],scalar=term['coefficient'],first=first,
                         tail={i:Q(c) for i,c in tail['tail']},
                         ratio=tail.get('common_ratio_power',0),tail_certificate=tail))
    pairs=[]
    for a in rows:
        for b in rows:
            first=multiply(a['first'],b['first']);k=first.get(0,Q(0))
            if k.denominator!=1 or k<0:raise ValueError('nonnegative integral Hadamard zeta order')
            residual=dict(first);residual[0]=residual.get(0,Q(0))-k;residual=clean(residual)
            if 0 in residual:raise ArithmeticError('complete zeta linear cancellation')
            threshold=max(Q(1,2),1-Q(min(residual),6)) if residual else Q(1,2)
            tail=multiply(a['tail'],b['tail'])
            pairs.append(dict(left=a['name'],right=b['name'],zeta_order=int(k),
                first_valuation=encode(first),tail_at_valuation2=encode(tail),
                geometric_ratio_power=a['ratio']+b['ratio'] if tail else None,
                regular_linear_term=encode(residual),absolute_convergence_Re_s_greater_than=str(threshold),
                local_identity='1+first(x)*z+tail(x)*z^2/(1-x^ratio*z); tail zero means omit that term',
                regularization='multiply the complete local identity by(1-z)^zeta_order; x=p^-1/6,z=p^-s'))
            meter.charge(150)
    order=max(p['zeta_order'] for p in pairs);leaders=[p for p in pairs if p['zeta_order']==order]
    if len(leaders)!=1 or leaders[0]['left']!=leaders[0]['right']:raise ValueError('unresolved leading mode cancellation')
    leader=leaders[0];dominant=next(r for r in rows if r['name']==leader['left'])
    if dominant['scalar']!='beta' or order!=4:raise ValueError('reviewed complete source scope')
    bernstein=LOCAL._bernstein(dominant['first'])
    if not all(v<0 for v in bernstein):raise ValueError('constant first-valuation sign needed for absolute profile')
    for row in rows:
        if row is dominant:continue
        if any(abs(v)>1 for v in LOCAL._bernstein(row['first'])):raise ValueError('bounded companion first valuation')
        t=row['tail_certificate']
        if not t['zero_above_first_valuation']:
            f=t['factorization']
            if abs(Q(f['coefficient']))>1 or f['monomial_power']<0 or f['multiplicity']<1:raise ValueError('bounded companion complete tail')
    t=dominant['tail_certificate'];f=t['factorization']
    if Q(f['coefficient'])<=0:raise ValueError('positive dominant complete geometric tail')
    absolute_first={i:-c for i,c in dominant['first'].items()}
    absolute_order=int(absolute_first.get(0,0))
    return dict(schema='complete-core-Hadamard-mass-profile-v1',hadamard_pairs=pairs,
        dominant_mode=dominant['name'],dominant_square_zeta_order=order,dominant_absolute_zeta_order=absolute_order,
        dominant_absolute_first=encode(absolute_first),dominant_absolute_tail=encode(dominant['tail']),
        dominant_absolute_ratio_power=dominant['ratio'],bounded_companion_modes=True,
        squared_coefficient_mass='sum_(n<=x) g(n)^2=c_a*x*(log x)^3+O_a(x*(log x)^2), c_a=beta^2*H_a(1)/6>0',
        absolute_coefficient_mass='sum_(n<=x)|g(n)|=d_a*x*log x+O_a(x), d_a=beta*J_a(1)>0',
        finite_prime_delay_extension='g(n)=f(n)-a*1_(2 divides n)*f(n/2); replace only the dominant local factor at2; its unit keeps H_a(1),J_a(1)>0',
        complete_work_diagonal_log_degree=order-1,
        complete_work_diagonal='D_eta(X)=c_a*log(2)*(log X)^3+O_a((log X)^2), uniformly|eta|<=2',
        full_termwise_absolute_step_growth='Theta_a(X*(log X)^2), uniformly|eta|<=2,0<=rho<=1',
        comparable_pair_kernel_lower='K_eta,Y(h,k)>=3/(20Y) forY>=8 andh,k in[Y,5Y/4]; useY=2X for the step',
        global_proof_dependencies=['exact complete Euler tails','absolute convergence of regular Euler products forRe(s)>2/3',
             'elementary divisor summation for d2/d4 and absolutely summable convolution','Abel summation on exact shells'],
        signed_work_upper_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False)


def critical_weight(X,M):
    if M>=2*X:return Q(0)
    return Q(1,max(X,M))-Q(1,2*X)


def logarithmic_weight(X,M):
    if M>=2*X:return arb(0)
    left=max(X,M)
    if left<2:raise ValueError('log integral needs positive nonunit lower endpoint')
    return arb(left).log().expint(1)-arb(2*X).log().expint(1)


def pair_kernel(X,h,k,eta):
    e=Q(eta);M=max(h,k);d=critical_weight(X,M)
    return (arb(1)-arb(e.numerator)/e.denominator)*arb(d.numerator)/d.denominator + (arb(e.numerator)/e.denominator)*arb(h*k).log()*logarithmic_weight(X,M)/2


def reduce_obligation(record,profile):
    WORK_CHECK.validate(record['program'])
    rho=Q(record['rho']);eta=Q(record['program']['eta']);k=record['log_power']
    if not 0<=rho<=1 or abs(eta)>2 or type(k)is not int or k<0 or Q(record['constant'])<0:
        raise ValueError('reviewed signed-kernel scope')
    degree=profile['complete_work_diagonal_log_degree']-(rho==1)
    result=dict(program_id=record['program_id'],program=record['program'],rho=str(rho),log_power=k,constant=record['constant'],
        exact_pair_kernel=dict(critical='d_X(m)=max(0,1/max(X,m)-1/(2X))',
            logarithmic='ell_X(m)=integral_max(X,m)^(2X) dx/(x^2 log x), zero whenm>=2X',
            full='K_eta,X(h,k)=(1-eta)*d_X(max(h,k))+eta*log(h*k)*ell_X(max(h,k))/2'),
        all_ordered_pairs_and_diagonal_retained=True,diagonal_step_log_degree=degree,
        separate_diagonal_payment_insufficient=k<degree,
        full_termwise_absolute_proof_ruled_out=True,
        must_group_signed_products_before_absolute_majorization=True,
        signed_candidate_disproved=False,uniform_required_bound_proved=False,
        whole_signed_bound_proved=False,RH_proved=False)
    # The coefficient solving 1/(4X)-rho/(2X)=0 is generated exactly.
    head_cancelling_rho=Q(1,4)/Q(1,2)
    result['generated_old_pair_energy_cancelling_rho']=str(head_cancelling_rho)
    if rho==head_cancelling_rho:
        result['reduced_obligation']=dict(
            fresh_sum=['sum_ordered_pairs',{'h':'1..4X-1','k':'1..4X-1','condition':'max(h,k)>X'},
                       ['multiply','g(h)','g(k)',['subtract',['K_eta','2X','h','k'],['multiply','1/2',['K_eta','X','h','k']]]]],
            boundary=['multiply',str(-eta),'a_X','G(X)','B_G(X)'],
            boundary_coefficient='a_X=(log2/2)*integral_X^(2X) dx/(x^2 log x log(2x))>0',
            required=['less_equal',['add','fresh_sum','boundary'],['multiply',record['constant'],['power','1+log2X',k]]],
            domain='all dyadic X>=1024; complete unit/cofactor/valuation support',
            boundary_sign_known=False,boundary_independently_paid=False,
            dependency='exact equivalent signed covariance obstruction; neither term is separately assumed bounded')
    return result
