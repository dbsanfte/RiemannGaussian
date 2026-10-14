"""Independent fixed-N,y floor completion and continuum prefix bound.

No LP, producer, scientific signature, Mobius table or kernel value is used.
The finite certificate proves all ratio parameters; uniform N growth is OPEN.
"""
from fractions import Fraction as Q
from math import gcd,prod
import check_mobius_mass_conservation_060 as MASS

Meter=MASS.Meter
MAX_N=65536
MAX_HORIZONS=4096


def _integer(n,minimum,maximum):
    if type(n) is not int or not minimum<=n<=maximum:raise ValueError('bounded strict integer')
    return n


def _weight(N,a,m):
    m.charge(20)
    value=(4*N)//a-3*((2*N)//a)+2*(N//a)
    if value not in (-1,0,1):raise ArithmeticError('complete shell weight range')
    return value


def verify_completion(cert,meter=None):
    m=Meter() if meter is None else meter
    MASS._fields(cert,('schema','parameters','N','y','H','horizons','ratios','coefficients','budget'))
    MASS._expect(cert['schema'],'mobius-prefix-completion-v1')
    alpha,gamma,tau,ps,p,q,period=MASS._parameters(cert['parameters'],m)
    N=_integer(cert['N'],2,MAX_N);D=(4*N)//p
    y=_integer(cert['y'],1,D);H=_integer(cert['H'],1,D)
    horizons=cert['horizons']
    if type(horizons) is not list or len(horizons)>MAX_HORIZONS:raise ValueError('bounded complete horizon list')
    last=0
    for X in horizons:
        _integer(X,1,4*N)
        if X<=last:raise ValueError('strict ascending distinct horizons')
        last=X;m.charge(4)
    ratios=[Q(p,q),Q(1)]
    MASS._expect(cert['ratios'],[str(r) for r in ratios])
    rows=cert['coefficients']
    if type(rows) is not list or len(rows)!=2:raise ValueError('two ratio endpoint vectors')
    coefficients=[]
    for row in rows:
        if type(row) is not list or len(row)!=len(horizons):raise ValueError('every horizon at both endpoint ratios')
        coefficients.append([MASS._rational(c,m) for c in row])
    budget=MASS._rational(cert['budget'],m)
    if budget<0:raise ValueError('nonnegative exact completion budget')
    coefficient_costs=[]
    for row in coefficients:
        cost=Q(0)
        for c in row:cost=MASS._bounded(cost+abs(c),m)
        coefficient_costs.append(cost)
    residual_costs=[Q(0),Q(0)];coprime_short=0;coprime_tail=0
    R=prod(ps);end=max([D]+horizons)
    for d in range(1,end+1):
        m.charge(10+d.bit_length()+R.bit_length())
        if gcd(d,R)!=1:continue
        if d<=y:
            A=_weight(N,p*d,m);B=_weight(N,q*d,m)
            target=[Q(A)-ratio*B for ratio in ratios]
        else:target=[Q(0),Q(0)]
        completed=[Q(0),Q(0)]
        for j,X in enumerate(horizons):
            floor=X//d;m.charge(10)
            for e in range(2):
                completed[e]=MASS._bounded(completed[e]+coefficients[e][j]*floor,m)
        if d>H:
            coprime_tail+=1
            if any(target[e]!=completed[e] for e in range(2)):
                raise ValueError('exact tail completion fails at an included coprime integer')
        else:
            coprime_short+=1
            for e in range(2):
                residual_costs[e]=MASS._bounded(residual_costs[e]+abs(target[e]-completed[e]),m)
    costs=[MASS._bounded(c+r,m) for c,r in zip(coefficient_costs,residual_costs)]
    if budget!=max(costs):raise ValueError('budget must equal complete maximum endpoint cost')
    m.charge(200)
    return {'verified':True,'schema':'verified-mobius-prefix-completion-v1',
        'parameters':cert['parameters'],'N':N,'y':y,'H':H,'D':D,
        'horizons':horizons,'ratios':[str(r) for r in ratios],
        'endpoint_costs':[{'ratio':str(ratio),'coefficient_l1':str(c),
            'short_residual_l1':str(residual),'total':str(total)}
            for ratio,c,residual,total in zip(ratios,coefficient_costs,residual_costs,costs)],
        'budget':str(budget),'finite_prefix_bound':{
            'expression':'|p^(-t)*sum_(d<=y,gcd(d,R)=1) mu(d)*(W(N/(p*d))-(p/q)^t*W(N/(q*d)))| <=budget*(1+log2(4N))^k',
            'log_degree':len(ps),'t_domain':'every real 0<t<1',
            'N_and_y_scope':'only the exact fixed integer N,y in this certificate',
            'proved':True},
        'finite_prefix_bound_proved':True,'parameter_continuum_proved':True,
        'completion':{'tail_checked_through':end,'coprime_tail_rows':coprime_tail,
            'coprime_short_rows':coprime_short,'all_added_horizon_exits_retained':True,
            'unit_in_short_residual':True,'nonsquarefree_coprime_rows_retained':True,
            'outside_primes_not_whitelisted':True,
            'beyond_checked_horizon':'target and every added floor vanish identically'},
        'interpolation':{'coefficients':'affine interpolation of BOTH complete endpoint vectors',
            'cost':'coefficient L1 plus complete short residual L1 is convex',
            'ratio_domain':'[p/q,1]','same_budget_for_all_ratios':True},
        'convolution_rule':'mu_M*One=indicator_M_smooth; all floor horizons complete; Psi_M includes1',
        'uniform_N_growth_proved':False,'all_y_bound_proved':False,'core_bound_proved':False,
        'whole_signed_target_bound_proved':False,'RH_proved':False,
        'scientific_source_values_or_kernel_integrals_evaluated':False}
