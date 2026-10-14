"""Independent exact witnesses and bound costs for convolution arguments.

Sparse linear witnesses are checked against complete reconstructed columns;
the producer's elimination algorithm is never imported or rerun.
"""
import copy
import itertools
import math
from fractions import Fraction as Q

import check_core_bound_argument_search as TRUSTED

require = TRUSTED.require
number = TRUSTED.rational
equal = TRUSTED.equal
env = TRUSTED.env
GRAMMAR = dict(max_denominator=6,ordered_cutoffs=2,coverage='2*beta>=1; fixed integer floors; beta<1',
               coefficient_search='all degree-m monomials with at most one e; rational linear certificates')


def geometry_grid(limit=6):
    require(type(limit) is int and 2<=limit<=12,'bounded rational cutoff enumeration')
    values=sorted({Q(n,d) for d in range(1,limit+1) for n in range(1,d)})
    return [(str(a),str(b)) for a in values for b in values if a<=b and b>=Q(1,2)]


def encode(p):
    return [dict(key=list(k),value=str(v)) for k,v in sorted(p.items()) if v]


def decode(rows,meter,coordinates='convolution'):
    require(type(rows) is list,'polynomial row list')
    out={}
    previous=None
    for row in rows:
        require(type(row) is dict and set(row)=={'key','value'} and type(row['key']) is list,'polynomial fields')
        key=tuple(row['key'])
        if coordinates=='floor':
            require(len(key)==3 and key[0] in {'n','Fa','Fd','Fad','one'} and
                    all(type(i) is int and 0<=i<=4 for i in key[1:]),'reciprocal coordinates')
        else:
            require(all(type(v) is str and v in {'C','e','r','t'} for v in key) and
                    tuple(sorted(key))==key and len(key)<=6,'Dirichlet monomial')
        require(previous is None or previous<key,'unique sorted polynomial rows')
        c=number(row['value'],meter)
        require(type(row['value']) is str and row['value']==str(c) and c,'canonical nonzero coefficient')
        out[key]=c;previous=key
    return out


def accumulate(out,p,c=Q(1)):
    for k,v in p.items():
        out[k]=out.get(k,Q(0))+c*v
        if not out[k]:del out[k]
    return out


def product(a,b,meter):
    out={}
    for k,v in a.items():
        for l,w in b.items():
            meter.charge()
            accumulate(out,{tuple(sorted(k+l)):v*w})
    return out


def certify_linear(columns,source,cert,meter,coordinates='convolution'):
    require(type(cert) is dict and cert.get('status') in {'feasible','infeasible'},'linear certificate status')
    universe=set(source).union(*(set(c) for c in columns))
    if cert['status']=='feasible':
        require(set(cert)=={'status','solution'} and type(cert['solution']) is list,'primal fields')
        out={};previous=-1
        for row in cert['solution']:
            require(type(row) is dict and set(row)=={'column','coefficient'},'primal row')
            i=row['column']
            require(type(i) is int and previous<i<len(columns),'complete-column primal index')
            c=number(row['coefficient'],meter)
            require(type(row['coefficient']) is str and row['coefficient']==str(c) and c,'nonzero exact primal')
            accumulate(out,columns[i],c);previous=i
            meter.charge(1+len(columns[i]))
        require(out==source,'exact primal reconstruction')
        return True
    require(set(cert)=={'status','dual','contradiction'},'dual fields')
    y=decode(cert['dual'],meter,coordinates)
    require(set(y)<=universe,'dual row belongs to complete constraint universe')
    for column in columns:
        require(sum((y.get(k,0)*v for k,v in column.items()),Q(0))==0,'dual annihilates every allowed column')
        meter.charge(1+len(column))
    contradiction=sum((y.get(k,0)*v for k,v in source.items()),Q(0))
    require(contradiction and number(cert['contradiction'],meter)==contradiction,'nonzero left-null contradiction')
    return False


def floor_columns():
    source={('Fd',1,0):Q(1),('Fad',0,0):Q(-1),('one',0,0):Q(-1,2),('one',1,0):Q(1,2)}
    basis=[]
    for symbol,x,y in [('d',0,1),('a',1,0),('ad',1,1)]:
        for i in range(3):
            for j in range(3-i):
                poly={('n',x+i,y+j):Q(1),('F'+symbol,i,j):Q(-1),
                      ('one',i,j):Q(-1,2),('one',x+i,y+j):Q(1,2)}
                basis.append(dict(denominator=[x,y],reciprocal=[i,j],polynomial=encode(poly)))
    return source,basis


def verify_floor(result,meter):
    source,basis=floor_columns()
    require(type(result) is dict and 'certificate' in result,'floor result')
    columns=[decode(b['polynomial'],meter,'floor') for b in basis]
    require(certify_linear(columns,source,result['certificate'],meter,'floor'),'floor rewrite must close')
    expected=dict(source=encode(source),basis=basis,certificate=result['certificate'],
        domain='positive integers a,d; integer n>=0',
        normalization='floor(floor(n/d)/a)=floor(n/(ad)); x=1/a,y=1/d',
        inference='denominator factor closure and reciprocal monomials of total degree<=2',numerical_fitting=False)
    equal(result,expected,meter,'complete floor synthesis')
    return dict(verified=True,columns=len(columns))


def verify_dilation(a,h,floor_certificate,result,meter):
    verify_floor(floor_certificate,meter)
    require(type(a) in (list,tuple) and type(h) in (list,tuple) and 1<=len(a)*len(h)<=10000,'finite arrays')
    a=[number(v,meter) for v in a];h=[number(v,meter) for v in h]
    c=sum((v/Q(d) for d,v in enumerate(a,1)),Q(0))
    weights=[Q(0)]*(len(a)*len(h))
    for i,av in enumerate(a,1):
        for d,hv in enumerate(h,1):
            weights[i*d-1]+=av*hv;meter.charge()
    for d,hv in enumerate(h,1):weights[d-1]-=c*hv
    null=sum((v/Q(n) for n,v in enumerate(weights,1)),Q(0))
    require(null==0,'complete harmonic cancellation')
    mean=1+sum((av*Q(d-1,2*d) for d,av in enumerate(a,1)),Q(0))
    expected=dict(coefficients=[str(v) for v in weights],c=str(c),mean=str(mean),harmonic_null='0',
                  short_head='-(1-C)*sum_(d>n)h(d); not part of the periodic covariance')
    equal(result,expected,meter,'signed collection, mean, unit and head')
    return dict(verified=True,support=len(weights))


def verify_gram(v,w,result,meter):
    require(len(v)*len(w)<=1000000,'finite Gram budget')
    v=[number(a,meter) for a in v];w=[number(a,meter) for a in w]
    h=max(len(v),len(w),1)
    j=[n*n for n in range(h+1)]
    for r in range(1,h+1):
        for multiple in range(2*r,h+1,r):j[multiple]-=j[r];meter.charge()
    covariance=Q(0)
    # Independent equal-conductor description includes ALL bilinear crosses.
    for r in range(2,min(len(v),len(w))+1):
        left=sum((v[n-1]*Q(r,n) for n in range(r,len(v)+1,r)),Q(0))
        right=sum((w[n-1]*Q(r,n) for n in range(r,len(w)+1,r)),Q(0))
        covariance+=left*right*Q(j[r],12*r*r)
        meter.charge(1+len(v)//r+len(w)//r)
    equal(result,str(covariance),meter,'exact signed discrete Gram')
    return dict(verified=True,covariance=str(covariance))


def sum_divisors(k,s):
    if s==1:return Q(1),Q(0),k
    if s<1:return 1/(1-s),1-s,k-1
    return (1+1/(s-1))**k,Q(0),0


def exponential_constant(j):
    # Integrate e^-y(1+y)^j by its binomial expansion.
    return sum(math.comb(j,i)*math.factorial(i) for i in range(j+1))


def verify_divisor_arguments(result,meter):
    require(type(result) is dict,'divisor result')
    p=result['p'];s=number(result['decay'],meter);profile=result['profile']
    require(type(p) is int and 0<=p<=12 and s>=0 and profile in {'bounded','mobius'},'divisor domain')
    k=p+1
    amplitude=Q(3) if profile=='mobius' else (Q(2) if not s else 2+1/s)
    extra=2 if profile=='bounded' and not s else 0
    rows=[]
    def row(rule,c,u,log,detail):
        rows.append(dict(rule=rule,bound=env(amplitude**2*c*k**log,k*u,logs=log+extra),
                         details=detail,amplitude=str(amplitude),amplitude_squared_log_degree=extra))
        meter.charge(10)
    c,u,log=sum_divisors(k,s)
    row('pointwise_divisor_mass',c*c/4,2*u,2*log,'abs(B_n)<=1/2; complete divisor mass')
    c,u,log=sum_divisors(2*k*k,2*s)
    row('weighted_coefficient_l2',c/6,u,log,'Var<=sum d2(n)*abs(v(n))^2/6; d2*d_k^2<=d_(2k^2)')
    c,u,log=sum_divisors(k*k,2*s)
    if s:
        row('uniform_divisor_cofactor',c*(1+1/s)**(2*k)/12,u,log,
            'complete cofactor bounded by d_k(r)*r^-decay*(1+1/decay)^k')
        base=Q(exponential_constant(2*k),12)
        if s<Q(1,2):
            row('weighted_Abel',base/(1-2*s)**2,1-2*s,k*k-1,
                'common-period norm of partial divisor envelopes; endpoint retained')
        elif s==Q(1,2):
            row('weighted_Abel',base,Q(0),k*k+1,'critical Abel integral retains two logs')
        else:
            row('weighted_Abel',base*(s/(s-Q(1,2)))**2,Q(0),k*k-1,
                'Abel with the full terminal logarithmic envelope')
    else:
        row('uniform_divisor_cofactor',c/12,u,log+2*k,'take the uniform cofactor maximum')
        row('cutoff_divisor_cofactor',Q(exponential_constant(2*k),12),Q(1),k*k-1,
            'retain H/r; d_k^2<=d_(k^2); Stieltjes exponential moment R_(2k)')
    best=min(range(len(rows)),key=lambda i:(Q(rows[i]['bound']['U_power']),rows[i]['bound']['log_degree'],
                                           Q(rows[i]['bound']['constant']),i))
    bound=rows[best]['bound']
    spacing=[env(bound['constant'],bound['U_power'],1,bound['log_degree']),
             env(2*k*Q(bound['constant']),Q(bound['U_power'])+2*k,logs=bound['log_degree']+1)]
    expected=dict(p=p,decay=str(s),profile=profile,divisor_depth=k,support_U_power=k,candidates=rows,
        selected=best,period_bound=bound,window_bound=spacing,
        window_domain='integer U,L>=1; physical prefix agrees on n>=U^p; exact short head otherwise',
        log_conversion='1+log(U^k)<=k*(1+log U); constants include k^log_degree',
        harmonic_null='sum_n (A^(p+1)-c*A^p)(n)/n=0; all coefficients including unit retained')
    equal(result,expected,meter,'all divisor routes, normalized logs and minimum cost')
    return dict(verified=True,arguments=len(rows),bound=bound)


def geometry_columns(alpha,beta,m,meter):
    variables=('C','e','r','t')
    monomials=lambda d:list(itertools.combinations_with_replacement(variables,d))
    source={('C',)*(m-j)+('e',)*j:Q(math.comb(m,j)) for j in range(m+1)}
    basis=[{key:Q(1)} for key in monomials(m) if key.count('e')<=1]
    costs=[alpha*next(iter(b)).count('t')+beta*next(iter(b)).count('r')
           if 'e' in next(iter(b)) else None for b in basis]
    ideals=[];descriptions=[]
    for a in range(m+1):
        for b in range(m+1-a):
            lower=a*alpha+b*beta
            if not a+b or lower<1:continue
            # (e-t)^a(e-r)^b, independently expanded by both binomial formulas.
            factor={}
            for i in range(a+1):
                for j in range(b+1):
                    key=tuple(sorted(('e',)*(a+b-i-j)+('t',)*i+('r',)*j))
                    accumulate(factor,{key:Q((-1)**(i+j)*math.comb(a,i)*math.comb(b,j))})
            for multiplier in monomials(m-a-b):
                ideals.append(product({multiplier:Q(1)},factor,meter))
                descriptions.append(dict(t_tail_power=a,r_tail_power=b,multiplier=list(multiplier),
                                         lower_support_power=str(lower)))
    return source,basis,costs,ideals,descriptions


def verify_geometry(result,meter):
    require(type(result) is dict,'geometry result')
    a,b=number(result['alpha'],meter),number(result['beta'],meter);m=result['m']
    require(0<a<=b<=1 and type(m) is int and 1<=m<=6,'ordered fixed cutoffs')
    source,basis,costs,ideals,descriptions=geometry_columns(a,b,m,meter)
    thresholds=sorted({Q(0)}|{c for c in costs if c is not None})
    require(type(result['trials']) is list and len(result['trials'])==len(thresholds),'all affordable thresholds')
    feasible=[]
    for i,(trial,threshold) in enumerate(zip(result['trials'],thresholds)):
        require(type(trial) is dict and set(trial)=={'support_threshold','allowed','certificate'},'threshold fields')
        allowed=[j for j,c in enumerate(costs) if c is None or c<=threshold]
        equal(trial['support_threshold'],str(threshold),meter,'support threshold')
        equal(trial['allowed'],allowed,meter,'complete affordable basis')
        if certify_linear([basis[j] for j in allowed]+ideals,source,trial['certificate'],meter):feasible.append(i)
    require(feasible,'a short source representation is required')
    selected=min(feasible)
    chosen=result['trials'][selected]
    representation={};vanishing={}
    for term in chosen['certificate']['solution']:
        index=term['column'];c=number(term['coefficient'],meter)
        if index<len(chosen['allowed']):accumulate(representation,basis[chosen['allowed'][index]],c)
        else:accumulate(vanishing,ideals[index-len(chosen['allowed'])],c)
    h={};z={}
    for key,c in representation.items():
        if 'e' in key:
            values=list(key);values.remove('e');h[tuple(values)]=c
        else:z[key]=c
    expected=dict(alpha=str(a),beta=str(b),m=m,source=encode(source),basis=[encode(x) for x in basis],
        support_costs=[None if c is None else str(c) for c in costs],ideals=[encode(x) for x in ideals],
        support_certificates=descriptions,trials=result['trials'],selected=selected,
        one_e_coefficient=encode(h),finite_head=encode(z),vanishing_remainder=encode(vanishing),
        identity='(C*delta+e)^m = h*e+z on coefficients n<=N',
        domain='fixed t=floor(N^alpha), r=floor(N^beta), integer N>=1; every coefficient 1<=n<=N',
        full_finite_head_indicator_retained=True,global_Dirichlet_series_identity=False,
        moving_cutoffs_allowed_in_period_rule=False,head_or_cross_paid=False)
    equal(result,expected,meter,'complete fixed-N identity and primal/dual optimum')
    return dict(verified=True,thresholds=len(thresholds),support_threshold=str(thresholds[selected]))


def geometry_cost(g,p,cutoff,meter):
    h=decode(g['one_e_coefficient'],meter);a=number(g['alpha'],meter);b=number(g['beta'],meter)
    u=number(cutoff,meter)
    require(h and g['m']==3 and type(p) is int and p>=0 and 0<u<1,'actual cubic cost domain')
    gamma=max(k.count('t')*a+k.count('r')*b for k in h)
    depth=max(p+2*(k.count('t')+k.count('r'))+1 for k in h)
    amplitude=3*sum((abs(c)*Q(5,2)**k.count('C')*5**(k.count('t')+k.count('r')) for k,c in h.items()),Q(0))
    return dict(coefficient_divisor_depth=depth,coefficient_amplitude=str(amplitude),coefficient_U_power=2,
        denominator=dict(U_power=p+1,N_power=str(gamma)),
        normalized_spacing_cost_power=str((3*(p+1)+4)*u+3*gamma-2),
        optimistic_zero_amplitude_cost_power=str(3*(p+1)*u+3*gamma-2),
        scope='cost of separate periodic-spacing argument divided by N^2; not a core energy bound',
        finite_head_and_cross_paid=False,outer_kernel_and_centering_paid=False,actual_arithmetic_lower_bound=False)


def source_binding(parent,meter):
    require(parent['schema']=='core-bound-argument-feedback-v1','current verified argument input')
    binding=TRUSTED.source_binding(dict(parent,schema='core-signed-primitive-feedback-v1'),meter)
    equal(binding,parent['bound_argument_search']['binding'],meter,'unchanged complete source')
    return binding


def prime_obstruction(p):
    require(type(p) is int and 0<=p<=12,'actual finite product depth')
    k=p+1
    return dict(p=p,number_of_distinct_primes=k,prime_interval='U/2<q<=U',
        conductor='product of k distinct primes from the declared interval',
        coefficient=str((-1)**k*math.factorial(k)),
        higher_cofactors_zero='a short factor containing q>U/2 cannot absorb any further integer>=2',
        lower_coefficient=str(Q(math.factorial(k)**2,24)),
        uniform_lower_bound='Var >= lower_coefficient * binom(pi(U)-pi(U/2),k)',
        jordan_ratio_lower='J2(r)/r^2>=1/2 by the telescoping product over all integers>=2',
        asymptotic=dict(U_power=k,log_denominator_degree=k,imported_theorem='pi(x)~x/log(x)',
            source='https://dlmf.nist.gov/27.2.E3',
            scope='positive implied constant for all sufficiently large U; no effective threshold claimed'),
        applies_only_to='full-period covariance of A^p*e at decay zero with actual Mobius coefficients',
        finite_window_lower_bound=False,full_core_refuted=False)


def verify_search(parent,result,meter):
    binding=source_binding(parent,meter);t=parent['cutoff_work_targets'][0]
    require((t['p'],t['m'])==(2,3),'actual source component')
    verify_floor(result['floor_search'],meter)
    require(type(result['divisor_proofs']) is list and len(result['divisor_proofs'])==2,'arithmetic ablation')
    count=0
    for argument,profile in zip(result['divisor_proofs'],('mobius','bounded')):
        equal((argument['p'],argument['decay'],argument['profile']),(t['p'],'0',profile),meter,'source divisor goal')
        count+=verify_divisor_arguments(argument,meter)['arguments']
    grid=geometry_grid()
    require(type(result['geometries']) is list and len(result['geometries'])==len(grid),'complete geometry search')
    threshold_count=0;costs=[]
    for g,(a,b) in zip(result['geometries'],grid):
        equal((g['alpha'],g['beta'],g['m']),(a,b,t['m']),meter,'declared source geometry')
        threshold_count+=verify_geometry(g,meter)['thresholds']
        costs.append(geometry_cost(g,t['p'],t['original_low_obligation']['parameters']['alpha'],meter))
    best=min(range(len(costs)),key=lambda i:(Q(costs[i]['normalized_spacing_cost_power']),i))
    expected=dict(schema='core-convolution-argument-search-v1',binding=binding,floor_search=result['floor_search'],
        divisor_proofs=result['divisor_proofs'],geometry_grammar=copy.deepcopy(GRAMMAR),
        geometries=result['geometries'],geometry_costs=costs,period_obstruction=prime_obstruction(t['p']),selected_geometry=best,
        inherited_recovery=copy.deepcopy(parent['bound_argument_search']['recovery']),
        complete_source='A^p*(h*e+z)-c^m*D on n<=N; unchanged full source outside local identity',
        source_recovery=dict(mean='C=1+(M(U)-c)/2',unit='e(1)=c-C; included in 5U*d2 envelope',
            floor_head='-(1-C)*sum_(d>n)(A^p*h)(d)',finite_head='prefix(A^p*z-c^m*D)(n)',
            joined_covariance='square of periodic branch + exact floor head + exact finite head, all ordered crosses',
            outer_K_and_analytic_residue='unchanged and still unpaid',ordinary_theta_moment_convergence_assumed=False),
        missing='uniform signed finite-window covariance of the COMPLETE joined hyperbola branches and '
                'outer-kernel/centering recovery; fixed-period estimates do not pay this',
        statistics=dict(floor_columns=len(result['floor_search']['basis']),divisor_arguments=count,geometries=len(grid),
            geometry_thresholds=threshold_count,actual_arithmetic_observations=0,fitted_constants=0,runtime_model_calls=0,
            arithmetic_U_power_advantage=False,arithmetic_log_degree_advantage=2,full_component_bound_proved=False),
        supplied_rules='CORE_DILATION_COVARIANCE_REVIEW_031.txt',formal_proof_assistant_verified=False,
        whole_signed_bound_proved=False,RH_proved=False)
    equal(result,expected,meter,'complete source, selection, costs and open recovery')
    return dict(verified=True,geometry_thresholds=threshold_count,full_component_bound_proved=False)


def verify_feedback(parent,result,out,artifact,meter):
    audit=verify_search(parent,result,meter)
    expected=copy.deepcopy(parent)
    expected.update(schema='core-convolution-argument-feedback-v1',status='convolution_arguments_searched_core_open',
                    parent_obligation_file='candidate10_bound_argument_obligation.json',complete_search_artifact=artifact)
    expected['convolution_argument_search']=copy.deepcopy(result)
    expected['inherited_convolution_argument_tasks']=copy.deepcopy(parent['next_search_tasks'])
    expected['next_search_tasks']=[copy.deepcopy(parent['next_search_tasks'][0]),dict(priority=1,
        target_id=result['binding']['target_id'],search_kind='signed_joined_hyperbola_window_covariance',status='open',
        exact_geometry=copy.deepcopy(result['geometries'][result['selected_geometry']]),
        failed_separate_spacing_cost=copy.deepcopy(result['geometry_costs'][result['selected_geometry']]),
        complete_recovery=copy.deepcopy(result['source_recovery']),missing=result['missing'],
        original_global_Mellin_bound_and_all_routes_retained=True)]+copy.deepcopy(parent['next_search_tasks'][1:])
    equal(out,expected,meter,'full inherited source and open-task preservation')
    return audit
