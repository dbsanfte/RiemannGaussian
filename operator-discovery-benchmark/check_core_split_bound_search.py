"""Independent exact audit of split-error optimizers and source certificates.

No generator, numerical source archive, or fitted coefficient is imported.
The optimizer audit includes a global convex lower-bound certificate, not
just a replay of the finite intersection enumeration.
"""
from fractions import Fraction as Q
from math import comb
from math import ceil
from itertools import product
import re


def _require(condition,message):
    if not condition:raise ValueError(message)


def _same(left,right):
    """JSON equality with exact types; booleans cannot stand in for indices."""
    if type(left) is not type(right):return False
    if type(left) is dict:return set(left)==set(right) and all(_same(left[k],right[k]) for k in left)
    if type(left) is list:return len(left)==len(right) and all(_same(a,b) for a,b in zip(left,right))
    return left==right


def _rational(text,meter):
    _require(type(text) is str and 0<len(text)<=1235 and re.fullmatch(r'-?\d+(?:/\d+)?',text) is not None,
             'canonical bounded rational string')
    meter.charge(len(text)+1)
    try:value=Q(text)
    except (ValueError,ZeroDivisionError) as error:raise ValueError('exact rational') from error
    _require(str(value)==text and max(abs(value.numerator).bit_length(),value.denominator.bit_length())<=4096,
             'canonical bounded exact rational')
    if hasattr(meter,'number'):return meter.number(value)
    return value


def _integer(value,lower=0,upper=1000000):
    _require(type(value) is int and lower<=value<=upper,'bounded exact integer')
    return value


def _intersection_candidates(lines,domain,meter):
    _require(bool(lines) and len(lines)<=64,'bounded nonempty affine power language')
    lower,upper=domain
    _require(lower<upper,'nonempty rational closed minimax domain')
    points={lower,upper}
    for i,(intercept,slope) in enumerate(lines):
        for other_intercept,other_slope in lines[i+1:]:
            if slope!=other_slope:
                t=(other_intercept-intercept)/(slope-other_slope)
                if lower<=t<=upper:points.add(t)
            meter.charge(20)
    candidates=[]
    for t in sorted(points):
        powers=[intercept+slope*t for intercept,slope in lines]
        candidates.append((t,max(powers),powers));meter.charge(10*len(lines))
    return candidates


def _global_minimum_certificate(lines,domain,point,value,meter):
    """Convex supporting-line proof of the claimed global minimax value."""
    active=[(i,intercept,slope) for i,(intercept,slope) in enumerate(lines) if intercept+slope*point==value]
    _require(bool(active),'claimed minimax value is on the upper envelope')
    lower,upper=domain
    if point==lower:
        eligible=[item for item in active if item[2]>=0]
        _require(bool(eligible),'left-boundary supporting slope proves global minimum')
        i,intercept,slope=eligible[0]
        return dict(kind='left_boundary_support',active=[i],weights=['1'],lower_bound=str(intercept+slope*lower))
    if point==upper:
        eligible=[item for item in active if item[2]<=0]
        _require(bool(eligible),'right-boundary supporting slope proves global minimum')
        i,intercept,slope=eligible[0]
        return dict(kind='right_boundary_support',active=[i],weights=['1'],lower_bound=str(intercept+slope*upper))
    zero=[item for item in active if item[2]==0]
    if zero:
        return dict(kind='constant_support',active=[zero[0][0]],weights=['1'],lower_bound=str(value))
    negative=[item for item in active if item[2]<0];positive=[item for item in active if item[2]>0]
    _require(bool(negative) and bool(positive),'interior active slopes must bracket zero')
    i,a,s=negative[0];j,b,t=positive[0]
    w=t/(t-s);v=-s/(t-s)
    _require(w>0 and v>0 and w+v==1 and w*s+v*t==0 and w*a+v*b==value,
             'exact convex dual lower bound for all real split points')
    meter.charge(30)
    return dict(kind='convex_dual_support',active=[i,j],weights=[str(w),str(v)],lower_bound=str(value))


def verify_minimax(problem,result,meter):
    _require(type(problem) is dict and set(problem)=={'lower','upper','terms'},'complete affine optimizer problem')
    domain=(_rational(problem['lower'],meter),_rational(problem['upper'],meter))
    terms=problem['terms']
    _require(type(terms) is list and 0<len(terms)<=64,'bounded nonempty affine error powers')
    lines=[]
    for term in terms:
        _require(type(term) is dict and set(term)=={'intercept','slope'},'exact affine power schema')
        lines.append((_rational(term['intercept'],meter),_rational(term['slope'],meter)))
    candidates=_intersection_candidates(lines,domain,meter)
    expected_vertices=[dict(parameter=str(t),power=str(value)) for t,value,_ in candidates]
    _require(type(result) is dict and set(result)=={'problem','vertices','parameter','power','active','dual_weights',
        'dual_slope','tie_rule','domain'},'complete optimizer certificate')
    _require(result['problem']==problem and result['vertices']==expected_vertices,'every boundary and pair intersection retained')
    expected=min(candidates,key=lambda candidate:(candidate[1],candidate[0]))
    point=_rational(result['parameter'],meter);power=_rational(result['power'],meter)
    _require((point,power)==expected[:2],'exact minimax optimum and deterministic tie')
    active=[i for i,(a,b) in enumerate(lines) if a+b*point==power]
    _require(result['active']==active and all(type(i) is int for i in result['active']),'complete active affine powers')
    supplied=result['dual_weights']
    _require(type(supplied) is list and len(supplied)==len(lines),'complete convex dual coefficients')
    weights=[_rational(v,meter) for v in supplied]
    _require(all(w>=0 for w in weights) and sum(weights,Q(0))==1 and
             all(w==0 or i in active for i,w in enumerate(weights)),'nonnegative convex support on active powers')
    slope=sum((w*b for w,(_,b) in zip(weights,lines)),Q(0))
    intercept=sum((w*a for w,(a,_) in zip(weights,lines)),Q(0))
    _require(_rational(result['dual_slope'],meter)==slope and intercept+slope*point==power,
             'exact dual supporting affine power')
    lower,upper=domain
    _require(slope>=0 if point==lower else slope<=0 if point==upper else slope==0,
             'dual lower bound holds on the whole declared domain')
    independent=_global_minimum_certificate(lines,domain,point,power,meter)
    _require(result['tie_rule']=='smallest parameter among minimizers' and
             result['domain']=='scale ratio R>=1; analytic error inequality checked separately',
             'optimizer tie and bounded analytical scope')
    return dict(verified=True,parameter=str(point),power=str(power),vertices=len(candidates),
        independent_global_lower_bound=independent,analytic_error_inequality_proved=False)


def verify_split(cert,meter):
    _require(type(cert) is dict and 'problem' in cert,'complete split certificate')
    return verify_minimax(cert['problem'],cert,meter)


def _power_problem(theta):
    return dict(lower='0',upper='1',terms=[dict(intercept='0',slope='1'),
        dict(intercept=str(theta),slope=str(-theta))])


def _inherited(parent,meter):
    _require(type(parent) is dict and parent.get('whole_signed_bound_proved') is False and
        parent.get('RH_proved') is False,'inherited full signed target remains open')
    chain=[];seen=set();current=parent
    while type(current) is dict:
        _require(id(current) not in seen,'acyclic complete parent ancestry')
        seen.add(id(current));chain.append(current);current=current.get('parent_obligation');meter.charge(10)
    sources=[p for p in chain if p.get('schema')=='source-specific-short-inverse-search-input-v1']
    programs=[p for p in chain if p.get('schema')=='detector-bound-program-search-input-v1']
    _require(len(sources)==len(programs)==1,'unique source and original channel ancestry')
    rows=sources[0].get('source_geometries')
    _require(type(rows) is list and bool(rows),'complete inherited source geometry')
    modes=[c['mode'] for c in rows[0]['cases']]
    expected_profiles={('B','beta',2,0,'1/3'),('U','-beta',1,1,'1/3'),('V','-beta',1,0,None),('power','-R_u',0,1,'1/3')}
    _require(len(modes)==4 and len({m['name'] for m in modes})==4 and
        {(m['name'],m['coefficient'],m['p'],m['q'],m['positive_shift']) for m in modes}==expected_profiles,
        'all four exact current arithmetic modes')
    for mode in modes:
        _require(set(mode)=={'name','coefficient','p','q','positive_shift'} and type(mode['name']) is str,
            'complete source-mode schema')
        _integer(mode['p'],0,2);_integer(mode['q'],0,2)
    for row in rows:
        _require(_same([c['mode'] for c in row['cases']],modes),'same full source in every inherited representation')
        meter.charge(20*len(modes))
    obligations=programs[0].get('generated_bound_program_obligations')
    _require(type(obligations) is list and bool(obligations),'all original route obligations retained')
    _require(len({p['id'] for p in obligations})==len(obligations),'unique original route bindings')
    return modes,obligations


def _spec(spec,meter):
    _require(type(spec) is dict and set(spec)=={'root_denominator_min','root_denominator_max',
        'maximum_inverse_factors','target'},'complete declared search grammar')
    lo=_integer(spec['root_denominator_min'],2,64);hi=_integer(spec['root_denominator_max'],lo,64)
    _integer(spec['maximum_inverse_factors'],4,128)
    _require(type(spec['target']) is dict and set(spec['target'])=={'energy_power','log_degree'},'exact component goal')
    _rational(spec['target']['energy_power'],meter);_integer(spec['target']['log_degree'],0,32)
    return lo,hi


def _multiply(left,right,meter):
    out={}
    for (i,j),a in left.items():
        for (k,l),b in right.items():
            key=i+k,j+l;out[key]=out.get(key,Q(0))+a*b;meter.charge(12)
    return {key:c for key,c in out.items() if c}


def verify_inverse(program,alpha,gamma,p,q,meter):
    """Independent closed coefficients AND residual support certificate.

    Below alpha*a+gamma*b=1 the inverse coefficient is the product of
    generalized binomial coefficients.  Multiplication checks every head,
    unit, mixed term and surviving support boundary without degree-20 limits.
    """
    _require(type(program) is dict and set(program)=={'alpha','gamma','p','q','terms'} and
        (program['alpha'],program['gamma'],program['p'],program['q'])==(str(alpha),str(gamma),p,q),
        'inverse binds the complete source and common cutoff')
    _integer(program['p'],0,2);_integer(program['q'],0,2)
    _integer(p,0,2);_integer(q,0,2)
    _require(0<alpha<1 and 0<gamma<1 and p+q>0,'licensed inverse factors')
    terms=program['terms'];_require(type(terms) is list and len(terms)<=8192,'bounded complete inverse polynomial')
    expected={}
    for a in range(ceil(1/alpha)):
        for b in range(ceil(1/gamma)):
            if a*alpha+b*gamma>=1:continue
            ca=comb(p+a-1,a) if p else int(a==0)
            cb=comb(q+b-1,b) if q else int(b==0)
            if ca*cb:expected[a,b]=Q(ca*cb)
            meter.charge(15)
    ordered=sorted(expected,key=lambda key:(sum(key),key))
    _require(_same(terms,[dict(a=a,b=b,coefficient=str(expected[a,b])) for a,b in ordered]),
        'all signed inverse terms and exact coefficients below support frontier')
    denominator={(a,b):Q((-1)**(a+b)*comb(p,a)*comb(q,b)) for a in range(p+1) for b in range(q+1)}
    remainder=_multiply(expected,denominator,meter)
    _require(remainder.pop((0,0),Q(0))==1,'inverse unit is retained exactly')
    _require(all(alpha*a+gamma*b>=1 for a,b in remainder),'every inverse remainder vanishes below common N')
    return ordered


def uniform_payment(energy,target,meter):
    """Conservative exact bound for N^-a(1+ln N)^k, N>=1.

    (1+x)^k<=2^k(1+x^k); x^k exp(-a*x)<= (k/a)^k.
    Equal-power positive excess logarithms remain unpaid.
    """
    c=_rational(energy['constant'],meter);difference=_rational(energy['power'],meter)-_rational(target['energy_power'],meter)
    _require(c>=0,'nonnegative energy certificate')
    excess=max(0,_integer(energy['log_degree'],0,256)-_integer(target['log_degree'],0,32))
    if difference>0 or difference==0 and excess:return None
    factor=Q(1) if excess==0 else 2**excess*(1+(Q(excess)/(-difference))**excess)
    meter.charge(40+10*excess)
    return str(c*factor)


def _weighted_mass(s):
    _require(s>0,'positive decreasing finite weighted mass')
    if s==1:return dict(constant='1',cutoff_power='0',log_degree=1)
    if s>1:return dict(constant=str(s/(s-1)),cutoff_power='0',log_degree=0)
    return dict(constant=str(1/(1-s)),cutoff_power=str(1-s),log_degree=0)


def _routes(mode,coefficient,alpha,gamma,split,target,meter):
    theta=1-Q(mode['positive_shift']);r=Q(split['power']);p,q=mode['p'],mode['q']
    _require(split['problem']==_power_problem(theta) and r==theta/(1+theta) and
        Q(split['parameter'])==r and 0<r<=theta<1,'licensed generic all-n optimal split')
    up=(p+1)/(1+theta);wb=_weighted_mass(Q(2,3)+r)
    direct=dict(rule='center_complete_bounded_prefix_factor',
        prefix_constant=str(36*Q(15,2)**q/(theta*(1-theta))),U_power=str(up),
        V_power=str(Q(q,3)/(1+theta)),log_degree=p+1,
        premises=dict(prefix_constant=str(2*3**q),prefix_U_power=str(p+1),prefix_V_power=str(Q(q,3)),
            density_constant=str(3*Q(5,2)**q),density_log_degree=p+1),
        full_conditional_moment=True,small_n_case_included=True)
    other=dict(rule='finite_weighted_propagation_with_complete_commutator',
        prefix_constant=str(42*(1+theta)**p*Q(wb['constant'])**q/(theta*(1-theta))),
        U_power=str(up),V_power=str(q*Q(wb['cutoff_power'])),log_degree=1+q*wb['log_degree'],
        premises=dict(B_weight_exponent=str(Q(2,3)+r),B_weight_bound=wb,
            E_moment_constant=str(2/(1-theta)+4),E_moment_U_power=str(1-theta),
            commutator_prefix='n^r * sum_all_d |h0(d)|/d^r',commutator_all_d_including_d_gt_n=True),
        full_conditional_moment=True,small_n_case_included=True)
    scalar=Q(5) if mode['coefficient']=='-R_u' else Q(9,2)
    for route in (direct,other):
        vp=Q(route['V_power']);e=r+up*alpha+vp*gamma
        energy=dict(constant=str((2*scalar*coefficient*Q(route['prefix_constant']))**2),
            power=str(2*e-1),log_degree=2*route['log_degree'])
        bound=(Q(target['energy_power'])/2+Q(1,2)-r-vp*gamma)/up
        route.update(local_n_power=str(r),prefix_N_power=str(e),energy=energy,
            target_constant=uniform_payment(energy,target,meter),
            cutoff_condition=dict(alpha_upper=str(bound),strict=energy['log_degree']>target['log_degree'],
                gamma=str(gamma),scope='sufficient within this proof route; failure is not an arithmetic counterexample'))
        meter.charge(300)
    return [direct,other]


def _application(mode,term,alpha,gamma,split,target,ident,meter):
    theta=1-Q(mode['positive_shift']);coefficient=Q(term['coefficient'])
    factors=['A']*mode['p']+['B']*mode['q']+['E']
    routes=_routes(mode,coefficient,alpha,gamma,split,target,meter)
    choice=min(range(2),key=lambda i:(Q(routes[i]['energy']['power']),routes[i]['energy']['log_degree'],
        Q(routes[i]['energy']['constant']),i))
    return dict(id=ident,source_key=dict(mode=mode['name'],a=1,b=0),source_scalar=mode['coefficient'],
        source_coefficient=str(coefficient),theta=str(theta),h_factors=factors,
        moment=dict(kind='complete_conditional_moment',theta=str(theta),factors=factors,
            factorization='finite moments of A,B times the full infinite conditional moment of E',truncated_at_horizon=False),
        pieces=[dict(kind='centered_power_convolution',coefficient=str(coefficient),factors=factors),
            dict(kind='moment_drift',coefficient=str(coefficient/theta),kernel='J_theta'),
            dict(kind='centering_compensation',coefficient=str(-coefficient),
                factors=['A']*mode['p']+['B']*mode['q']+['C','K','O'])],
        routes=routes,selected_route=choice,component_target_proved=routes[choice]['target_constant'] is not None,
        compensating_terms_bounded=False,scope='one centered component; the complete signed residual stays open')


def _geometry(row,modes,alpha,gamma,spec,splits,ident,meter):
    _require(type(row) is dict and set(row)=={'id','alpha','gamma','cases','component_count',
        'maximum_convolution_factors','applications','exact_join','full_signed_bound_proved','RH_proved'},'complete geometry schema')
    _require(row['id']==ident and type(row['id']) is int and row['alpha']==str(alpha) and row['gamma']==str(gamma),
        'every declared root pair retained in grammar order')
    _require(type(row['cases']) is list and len(row['cases'])==4,'all four signed source rows')
    applications=[];untouched=[];depth=0;count=0
    for case,mode in zip(row['cases'],modes):
        _require(type(case) is dict and set(case)=={'mode','program'} and _same(case['mode'],mode),'exact inherited source mode')
        verify_inverse(case['program'],alpha,gamma,mode['p'],mode['q'],meter)
        for term in case['program']['terms']:
            count+=1;depth=max(depth,mode['p']+mode['q']+term['a']+term['b']+int(mode['positive_shift'] is not None))
            if mode['positive_shift'] is not None and (term['a'],term['b'])==(1,0):
                split=splits[str(1-Q(mode['positive_shift']))]
                applications.append(_application(mode,term,alpha,gamma,split,spec['target'],len(applications),meter))
            else:untouched.append(dict(mode=mode['name'],a=term['a'],b=term['b']))
    _require(depth<=spec['maximum_inverse_factors'] and row['maximum_convolution_factors']==depth and
        type(row['maximum_convolution_factors']) is int and row['component_count']==count and type(row['component_count']) is int,
        'complete degree budget and source count; no truncation')
    _require(_same(row['applications'],applications),'all centered source matches, moments, three signs and competing proof routes')
    paid=[a['id'] for a in applications if a['component_target_proved']];allids=list(range(len(applications)))
    join=dict(untouched_source_terms=untouched,replaced_source_terms=[a['source_key'] for a in applications],
        paid_centered_components=paid,residual_centered_components=[i for i in allids if i not in paid],
        all_moment_drifts=allids,all_centering_compensations=allids,transport_error_coefficient='-1',
        transport_error_definition='e=f-g',identity='g=P+R; P=sum(paid centered components); R=all other complete signed pieces-e')
    _require(_same(row['exact_join'],join) and row['full_signed_bound_proved'] is False and row['RH_proved'] is False,
        'complete joined signed residual and original transport error remain open')
    return applications


def _rank(row):
    paid=[a for a in row['applications'] if a['component_target_proved']]
    worst=max((Q(a['routes'][a['selected_route']]['energy']['power']) for a in paid),default=Q(1000))
    return (-len(paid),worst,row['component_count'],row['maximum_convolution_factors'],Q(row['alpha']),Q(row['gamma']))


def _bindings(row,obligations,target,meter):
    if target!=dict(energy_power='0',log_degree=0):return []
    constants=[Q(a['routes'][a['selected_route']]['target_constant']) for a in row['applications'] if a['component_target_proved']]
    source_cost=len(constants)*sum(constants,Q(0));bindings=[]
    for parent in obligations:
        original=_rational(parent['reduction']['target_log_power'],meter)
        loss=_rational(parent['construction']['recovery_log_power'],meter)
        exponent=original-loss
        forcing=_rational(parent['reduction']['required_coarse_forcing_log_power'],meter)
        rho=_rational(parent['reduction']['rho'],meter)
        recovery_constant=parent['construction']['recovery_constant']
        _require(original>=0 and loss>=0 and exponent>=0 and exponent==forcing+int(rho==1) and
            _rational(recovery_constant,meter)>0,'inherited recurrence recovery cost consumes its full log budget')
        p=str(exponent)
        channels=parent['construction']['channels'];_require(type(channels) is list and bool(channels),'complete channel vector')
        channel_cost=Q(0)
        for channel in channels:
            eta=_rational(channel['eta'],meter);_require(eta>=0,'licensed decreasing Abel log weights')
            coeffs=channel['polynomial'];_require(type(coeffs) is list and bool(coeffs),'all channel polynomial coefficients')
            coeffs=[_rational(c,meter) for c in coeffs]
            variation=abs(coeffs[0])+2*sum(map(abs,coeffs[1:]),Q(0))
            channel_cost+=(2**ceil(eta)*variation)**2;meter.charge(100+20*len(coeffs))
        bindings.append(dict(parent_obligation_id=parent['id'],geometry_id=row['id'],transport_program=parent['transport_program'],
            channel_abel_constant=str(channel_cost),combined_paid_energy_constant=str(channel_cost*source_cost),
            sufficient_goal=dict(expression='complete signed projected residual energy S_R(X)',upper='C*(1+log2X)^p',
                p=p,quantifier='one fixed finite C; EVERY dyadic X>=1',status='open'),
            original_target_log_degree=str(original),inherited_recovery_log_power=str(loss),
            inherited_recovery_constant=recovery_constant,original_recovery=parent['conditional_conclusion']['original_recovery'],
            recovery='S_g<=2*S_R+2*C_paid; S_R<=2*S_g+2*C_paid',common_horizon='N=4X-1 for BOTH blocks',
            all_units_primes_prime_powers_and_cross_terms_retained=True,exact_transport_error_retained=True,
            whole_signed_bound_proved=False,RH_proved=False))
    return bindings


def verify_search(parent,result,meter):
    _require(type(result) is dict and set(result)=={'schema','spec','split_certificates','geometries','selected_geometry',
        'selected_bindings','statistics','supplied','generated','source_observations','model_calls_in_search',
        'general_analytic_prover','whole_signed_bound_proved','RH_proved'},'complete search certificate schema')
    _require(result['schema']=='core-split-bound-search-v1','split bound search schema')
    modes,obligations=_inherited(parent,meter);lo,hi=_spec(result['spec'],meter)
    splits=result['split_certificates'];thetas={str(1-Q(m['positive_shift'])) for m in modes if m['positive_shift'] is not None}
    _require(type(splits) is dict and set(splits)==thetas,'all and only source kernel split problems')
    for theta in thetas:
        verify_split(splits[theta],meter)
        _require(splits[theta]['problem']==_power_problem(Q(theta)),'generic minimax bound to actual kernel')
    roots=[Q(1,d) for d in range(lo,hi+1)];grid=list(product(roots,repeat=2));rows=result['geometries']
    _require(type(rows) is list and len(rows)==len(grid),'whole declared geometry candidate set')
    applications=[]
    for ident,(row,(alpha,gamma)) in enumerate(zip(rows,grid)):
        applications.extend(_geometry(row,modes,alpha,gamma,result['spec'],splits,ident,meter))
    chosen=min(rows,key=_rank);_require(type(result['selected_geometry']) is int and result['selected_geometry']==chosen['id'],
        'deterministic exact ranking of all generated controls')
    bindings=_bindings(chosen,obligations,result['spec']['target'],meter)
    _require(_same(result['selected_bindings'],bindings),'every original parent channel and transport route bound to complete representation')
    stats=dict(geometries=len(rows),source_terms=sum(r['component_count'] for r in rows),applications=len(applications),
        proof_routes=2*len(applications),component_target_certificates=sum(a['component_target_proved'] for a in applications),
        geometries_with_component_control=sum(bool(r['exact_join']['paid_centered_components']) for r in rows),
        selected_component_controls=len(chosen['exact_join']['paid_centered_components']),inherited_route_bindings=len(bindings))
    _require(result['statistics']==stats and all(type(v) is int for v in result['statistics'].values()),'exact proof-search statistics')
    _require(result['supplied']==['arithmetic atom facts','centering identity','hyperbola and Abel error inequalities',
        'complete finite-factor commutator bound','root grammar and ranking policy'] and
        result['generated']==['error-balancing split','full source inverse polynomials','matching subexpressions',
        'competing proof routes','cutoff feasibility inequalities','paid partition',
        'complete compensating terms and remaining signed obligations'],'supplied facts distinguished from generated constructions')
    _require(result['source_observations']==0 and type(result['source_observations']) is int and
        result['model_calls_in_search']==0 and type(result['model_calls_in_search']) is int and
        result['general_analytic_prover'] is False and result['whole_signed_bound_proved'] is False and result['RH_proved'] is False,
        'symbolic component synthesis does not close original signed target')
    meter.live(30*sum(r['component_count'] for r in rows)+100*len(applications))
    return dict(verified=True,geometries=len(rows),source_terms=stats['source_terms'],
        selected_geometry=chosen['id'],component_controls=stats['selected_component_controls'],
        inherited_route_bindings=len(bindings),complete_signed_join_proved=False,RH_proved=False)


def verify_feedback(result,feedback,input_file,result_file,meter):
    _require(type(input_file) is str and bool(input_file) and type(result_file) is str and bool(result_file),
        'explicit parent and complete artifact references')
    chosen=result['geometries'][result['selected_geometry']]
    expected=dict(schema='core-split-bound-feedback-v1',status='open',parent_obligation_file=input_file,
        complete_search_artifact=result_file,selected_geometry=chosen['id'],selected_source_representation=chosen,
        generated_bound_obligations=result['selected_bindings'],proof_frontier=[
            dict(id='actual_signed_core',expression=chosen['exact_join'],status='open',depends_on=[],
                priority='independent signed control of the complete join'),
            dict(id='source_recovery',status='proved conditional reduction',depends_on=['actual_signed_core']),
            dict(id='previous_frame_moment_conditions',status='open',parent_file=input_file,
                priority='retained; conditioning alone does not bound the common core')],
        unsupported_next_targets=[
            dict(expression='multiple residual factors R,S in the untouched complete source terms',
                missing='a signed-prefix, correlation or recurrence rule beyond the current bounded-prefix factor language'),
            dict(expression='joint moment drifts, centering compensations, and untouched source minus e',
                missing='a uniform signed estimate retaining their interaction')],
        actual_new_component_controls=len(chosen['exact_join']['paid_centered_components']),
        complete_compensations_and_original_target_retained=True,
        scope='new partial all-scale component controls; full signed core and RH remain open',whole_signed_bound_proved=False,RH_proved=False)
    _require(_same(feedback,expected),'complete inherited frontier, compensations and original signed goal retained')
    _require(feedback['whole_signed_bound_proved'] is False and feedback['RH_proved'] is False,'no false feedback closure')
    meter.charge(300+100*len(result['selected_bindings']))
    return dict(verified=True,status='open',original_target_retained=True)
