"""Independent symbolic audit for conditional multiple-residual bound goals.

No new producer or numerical arithmetic source is imported.  Polynomial
inequalities are checked on whole rational intervals, including stationary
points, rather than inferred from sampled parameters.
"""
from fractions import Fraction as Q
from math import comb, gcd
from itertools import product

from check_core_split_bound_search import _require, _same, _rational, verify_split, verify_inverse


def _trim(poly):
    poly=list(poly)
    while len(poly)>1 and poly[-1]==0:poly.pop()
    return poly or [Q(0)]


def _add(left,right,scale=Q(1)):
    result=[Q(0)]*max(len(left),len(right))
    for i,c in enumerate(left):result[i]+=c
    for i,c in enumerate(right):result[i]+=scale*c
    return _trim(result)


def _multiply(left,right,meter):
    result=[Q(0)]*(len(left)+len(right)-1)
    for i,c in enumerate(left):
        for j,d in enumerate(right):result[i+j]+=c*d;meter.charge(12)
    return _trim(result)


def _value(poly,point,meter):
    result=Q(0)
    for c in reversed(poly):result=result*point+c;meter.charge(10)
    return result


def nonnegative_on_interval(coefficients,lower,upper,meter):
    """Exact complete test for a polynomial of degree at most two.

    Endpoints and the sole possible interior stationary point suffice.
    This proves every gap inequality on the whole declared parameter range.
    """
    poly=_trim([Q(c) for c in coefficients]);lo,hi=Q(lower),Q(upper)
    _require(lo<hi and len(poly)<=3,'bounded quadratic on a nonempty rational interval')
    points=[lo,hi]
    if len(poly)==3 and poly[2]:
        stationary=-poly[1]/(2*poly[2])
        if lo<stationary<hi:points.append(stationary)
    return all(_value(poly,t,meter)>=0 for t in points)


def _strings(poly):return [str(c) for c in _trim(poly)]


def _divide(numerator,denominator,meter):
    remainder=_trim(numerator);denominator=_trim(denominator)
    _require(denominator!=[0],'nonzero symbolic denominator')
    quotient=[Q(0)]*max(1,len(remainder)-len(denominator)+1)
    while remainder!=[0] and len(remainder)>=len(denominator):
        degree=len(remainder)-len(denominator);c=remainder[-1]/denominator[-1]
        quotient[degree]+=c
        remainder=_add(remainder,[Q(0)]*degree+[c*d for d in denominator],Q(-1));meter.charge(30)
    _require(remainder==[0],'exact cancellation in C power polynomial division')
    return _trim(quotient)


def _integer(value,lo,hi):
    _require(type(value) is int and lo<=value<=hi,'bounded exact integer')
    return value


def _lines(theta,rule):
    _require(0<theta<1,'licensed kernel theta')
    if rule=='ordinary':return [([Q(0)],[Q(1)]),([theta],[-theta,Q(1)])]
    _require(rule=='euler_remainder','licensed ordinary or Euler error rule')
    return [([theta-1],[2-theta]),([theta],[-theta,Q(1)]),([Q(0),Q(1)],[Q(0)])]


def _family(theta,rule,meter):
    """Derive active intersections and a global convex lower bound in rho."""
    lines=_lines(theta,rule);accepted=[]
    for first in range(len(lines)):
        for second in range(first+1,len(lines)):
            for i,j in ((first,second),(second,first)):
                ai,bi=lines[i];aj,bj=lines[j]
                den=_add(bi,bj,Q(-1));tn=_add(aj,ai,Q(-1))
                rn=_add(_multiply(ai,den,meter),_multiply(bi,tn,meter))
                gaps=[_add(rn,_add(_multiply(a,den,meter),_multiply(b,tn,meter)),Q(-1)) for a,b in lines]
                constraints=[bi,[-c for c in bj],tn,_add(den,tn,Q(-1))]+gaps
                if not all(_value(den,x,meter)>0 for x in (Q(0),theta)):continue
                if not all(nonnegative_on_interval(c,Q(0),theta,meter) for c in constraints):continue
                # Convex dual: active coefficients are -bj/den and bi/den.
                # Their weighted slope is zero, and their weighted intercept
                # is rn/den; therefore every split point has envelope >=rn/den.
                dual=[[-c for c in bj],bi]
                _require(_add(dual[0],dual[1])==den and
                    _add(_multiply(dual[0],bi,meter),_multiply(dual[1],bj,meter))==[0] and
                    _add(_multiply(dual[0],ai,meter),_multiply(dual[1],aj,meter))==rn,
                    'whole-domain exact convex dual proof')
                cn=_divide(_add(den,rn,Q(-1)),[Q(1),Q(-1)],meter)
                accepted.append(dict(active_pair=[i,j],denominator=_strings(den),parameter_numerator=_strings(tn),
                    power_numerator=_strings(rn),C_power_numerator=_strings(cn),gap_polynomials=list(map(_strings,gaps)),
                    dual_weight_numerators=list(map(_strings,dual))))
    _require(bool(accepted),'at least one complete symbolic error minimax certificate')
    expected=accepted[0]
    expected.update(rule=rule,theta=str(theta),rho_domain=dict(lower='0',upper=str(theta),upper_excluded=True),
        lines=[dict(intercept=_strings(a),slope=_strings(b)) for a,b in lines],
        moment='complete ordinarily convergent conditional moment; rho<theta',
        scale='T0=C^(1/(1-rho)); R=n/T0; D=ceil(T0*R^t) when n>=T0',all_small_prefixes_included=True,
        retained_euler_compensation=dict(coefficient='c_theta',expression='h',bound='|c_theta|<=1/theta',
            separately_bounded=True) if rule=='euler_remainder' else None)
    return expected


def _primitive_integers(values):
    denominator=1
    for q in values:denominator=denominator*q.denominator//gcd(denominator,q.denominator)
    integers=[int(q*denominator) for q in values]
    divisor=0
    for n in integers:divisor=gcd(divisor,abs(n))
    _require(divisor>0,'nontrivial backwards inequality')
    return [n//divisor for n in integers]


def _region(family,alpha,p,goal,meter):
    den=list(map(Q,family['denominator']));rn=list(map(Q,family['power_numerator']))
    cn=list(map(Q,family['C_power_numerator']));_require(len(cn)==1,'constant C numerator in licensed family')
    critical=(Q(goal)+1)/2;bc=alpha*cn[0]
    # e<critical iff alpha*cn*b + rn + alpha*cn*p*(1-rho)
    #              -critical*den < 0, since den is positive everywhere.
    remainder=_add(_add(rn,[bc*p,-bc*p]),[-critical*c for c in den])
    _require(len(remainder)<=2,'exact affine backwards bound region')
    integers=_primitive_integers([bc,remainder[1] if len(remainder)==2 else Q(0),-remainder[0]])
    return dict(b_coefficient=str(integers[0]),rho_coefficient=str(integers[1]),rhs=str(integers[2]),
        relation='<',b_lower='0',rho_domain=family['rho_domain'],target_energy_power=goal,
        critical_prefix_power=str(critical),
        bound_schema='exists fixed C,k: |P_(E^m)(t)|<=C U^b t^rho (1+log(2Ut))^k; all U,t>=1',
        finite_factor_U_cost=str(p)+'*(1-rho)',
        equality_scope='fixed polylogarithmic energy only; no constant payment at equality')


def _substitution(region,j,meter):
    a,b,c=[Q(region[k]) for k in ('b_coefficient','rho_coefficient','rhs')]
    slope=b-a*j;rhs=c-a*j;upper=Q(region['rho_domain']['upper'])
    # A strict affine inequality cannot hold at only the excluded upper end:
    # whenever the upper value is strict, a neighboring included point works.
    feasible=min(Q(0),slope*upper)<rhs
    meter.charge(50)
    return dict(j=j,substitution=dict(b_constant=str(j),b_rho_coefficient=str(-j)),
        kappa_coefficient=str(slope),rhs=str(rhs),relation='<',kappa_domain=region['rho_domain'],
        has_strictly_feasible_exponent=feasible,threshold=str(rhs/slope) if slope else None,
        status='conditional; the complete remainder estimate has not been proved')


def _point(family,point,meter):
    _require(type(point) is dict and set(point)=={'rho','split','C_power'},'complete rational diagnostic or current point')
    rho=_rational(point['rho'],meter);theta=Q(family['theta'])
    _require(0<=rho<theta,'strict ordinary moment convergence boundary')
    problem=dict(lower='0',upper='1',terms=[dict(intercept=str(_value(a,rho,meter)),
        slope=str(_value(b,rho,meter))) for a,b in _lines(theta,family['rule'])])
    _require(_same(point['split']['problem'],problem),'rational split uses licensed error family')
    verify_split(point['split'],meter)
    den=_value(list(map(Q,family['denominator'])),rho,meter)
    t=_value(list(map(Q,family['parameter_numerator'])),rho,meter)/den
    r=_value(list(map(Q,family['power_numerator'])),rho,meter)/den
    cp=_value(list(map(Q,family['C_power_numerator'])),rho,meter)/den
    _require(Q(point['split']['parameter'])==t and Q(point['split']['power'])==r and
        point['C_power']==str(cp) and cp==(1-r)/(1-rho),'diagnostic optimum and full cutoff C cost')
    return rho,r,cp


def _extract_tail(expression,basis,outer,meter):
    anchor=Q(0);tail=[Q(0)]*len(basis)
    for term in expression:
        coefficient=_rational(term['coefficient'],meter);factors=list(term['factors'])
        if not factors:anchor+=coefficient;continue
        _require(factors.count(outer)==1,'one shared outer convolution factor')
        factors.remove(outer)
        _require(len(factors)<=1 and (not factors or factors[0] in basis),'finite affine convolution tail')
        atom=factors[0] if factors else 'delta';tail[basis.index(atom)]+=coefficient
    _require(all(c.denominator==1 for c in tail),'integer finite factor grammar')
    return str(anchor),[int(c) for c in tail]


def _factor_search(radius,meter,basis=None,moments=None,expression=None):
    basis=basis or ['A','C','delta']
    moments=moments or [{'c':'1'},{'c':'1'},{'one':'1'}]
    expression=expression or [dict(coefficient='1',factors=[]),dict(coefficient='-1',factors=['O','A']),
        dict(coefficient='1',factors=['O','C'])]
    _require(1<=len(basis)<=5 and len(moments)==len(basis),'bounded finite symbolic moment map')
    anchor,tail=_extract_tail(expression,basis,'O',meter)
    _require(anchor=='1','actual centered residual unit anchor')
    atoms=sorted({a for m in moments for a in m})
    candidates=[]
    for vector in product(range(-radius,radius+1),repeat=len(basis)):
        divisor=0
        for c in vector:divisor=gcd(divisor,abs(c))
        meter.charge(10*len(basis))
        if divisor!=1:continue
        moment={}
        for atom in atoms:
            coefficient=sum((Q(c)*Q(m.get(atom,'0')) for c,m in zip(vector,moments)),Q(0))
            if coefficient:moment[atom]=str(coefficient)
        candidates.append(dict(coefficients=list(vector),harmonic_moment=moment,zero_moment=not moment,
            exact_tail_match=list(vector)==tail))
    matches=[i for i,c in enumerate(candidates) if c['zero_moment'] and c['exact_tail_match']]
    _require(len(matches)==1,'unique source-tail factor found in full primitive search')
    return dict(basis=basis,harmonic_moment_map=moments,required_convolution_tail=tail,
        coefficient_radius=radius,candidates=candidates,selected=matches[0],
        selection='first exact tail match with identically zero harmonic moment',
        supplied_residual_expression=expression,extracted_anchor=anchor,outer_factor='O')


def _source(parent,meter):
    _require(parent.get('whole_signed_bound_proved') is False and parent.get('RH_proved') is False,'original full core remains open')
    source=parent['selected_source_representation'];alpha=_rational(source['alpha'],meter);gamma=_rational(source['gamma'],meter)
    _require(source.get('full_signed_bound_proved') is False and source.get('RH_proved') is False,'inherited source representation does not claim closure')
    _require(0<alpha<1 and 0<gamma<1,'strict common-horizon cutoffs')
    cases=source['cases'];_require(type(cases) is list and len(cases)==4,'all four source modes')
    profiles={('B','beta',2,0,'1/3'),('U','-beta',1,1,'1/3'),('V','-beta',1,0,None),('power','-R_u',0,1,'1/3')}
    _require({(c['mode']['name'],c['mode']['coefficient'],c['mode']['p'],c['mode']['q'],c['mode']['positive_shift'])
        for c in cases}==profiles,'actual full signed source profiles')
    count=0;polynomial={};origins=[]
    for case in cases:
        mode=case['mode'];p=_integer(mode['p'],0,2);q=_integer(mode['q'],0,2)
        verify_inverse(case['program'],alpha,gamma,p,q,meter)
        for term in case['program']['terms']:
            count+=1;a,b=term['a'],term['b'];inverse=Q(term['coefficient'])
            # Multiply a copies of (E-C*O), independently of binomial formula.
            residual=[Q(1)]
            for _ in range(a):residual=_multiply(residual,[Q(-1),Q(1)],meter)
            scalar=Q(-1) if mode['coefficient']=='-R_u' else Q(9,2)*(1 if mode['coefficient']=='beta' else -1)
            expansion=[]
            for m,c in enumerate(residual):
                powers=(p,q,int(mode['positive_shift'] is not None),m,b,a-m,a-m,int(mode['coefficient']=='-R_u'))
                coefficient=inverse*scalar*c;polynomial[powers]=polynomial.get(powers,Q(0))+coefficient
                expansion.append(dict(powers=list(powers),coefficient=str(coefficient)));meter.charge(35)
            origins.append(dict(mode=mode['name'],a=a,b=b,terms=expansion))
    _require(type(source['component_count']) is int and source['component_count']==count,'every original source term accounted for')
    return dict(symbols=['A','B','K','E','S','C','O','R_u'],
        substitution='R=E-C*O; C=c*delta; c=sum_(d<=U)mu(d)/d',
        collected_terms=[dict(powers=list(k),coefficient=str(c)) for k,c in sorted(polynomial.items()) if c],
        source_expansions=origins,transport_error=dict(coefficient='-1',definition='e=f-g'),all_compensations_retained=True,
        common_horizon='N=4X-1; every source prefix n<=N; U=floor(N^alpha), V=floor(N^gamma)',
        scope='exact alternative source representation; nonzero formal terms need not be arithmetically independent')


def _moment(j,meter):
    trace=[dict(left_order=i,right_order=1,product_order=i+1) for i in range(j)]
    main=[]
    for degree in range(j):
        # Expand (log n-log d)^degree, then apply moments of T^j/d.
        terms=[dict(log_n_power=degree-k,moment_degree=k,coefficient=str((-1)**k*comb(degree,k)))
            for k in range(degree+1)]
        main.append(dict(main_log_degree=degree,terms=terms,identically_zero=True));meter.charge(25*(degree+1))
    return dict(j=j,finite_factor='T^j',moment_point='1',T_zero_moment=True,valuation_trace=trace,
        zero_moment_degrees=list(range(j)),main_term_expansions=main,
        polynomial='arbitrary fixed polynomial in log(x) of degree at most j-1',full_support_sum=True,
        include_d_greater_than_n=True,remainder_definition='Delta_j(x)=D_j(x)-x*P_(j-1)(log(x)); EVERY real x>0',
        D_definition='D_j(x)=sum_(n<=x) (One^j)(n); zero for 0<x<1',bounded_polynomial=['1'] if j==1 else None,
        identity_proved=True,remainder_bound_proved=j==1)


def _baseline(m):
    if m==1:return dict(rho='0',U_power='1',constant='2',combined_log_degree=0)
    return dict(rho=str(Q(m-1,m)),U_power='1',constant=str(2*(2*m+1)*3**(m-1)),combined_log_degree=2*m-3)


def _target(target,term,alpha,spec,families,meter):
    p=term['powers'][0];m=term['powers'][3];known=_baseline(m);rho=Q(known['rho']);theta=Q(2,3)
    routes=[]
    _require(type(target) is dict and type(target.get('routes')) is list and len(target['routes'])==2,'both backwards proof routes')
    for family,route in zip(families,target['routes']):
        region=_region(family,alpha,p,spec['energy_power'],meter)
        if rho>=theta:
            current=dict(status='unlicensed',reason='rho>=theta: complete ordinary moment not established by this bound')
        else:
            declared=route['current_generic_bound']
            point={k:declared[k] for k in ('rho','split','C_power')}
            point_rho,r,cp=_point(family,point,meter);_require(point_rho==rho,'baseline moment exponent')
            # Finite A^p contributes p*(1-rho) BEFORE the C exponent.
            e=r+alpha*cp*(1+p*(1-rho))
            _require(2*e-1>=Q(spec['energy_power']),'new payable component needs a complete constants/recovery implementation')
            current=dict(status='proved exponent with fixed polylogarithmic losses',**point,
                prefix_N_power=str(e),energy_N_power=str(2*e-1),strictly_meets_target=False)
        regions=[_substitution(region,j,meter) for j in range(2,m+1)]
        declared_heads=route.get('proved_head_branches');_require(type(declared_heads) is list and len(declared_heads)==2,'both known heads explicitly costed')
        heads=[]
        for j,declared in enumerate(declared_heads):
            point={k:declared[k] for k in ('rho','split','C_power')}
            head_rho,head_r,head_cp=_point(family,point,meter);_require(head_rho==0,'bounded known head prefix')
            head_e=head_r+alpha*head_cp*(j+p)
            heads.append(dict(j=j,b=str(j),**point,prefix_N_power=str(head_e),energy_N_power=str(2*head_e-1),
                strictly_meets_target=2*head_e-1<Q(spec['energy_power'])))
        feasible=all(r['has_strictly_feasible_exponent'] for r in regions)
        routes.append(dict(rule=family['rule'],family_reference=family['rule'],current_generic_bound=current,
            missing_prefix_bound_region=region,proved_head_branches=heads,remainder_branch_regions=regions,
            all_remainder_branches_feasible=feasible,
            conditional_auxiliary_route_has_feasible_exponents=feasible and all(h['strictly_meets_target'] for h in heads)))
    branches=[dict(j=j,coefficient=str(comb(m,j)),prefix_rule='delta' if j==0 else
        'complete_floor_remainder' if j==1 else 'complete_kernel_remainder',status='proved' if j<2 else 'open',
        rho='0' if j<2 else 'kappa_j',U_power='0' if j==0 else '1' if j==1 else str(j)+'*(1-kappa_j)',
        constant='1' if j==0 else '3' if j==1 else 'C_j*(2+1/(1-kappa_j))^'+str(j),
        mass_bound=dict(constant=str(3**j),U_log_degree=j,t_log_degree=max(0,j-1),t_power='1'),
        uniform_quantifiers='fixed finite constants and log degrees; EVERY U,t>=1',
        complete_remainder_for_all_positive_arguments=True) for j in range(m+1)]
    identity=[dict(j=j,coefficient=str(comb(m,j)),kernel='One^j',finite_factor='T^j') for j in range(m+1)]
    expected=dict(id='centered_A'+str(p)+'_E'+str(m),source_term=term,p=p,m=m,
        target='P_(K*A^p*E^m - m_theta(A^p*E^m)*J_theta/theta)',theta='2/3',original_moment_drift_retained=True,
        moment_drift_status='conditional on ordinary convergence; never discarded',generic_prefix_rule=known,routes=routes,
        auxiliary_identity=dict(anchor='delta',base='E=delta+One*T',terms=identity,
            all_j_including_zero_retained=True,identity_proved=True),remainder_branches=branches,
        status='open',component_bound_proved=False,complete_source_bound_proved=False)
    _require(_same(target,expected),'full auxiliary identity, backward costs, exact gates and conditional status')


def _graph(targets):
    nodes=[dict(id='finite_moment_factor',status='proved',depends_on=[]),
        dict(id='generic_multiple_prefix_rule',status='proved',depends_on=[])]
    for target in targets:
        ident=target['id']
        for branch in target['remainder_branches']:
            j=branch['j'];nodes.append(dict(id=ident+'_remainder_'+str(j),status=branch['status'],
                depends_on=['finite_moment_factor'],expression='complete D_'+str(j)+' remainder bound' if j>1 else branch['prefix_rule']))
        nodes.append(dict(id=ident,status='open',depends_on=[ident+'_remainder_'+str(j) for j in range(target['m']+1)],
            dependency_semantics='necessary proof obligations in this branch; exponent/cost gates must also pass'))
    nodes.append(dict(id='complete_signed_complement',status='open',depends_on=[],
        expression='every remaining source term, every centering drift and the exact transport error; retain their signed correlations'))
    nodes.append(dict(id='actual_signed_core',status='open',depends_on=[t['id'] for t in targets]+['complete_signed_complement'],
        other_obligations='all untouched terms, compensating drifts, joint correlations and exact transport error remain'))
    nodes.append(dict(id='original_RH_recovery',status='conditional',depends_on=['actual_signed_core']))
    return nodes


def _audit_graph(nodes,meter):
    _require(type(nodes) is list and len(nodes)<=10000,'bounded explicit proof dependency graph')
    lookup={node['id']:node for node in nodes};_require(len(lookup)==len(nodes),'unique proof node ids')
    visiting=set();done=set()
    def visit(ident):
        _require(ident in lookup and ident not in visiting,'known acyclic proof dependencies')
        if ident in done:return
        visiting.add(ident);node=lookup[ident]
        _require(node['status'] in ('proved','open','conditional'),'explicit proof status')
        for child in node['depends_on']:
            visit(child)
            _require(node['status']!='proved' or lookup[child]['status']=='proved','proved node cannot depend on an open premise')
            meter.charge(30)
        visiting.remove(ident);done.add(ident)
    for ident in lookup:visit(ident)


def _next_tasks(targets):
    tasks=[dict(target_id='actual_signed_core',search_kind='joint_signed_core_control',status='open',priority=0,
        preserve='complete signed join, inherited recovery and all compensation/error terms')]
    for target in targets:
        routes=[r['rule'] for r in target['routes'] if r['conditional_auxiliary_route_has_feasible_exponents']]
        tasks.append(dict(target_id=target['id'],status='open',priority=1,
            search_kind='search_complete_remainder_bounds' if routes else 'search_joint_weighted_remainder_control',
            conditionally_admissible_routes=routes,
            reason='some separate remainder exponents satisfy the derived cost gates; their proofs remain open' if routes else
                'no separate remainder-bound portfolio in this declared family pays all branches at the current cutoff',
            preserve='the entire signed auxiliary identity, finite T^j weights, unit, all quotients and full centering moment',
            prohibits='do not infer arithmetic impossibility or close an estimate from its requested exponent'))
    return tasks


def verify_search(parent,result,meter):
    _require(type(result) is dict and set(result)=={'schema','spec','inherited_selected_source','inherited_bound_obligations',
        'inherited_proof_frontier','complete_signed_join','factor_search','symbolic_bound_families','diagnostic_minimax',
        'moment_cancellation_certificates','generated_bound_targets','proof_dependencies','next_search_tasks','statistics',
        'actual_source_observations','model_calls_in_search','detector_has_general_analytic_prover','whole_signed_bound_proved','RH_proved'},
        'complete bound-goal search schema')
    _require(result['schema']=='core-bound-goal-search-v1','bound-goal schema')
    spec=result['spec'];_require(type(spec) is dict and set(spec)=={'linear_coefficient_radius','maximum_residual_degree',
        'diagnostic_denominator_max','energy_power'},'complete declared goal grammar')
    radius=_integer(spec['linear_coefficient_radius'],1,4);maxdegree=_integer(spec['maximum_residual_degree'],2,64)
    diagmax=_integer(spec['diagnostic_denominator_max'],2,24);_rational(spec['energy_power'],meter)
    join=_source(parent,meter);source=parent['selected_source_representation']
    _require(_same(result['inherited_selected_source'],source) and
        _same(result['inherited_bound_obligations'],parent['generated_bound_obligations']) and
        _same(result['inherited_proof_frontier'],parent['proof_frontier']),'complete prior representation, paid join and route frontier retained verbatim')
    _require(_same(result['complete_signed_join'],join),'every original signed expansion, companion and exact -e retained')
    degree=max(t['powers'][3] for t in join['collected_terms']);_require(degree<=maxdegree,'cap failure cannot truncate residual powers')
    factor=_factor_search(radius,meter);_require(_same(result['factor_search'],factor),'whole primitive linear-factor search and source-match selection')
    families=[_family(Q(2,3),rule,meter) for rule in ('ordinary','euler_remainder')]
    _require(_same(result['symbolic_bound_families'],families),'generated symbolic minimax, exact duals, all-small-n scope and compensation')
    rationals=sorted({Q(n,d) for d in range(1,diagmax+1) for n in range(d+1) if Q(n,d)<Q(2,3)})
    diagnostics=result['diagnostic_minimax'];_require(type(diagnostics) is list and len(diagnostics)==2,'both complete diagnostic families')
    for family,diagnostic in zip(families,diagnostics):
        _require(set(diagnostic)=={'rule','points'} and diagnostic['rule']==family['rule'] and
            type(diagnostic['points']) is list and len(diagnostic['points'])==len(rationals),'all diagnostic rational probes')
        for expected,point in zip(rationals,diagnostic['points']):
            rho,_,_=_point(family,point,meter);_require(rho==expected,'all reduced rational probes in order')
    moments=[_moment(j,meter) for j in range(1,degree+1)]
    _require(_same(result['moment_cancellation_certificates'],moments),'all product jets and arbitrary log-polynomial moment annihilations')
    eligible=[t for t in join['collected_terms'] if t['powers'][2]==1 and t['powers'][3]>=2 and
        all(t['powers'][i]==0 for i in (1,4,5,6,7))]
    targets=result['generated_bound_targets'];_require(type(targets) is list and len(targets)==len(eligible),'every surviving eligible pure residual target')
    for target,term in zip(targets,eligible):_target(target,term,Q(source['alpha']),spec,families,meter)
    _audit_graph(result['proof_dependencies'],meter)
    _require(_same(result['proof_dependencies'],_graph(targets)),'complete conditional target graph and original signed recovery')
    tasks=_next_tasks(targets);_require(_same(result['next_search_tasks'],tasks),'next search language derived from proved conditional cost gates')
    stats=dict(original_source_terms=source['component_count'],collected_signed_terms=len(join['collected_terms']),
        linear_candidates=len(factor['candidates']),zero_moment_candidates=sum(c['zero_moment'] for c in factor['candidates']),
        source_matched_factors=1,generated_bound_targets=len(targets),kernel_remainder_branches=sum(t['m']-1 for t in targets),
        symbolic_bound_families=2,independent_rational_split_probes=2*len(rationals),
        inherited_bindings=len(parent['generated_bound_obligations']),new_component_bounds_proved=0,
        targets_redirected_to_joint_control=sum(t['search_kind']=='search_joint_weighted_remainder_control' for t in tasks))
    _require(_same(result['statistics'],stats),'exact search counts exclude conditional goals from theorem counts')
    _require(type(result['actual_source_observations']) is int and result['actual_source_observations']==0 and
        type(result['model_calls_in_search']) is int and result['model_calls_in_search']==0 and
        result['detector_has_general_analytic_prover'] is False and result['whole_signed_bound_proved'] is False and
        result['RH_proved'] is False,'no fitted source observations or false arithmetic closure')
    meter.live(30*len(join['collected_terms'])+100*len(targets)+100*len(moments))
    return dict(verified=True,targets=len(targets),source_terms=source['component_count'],
        inherited_bindings=len(parent['generated_bound_obligations']),new_component_bounds_proved=0,
        complete_source_bound_proved=False,RH_proved=False)


def verify_feedback(result,feedback,input_file,artifact,meter):
    _require(type(input_file) is str and bool(input_file) and type(artifact) is str and bool(artifact),'explicit immutable artifact references')
    expected=dict(schema='core-bound-goal-feedback-v1',status='open',parent_obligation_file=input_file,
        complete_search_artifact=artifact,selected_source_representation=result['inherited_selected_source'],
        generated_bound_obligations=result['inherited_bound_obligations'],auxiliary_bound_targets=result['generated_bound_targets'],
        proof_dependencies=result['proof_dependencies'],next_search_tasks=result['next_search_tasks'],
        retained_original_proof_frontier=result['inherited_proof_frontier'],
        next_priority='search the open arithmetic remainder estimates AND the complete signed join; keep full recovery costs',
        all_remainder_estimates_are_conditional=True,new_component_bounds_proved=0,
        scope='checked auxiliary identities and backwards requirements; no new full signed control',whole_signed_bound_proved=False,RH_proved=False)
    _require(_same(feedback,expected),'retained original frontier, all conditional estimates and open complete source')
    meter.charge(300+50*len(result['generated_bound_targets']))
    return dict(verified=True,status='open',new_component_bounds_proved=0)
