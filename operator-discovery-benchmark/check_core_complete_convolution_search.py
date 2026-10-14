"""Independent complete-prefix pricing and analytic centered-transfer audit."""
import copy
import itertools
import math
from fractions import Fraction as Q

import check_core_convolution_argument_search as PRIOR

require=PRIOR.require
number=PRIOR.number
equal=PRIOR.equal
encode=PRIOR.encode
accumulate=PRIOR.accumulate
product=PRIOR.product


def polynomial(rows,meter):
    require(type(rows) is list,'polynomial list')
    out={};last=None
    for row in rows:
        require(type(row) is dict and set(row)=={'key','value'} and type(row['key']) is list,'polynomial fields')
        key=tuple(row['key'])
        require(all(type(v) is str and v in {'C','E','R','T'} for v in key) and tuple(sorted(key))==key and len(key)<=6,
                'typed Dirichlet monomial')
        require(last is None or last<key,'sorted unique monomials')
        value=number(row['value'],meter)
        require(type(row['value']) is str and str(value)==row['value'] and value,'nonzero canonical coefficient')
        out[key]=value;last=key
    return out


def linear(columns,source,cert,meter):
    require(type(cert) is dict and cert.get('status') in {'feasible','infeasible'},'linear proof status')
    if cert['status']=='feasible':
        require(set(cert)=={'status','solution'} and type(cert['solution']) is list,'primal fields')
        last=-1;out={}
        for row in cert['solution']:
            require(type(row) is dict and set(row)=={'column','coefficient'},'primal term')
            index=row['column'];coefficient=number(row['coefficient'],meter)
            require(type(index) is int and last<index<len(columns),'complete column index')
            require(type(row['coefficient']) is str and str(coefficient)==row['coefficient'] and coefficient,'primal rational')
            accumulate(out,columns[index],coefficient);last=index;meter.charge(1+len(columns[index]))
        require(out==source,'exact primal identity')
        return True
    require(set(cert)=={'status','dual','contradiction'},'dual fields')
    y=polynomial(cert['dual'],meter)
    universe=set(source).union(*(set(c) for c in columns))
    require(set(y)<=universe,'complete dual constraint universe')
    for c in columns:
        require(sum((y.get(k,0)*v for k,v in c.items()),Q(0))==0,'dual annihilates every allowed column')
        meter.charge(1+len(c))
    contradiction=sum((y.get(k,0)*v for k,v in source.items()),Q(0))
    require(contradiction and contradiction==number(cert['contradiction'],meter),'nonzero dual contradiction')
    return False


def term(c=1,u=0,x=0,lu=0,lx=0):
    return dict(constant=str(Q(c)),U_power=str(Q(u)),X_power=str(Q(x)),logU_degree=lu,logX_degree=lx)


def collect(rows):
    out={}
    for row in rows:
        key=(Q(row['U_power']),Q(row['X_power']),row['logU_degree'],row['logX_degree'])
        out[key]=out.get(key,Q(0))+Q(row['constant'])
    return [term(c,*key) for key,c in sorted(out.items()) if c]


def scaled(rows,c):
    return [dict(row,constant=str(Q(row['constant'])*c)) for row in rows if c]


def cost(rows,rho):
    require(rows,'nonempty proved envelope')
    top=max((Q(t['X_power'])+rho*Q(t['U_power']),t['logU_degree']+t['logX_degree']) for t in rows)
    constant=sum((Q(t['constant']) for t in rows if
                 (Q(t['X_power'])+rho*Q(t['U_power']),t['logU_degree']+t['logX_degree'])==top),Q(0))
    return (*top,constant)


def fraction_grid():
    return sorted({Q(a,b) for b in range(2,7) for a in range(1,b)})


def mass(m,profile):
    return [term(3**m,0,1,m if profile=='bounded' else 0,2*m-1)]


def finite_lift(rows,caps,profile):
    require(profile in {'mobius','bounded'},'coefficient premise profile')
    caps=[Q(cap) for cap in caps]
    require(all(0<a<=1 for a in caps),'finite cutoff powers')
    k=len(caps);out=[]
    for row in rows:
        exponent=Q(row['X_power'])
        require(0<=exponent<=1,'weighted divisor premise domain')
        if exponent==1:
            c,x,logs=Q(3)**k,Q(1),2*k
        else:
            c,x,logs=(3/(1-exponent))**k,exponent+(1-exponent)*sum(caps,Q(0)),k
        out.append(term(Q(row['constant'])*c,row['U_power'],x,
            row['logU_degree']+(k if profile=='bounded' else 0),row['logX_degree']+logs))
    return collect(out)


def finite_power(m,alpha,profile,rho):
    candidates=[dict(rule='coefficient_mass',bound=mass(m,profile)),
        dict(rule='keep_one_signed_prefix',bound=finite_lift([term(2,1)],[alpha]*(m-1),profile))]
    if m*alpha<=1:candidates.append(dict(rule='complete_rectangle',bound=[term(2**m,m)]))
    best=min(range(len(candidates)),key=lambda i:cost(candidates[i]['bound'],rho)+(i,))
    return dict(candidates=candidates,selected=best,bound=candidates[best]['bound'])


def verify_prefix_library(result,meter):
    require(type(result) is dict,'prefix library')
    profile=result['profile'];rho=number(result['rho'],meter)
    require(profile in {'mobius','bounded'} and 0<rho<1,'prefix assumptions and scale')
    require(type(result['levels']) is list and 1<=len(result['levels'])<=4,'bounded acyclic power grammar')
    levels=[dict(power=1,selected=0,candidates=[dict(rule='bounded_prefix',bound=[term(2,1)])],bound=[term(2,1)])]
    equal(result['levels'][0],levels[0],meter,'unit, all-history prefix premise')
    for m in range(2,len(result['levels'])+1):
        source={('E',)*m:Q(1)}
        basis=[{('E',)*(m-k)+('T',)*k:Q(1)} for k in range(1,m+1)]
        ideal={('E',)*(m-k)+('T',)*k:Q((-1)**k*math.comb(m,k)) for k in range(m+1)}
        alphas=[a for a in fraction_grid() if m*a>=1]
        provided=result['levels'][m-1]
        require(type(provided['candidates']) is list and len(provided['candidates'])==1+len(alphas),'all power cutoffs')
        candidates=[dict(rule='coefficient_mass',bound=mass(m,profile))]
        for candidate,alpha in zip(provided['candidates'][1:],alphas):
            cert=candidate['certificate']
            require(linear(basis+[ideal],source,cert,meter),'complete power identity feasible')
            priced=[];bound=[]
            for item in cert['solution']:
                column=item['column']
                if column==m:continue
                k=column+1
                if k==m:price=finite_power(m,alpha,profile,rho)
                else:price=dict(rule='weighted_finite_lift',premise_power=m-k,
                               bound=finite_lift(levels[m-k-1]['bound'],[alpha]*k,profile))
                priced.append(dict(column=column,coefficient=item['coefficient'],pricing=price))
                bound+=scaled(price['bound'],abs(Q(item['coefficient'])))
            candidates.append(dict(rule='synthesized_hyperbola',alpha=str(alpha),source=encode(source),
                basis=[encode(b) for b in basis],ideal=encode(ideal),certificate=cert,priced_terms=priced,
                bound=collect(bound),full_product_indicator_retained=True))
        best=min(range(len(candidates)),key=lambda i:cost(candidates[i]['bound'],rho)+(i,))
        expected=dict(power=m,candidates=candidates,selected=best,bound=candidates[best]['bound'])
        equal(provided,expected,meter,'complete lower-power dependencies and signed head pricing')
        levels.append(expected)
    expected=dict(profile=profile,rho=str(rho),levels=levels,
        quantifier='every fixed f with |prefix_f(x)|<=2U and |f(n)|<=K*d2(n), every real x>=1, uniformly in any truncation of f',
        K='3' if profile=='mobius' else '3*(1+log U)',ordinary_critical_moment_convergence_assumed=False)
    equal(result,expected,meter,'uniform complete prefix proof library')
    return dict(verified=True,powers=len(levels))


def substitution(p,mapping,meter):
    out={}
    for key,c in p.items():
        value={():c}
        for variable in key:value=product(value,mapping[variable],meter)
        accumulate(out,value)
    return out


def verify_normalization(g,result,meter):
    # Replay the inherited short identity, not its producer search or old suite.
    PRIOR.verify_geometry(g,meter)
    joined=product(PRIOR.decode(g['one_e_coefficient'],meter),{('e',):Q(1)},meter)
    accumulate(joined,PRIOR.decode(g['finite_head'],meter))
    mapping={'C':{('C',):Q(1)},'e':{('E',):Q(1),('C',):Q(-1)},
             'r':{('R',):Q(1),('C',):Q(-1)},'t':{('T',):Q(1),('C',):Q(-1)}}
    affine=substitution(joined,mapping,meter)
    remainder=substitution(PRIOR.decode(g['vanishing_remainder'],meter),mapping,meter)
    total=dict(affine);accumulate(total,remainder)
    require(total=={('E',)*g['m']:Q(1)},'whole affine source before specialization')
    reduced={k:c for k,c in affine.items() if 'C' not in k}
    vanished={k:c for k,c in remainder.items() if 'C' not in k}
    total=dict(reduced);accumulate(total,vanished)
    require(total=={('E',)*g['m']:Q(1)},'C-independent complete tail identity')
    expected=dict(alpha=g['alpha'],beta=g['beta'],affine_join=encode(affine),affine_remainder=encode(remainder),
        normalized_join=encode(reduced),normalized_remainder=encode(vanished),
        license='tails E-T and E-R are independent of C; specialize the complete polynomial identity at C=0',
        domain='coefficients n<=N with the original fixed integer cutoffs',full_source_retained=True)
    equal(result,expected,meter,'whole affine normalization, head and mean collection')
    return dict(verified=True)


def geometry_columns(alpha,beta,meter):
    require(0<alpha<=beta<1,'strict short geometry')
    letters=('E','R','T')
    basis=[{key:Q(1)} for key in itertools.combinations_with_replacement(letters,3) if key.count('E')<=2]
    ideals=[];support=[]
    for a in range(4):
        for b in range(4-a):
            lower=a*alpha+b*beta
            if not a+b or lower<1:continue
            tail={}
            for i in range(a+1):
                for j in range(b+1):
                    key=tuple(sorted(('E',)*(a+b-i-j)+('T',)*i+('R',)*j))
                    accumulate(tail,{key:Q((-1)**(i+j)*math.comb(a,i)*math.comb(b,j))})
            for key in itertools.combinations_with_replacement(letters,3-a-b):
                ideals.append(product({key:Q(1)},tail,meter))
                support.append(dict(t_tail_power=a,r_tail_power=b,multiplier=list(key),support_power=str(lower)))
    return basis,ideals,support


def monomial_price(key,alpha,beta,library,meter):
    profile=library['profile'];rho=Q(library['rho']);caps={'E':Q(1),'T':alpha,'R':beta}
    candidates=[dict(rule='coefficient_mass',bound=mass(len(key),profile))]
    if 'E' not in key and sum((caps[v] for v in key),Q(0))<=1:
        candidates.append(dict(rule='complete_rectangle',bound=[term(2**len(key),len(key))]))
    for variable in sorted(set(key)):
        count=key.count(variable)
        require(variable!='E' or count<3,'no original cubic target as a premise')
        candidates.append(dict(rule='uniform_power_then_finite_lift',base=variable,premise_power=count,
            bound=finite_lift(library['levels'][count-1]['bound'],[caps[v] for v in key if v!=variable],profile)))
        meter.charge(10)
    best=min(range(len(candidates)),key=lambda i:cost(candidates[i]['bound'],rho)+(i,))
    return dict(candidates=candidates,selected=best,bound=candidates[best]['bound'])


def verify_geometry(result,library,meter):
    verify_prefix_library(library,meter)
    a,b=number(result['alpha'],meter),number(result['beta'],meter);rho=Q(library['rho'])
    basis,ideals,support=geometry_columns(a,b,meter)
    prices=[monomial_price(next(iter(c)),a,b,library,meter) for c in basis]
    costs=[cost(p['bound'],rho)[:2] for p in prices];thresholds=sorted(set(costs))
    require(type(result['trials']) is list and len(result['trials'])==len(thresholds),'all full-cost thresholds')
    source={('E',)*3:Q(1)};trials=[];viable=[]
    for i,(provided,threshold) in enumerate(zip(result['trials'],thresholds)):
        allowed=[j for j,c in enumerate(costs) if c<=threshold]
        feasible=linear([basis[j] for j in allowed]+ideals,source,provided['certificate'],meter)
        row=dict(threshold=[str(threshold[0]),threshold[1]],allowed=allowed,certificate=provided['certificate'])
        if feasible:
            representation={};bound=[]
            for item in provided['certificate']['solution']:
                if item['column']<len(allowed):
                    j=allowed[item['column']];c=Q(item['coefficient'])
                    accumulate(representation,basis[j],c);bound+=scaled(prices[j]['bound'],abs(c))
            row.update(representation=encode(representation),bound=collect(bound));viable.append(i)
        equal(provided,row,meter,'full-cost threshold primal/dual')
        trials.append(row)
    require(viable,'fully priced source representation')
    best=min(viable,key=lambda i:cost(trials[i]['bound'],rho)+(i,))
    expected=dict(alpha=str(a),beta=str(b),basis=[encode(c) for c in basis],ideals=[encode(c) for c in ideals],
        support_certificates=support,monomial_prices=prices,trials=trials,selected=best,bound=trials[best]['bound'],
        every_finite_head_priced=True,scope='complete E^3 prefix, uniformly for integer N>=1; outer A and K not yet applied')
    equal(result,expected,meter,'all finite heads priced, minimum certified whole bound')
    return dict(verified=True,thresholds=len(thresholds))


def outer_lift(bound,p,m,profile):
    # The bound is for the COMPLETE E^m prefix at every horizon. Its
    # auxiliary cutoffs can be selected afresh at floor(x/d). This is not
    # a claim that a fixed parent's T/R cutoff contracts inside the lift.
    require(profile in {'mobius','bounded'} and type(p) is int and 0<=p<=6 and type(m) is int and m==p+1,
            'declared One_[1,U] head and outer powers')
    rows=[]
    for t in bound:
        beta=Q(t['X_power']);require(0<=beta<=1,'outer weighted mass decay')
        c,u,logs=((1/(1-beta))**p,p*(1-beta),0) if beta<1 else (Q(1),Q(0),p)
        rows.append(term(Q(t['constant'])*c,Q(t['U_power'])+u,beta,t['logU_degree']+logs,t['logX_degree']))
    rows.append(term(2**m if profile=='mobius' else 1,1,0,m if profile=='bounded' else 0))
    return collect(rows)


def squared(bound):
    # Every ordered pair is retained, including mixed powers and logs.
    return collect([term(Q(a['constant'])*Q(b['constant']),Q(a['U_power'])+Q(b['U_power']),
        Q(a['X_power'])+Q(b['X_power'])-1,a['logU_degree']+b['logU_degree'],a['logX_degree']+b['logX_degree'])
        for a in bound for b in bound])


def verify_transfer(result,meter):
    p=result['p'];theta=number(result['theta'],meter);rho=number(result['rho'],meter)
    profile=result['profile']
    require(type(p) is int and 0<=p<=6 and 0<theta<1 and 0<rho<1 and profile in {'mobius','bounded'},
            'centered transfer parameters and coefficient class')
    u=1-theta;c1=Q(216)/(theta*u**(p+2))
    c2=Q(144)*((2 if profile=='mobius' else 3)/u+8)/(theta*u**p)
    tail_logs,defect_logs=(4,0) if profile=='mobius' else (8,4)
    declared=[(Q(a),Q(b),base) for a,b in PRIOR.geometry_grid() if Q(a)>=rho for base in ('T','R')]
    require(type(result['trials']) is list and len(result['trials'])==len(declared),'all transfer cutoffs and square bases')
    trials=[];eligible=[]
    source={('E',)*3:Q(1),('R',)*3:Q(-1)}
    for i,(provided,(a,b,base)) in enumerate(zip(result['trials'],declared)):
        _,ideals,support=geometry_columns(a,b,meter)
        column={(base,base,'E'):Q(1),(base,base,'R'):Q(-1)}
        column={tuple(sorted(k)):v for k,v in column.items()}
        feasible=linear([column]+ideals,source,provided['certificate'],meter)
        cutoff=a if base=='T' else b
        row=dict(alpha=str(a),beta=str(b),base=base,effective_short_cutoff=str(cutoff),
                 column=encode(column),support_certificates=support,certificate=provided['certificate'])
        if feasible:
            coefficient=sum((Q(t['coefficient']) for t in provided['certificate']['solution'] if t['column']==0),Q(0))
            require(coefficient==3,'exact solved square coefficient')
            tail=2*rho*(1+p*u)+4*u*cutoff+2*theta-1-2*theta*b
            defect=2*rho*(2+(p+1)*u)+2*theta-1-2*theta*(cutoff+b)
            paid=max(tail,defect)<0
            row.update(coefficient='3',normalized_error_energy=[
                dict(constant=str(8*c1*c1),N_power=str(tail),log_degree=tail_logs),
                dict(constant=str(32*c2*c2),N_power=str(defect),log_degree=defect_logs)],subcritical_padding=paid,
                moment_defect='A(theta)^p*J(theta)*(E(theta)^2+E(theta)*R(theta)+R(theta)^2-3*S(theta)^2)',
                analytic_moment_not_inferred_from_local_identity=True)
            if paid:eligible.append(i)
        equal(provided,row,meter,'exact transfer, all-real tail, analytic defect and energy costs')
        trials.append(row)
    best=min(eligible,key=lambda i:(Q(trials[i]['beta']),
        max(Q(t['N_power']) for t in trials[i]['normalized_error_energy']),Q(trials[i]['alpha']),i)) if eligible else None
    expected=dict(p=p,theta=str(theta),rho=str(rho),profile=profile,trials=trials,selected=best,C1=str(c1),C2=str(c2),
        energy='N^-2*sum_(1<=n<=N)|S(n)|^2; all integer U,N>=1 with U<=N^rho',
        domain='t=floor(N^alpha)>=U, r=floor(N^beta)>=t; fixed N; S denotes the chosen short E truncation',
        exact_join='S_F=S_R+S_(hJ)-(mF-mR-h(theta)*J(theta))*n^theta/theta; h=3*A^p*S^2',
        retained_head='the SAME -c^3*D in F=A^p*E^3-c^3*D and Rsource=A^p*R^3-c^3*D',
        comparison='energy(F)<=2*energy(Rsource)+2*error_energy and conversely; error includes both pieces and their cross',
        full_finite_cube_bound_proved=False,global_fixed_U_Mellin_bound_proved=False)
    equal(result,expected,meter,'uniform centered transfer and shortest paid finite cube')
    return dict(verified=True,trials=len(trials),selected=best)


def source_binding(parent,meter):
    require(parent['schema']=='core-convolution-argument-feedback-v1','current accepted source')
    binding=PRIOR.source_binding(dict(parent,schema='core-bound-argument-feedback-v1'),meter)
    equal(binding,parent['convolution_argument_search']['binding'],meter,'unchanged original source')
    return binding


def verify_search(parent,result,meter):
    binding=source_binding(parent,meter);target=parent['cutoff_work_targets'][0]
    require((target['p'],target['m'],target['theta'])==(2,3,'2/3'),'current component mapping')
    rho=number(target['original_low_obligation']['parameters']['alpha'],meter)
    require(type(result['libraries']) is list and len(result['libraries'])==2,'actual/generic comparison')
    for library,profile in zip(result['libraries'],('mobius','bounded')):
        equal((library['profile'],library['rho'],len(library['levels'])),(profile,str(rho),3),meter,'source library scope')
        verify_prefix_library(library,meter)
    old=parent['convolution_argument_search']['geometries']
    equal([(g['alpha'],g['beta']) for g in old],PRIOR.geometry_grid(),meter,
          'complete inherited short-cutoff grammar')
    require(type(result['normalizations']) is list and len(result['normalizations'])==len(old),'all inherited normalizations')
    for g,normalization in zip(old,result['normalizations']):verify_normalization(g,normalization,meter)
    grid=PRIOR.geometry_grid();require(type(result['geometries']) is list and len(result['geometries'])==len(grid),'all complete geometries')
    threshold_count=0
    for g,(a,b) in zip(result['geometries'],grid):
        equal((g['alpha'],g['beta']),(a,b),meter,'declared complete geometry')
        threshold_count+=verify_geometry(g,result['libraries'][0],meter)['thresholds']
    best_geometry=min(range(len(grid)),key=lambda i:cost(result['geometries'][i]['bound'],rho)+(i,))
    routes=[dict(rule='universal_cubic',bound=outer_lift(result['libraries'][0]['levels'][2]['bound'],2,3,'mobius'))]
    routes.extend(dict(rule='complete_geometry',geometry=i,bound=outer_lift(g['bound'],2,3,'mobius'))
                  for i,g in enumerate(result['geometries']))
    best=min(range(len(routes)),key=lambda i:cost(routes[i]['bound'],rho)+(i,));bound=routes[best]['bound']
    comparison=outer_lift(result['libraries'][1]['levels'][2]['bound'],2,3,'bounded')
    equal((result['centered_transfer']['p'],result['centered_transfer']['theta'],result['centered_transfer']['rho'],
           result['centered_transfer']['profile']),
          (2,target['theta'],str(rho),'mobius'),meter,'source transfer parameters')
    transfer=verify_transfer(result['centered_transfer'],meter)
    equal((result['transfer_ablation']['p'],result['transfer_ablation']['theta'],result['transfer_ablation']['rho'],
           result['transfer_ablation']['profile']),
          (2,target['theta'],str(rho),'bounded'),meter,'generic transfer parameters')
    verify_transfer(result['transfer_ablation'],meter)
    actual_powers=[[(row['N_power']) for row in t.get('normalized_error_energy',[])]
                   for t in result['centered_transfer']['trials']]
    generic_powers=[[(row['N_power']) for row in t.get('normalized_error_energy',[])]
                    for t in result['transfer_ablation']['trials']]
    equal(actual_powers,generic_powers,meter,'generic and actual padding have identical powers')
    equal(result['centered_transfer']['selected'],result['transfer_ablation']['selected'],meter,
          'extra generic logarithms do not change strict power payment')
    expected=dict(schema='core-complete-convolution-search-v1',binding=binding,normalizations=result['normalizations'],
        libraries=result['libraries'],geometries=result['geometries'],selected_geometry=best_geometry,full_prefix_routes=routes,
        selected_prefix_route=best,full_source_prefix_bound=bound,generic_comparison=comparison,
        before_outer_K_energy_bound=squared(bound),centered_transfer=result['centered_transfer'],
        transfer_ablation=result['transfer_ablation'],
        frontier=dict(finite_cube='uniform subpower centered energy of A^2*R^3-c^3*D at the selected moving cutoff',
            original_Mellin=copy.deepcopy(target['original_low_obligation']),
            ordinary_moment_test=dict(prefix_X_power=str(max(Q(t['X_power']) for t in bound)),
                sigma=target['sigma'],theta=target['theta'],strict_convergence_proved=False)),
        statistics=dict(normalizations=len(old),complete_geometries=len(grid),complete_thresholds=threshold_count,
            transfer_trials=transfer['trials'],subcritical_transfer_candidates=sum(t.get('subcritical_padding',False)
                for t in result['centered_transfer']['trials']),arithmetic_power_advantage=False,
            actual_source_observations=0,runtime_model_calls=0),
        supplied_rules='CORE_COMPLETE_CONVOLUTION_BOUND_REVIEW_032.txt',full_component_bound_proved=False,
        whole_signed_bound_proved=False,RH_proved=False)
    equal(result,expected,meter,'complete source costs, centered padding and open core')
    return dict(verified=True,complete_geometries=len(grid),transfer_trials=transfer['trials'],full_component_bound_proved=False)


def verify_feedback(parent,result,out,artifact,meter):
    audit=verify_search(parent,result,meter)
    expected=copy.deepcopy(parent)
    expected.update(schema='core-complete-convolution-feedback-v1',status='complete_convolution_search_core_open',
                    parent_obligation_file='candidate10_convolution_argument_obligation.json',complete_search_artifact=artifact)
    expected['complete_convolution_search']=copy.deepcopy(result)
    expected['inherited_complete_convolution_tasks']=copy.deepcopy(parent['next_search_tasks'])
    transfer=result['centered_transfer'];chosen=None if transfer['selected'] is None else transfer['trials'][transfer['selected']]
    expected['next_search_tasks']=[copy.deepcopy(parent['next_search_tasks'][0]),dict(priority=1,
        target_id=result['binding']['target_id'],search_kind='complete_centered_finite_cube',status='open',
        verified_transfer=copy.deepcopy(chosen),exact_source='A^2*(E restricted<=floor(N^beta))^3-c^3*D',
        all_finite_heads_units_and_crosses_required=True,analytic_moment_required=True,
        original_global_Mellin_obligation_retained=True)]+copy.deepcopy(parent['next_search_tasks'][1:])
    equal(out,expected,meter,'full inherited source and finite cube task')
    return audit
