"""Independent moment-region optimum, analytic-source and recovery auditor.

The new producer is never imported. Active supporting constraints reconstruct
the allocation vertices; every licensed reflection/provider choice is priced.
"""
import copy
import itertools
from fractions import Fraction as Q
from math import ceil

from check_core_moment_bound_search import allocation_vertices, _source
import check_core_complete_convolution_search as TRANSFER

require=TRANSFER.require
equal=TRANSFER.equal
number=TRANSFER.number


def rational(value,meter):
    require(type(value) is str and len(value)<=64,'bounded canonical rational string')
    out=number(value,meter)
    require(str(out)==value,'canonical rational string')
    return out


def integer(value,low,high):
    require(type(value) is int and low<=value<=high,'bounded exact integer')
    return value


def library():
    records=[]
    for order,lower,strict in ((2,'1/2',False),(4,'1/2',False),(6,'7/12',True),
                              (8,'5/8',True),(10,'41/60',True),(12,'5/7',True)):
        records.append(dict(id='moment'+str(order),order=str(order),lower=lower,strict=strict,
            height_power='1',epsilon_coefficient='1',upper='1',upper_strict=True,
            status='unconditional_external_theorem',
            source='https://arxiv.org/html/1609.02539v1' if order<=4 else 'https://arxiv.org/pdf/math/0311403',
            reference='fourth moment and Holder; off-line transfer in018' if order<=4
                      else 'equations(1.3)-(1.5), strict domains'))
    return records


def licensed(ids):
    records=library()
    require(type(ids) is list and all(type(i) is str for i in ids) and len(set(ids))==len(ids),
            'unique unconditional provider identifiers')
    require(ids==[r['id'] for r in records if r['id'] in ids],'canonical supplied library subset')
    return [r for r in records if r['id'] in ids]


def provider_available(row,line):
    low=Q(row['lower'])
    return line<1 and (line>low if row['strict'] else line>=low)


def product_optimum(factors,ids,meter,cache=None):
    require(type(factors) is list and 1<=len(factors)<=4,'bounded positive fractional moment product')
    records=licensed(ids);parsed=[]
    for f in factors:
        require(type(f) is dict and set(f)=={'real_part','power'},'complete moment factor schema')
        a,b=rational(f['real_part'],meter),rational(f['power'],meter)
        require(0<a<1 and 0<b<=128,'non-pole strip and positive bounded powers')
        parsed.append((a,b))
    cache={} if cache is None else cache
    key=('product',tuple(parsed),tuple(ids))
    if key in cache:
        meter.charge(20+10*len(parsed))
        return cache[key]
    optimum=None;examined=0
    for reflection in itertools.product((False,True),repeat=len(parsed)):
        effective=[1-a if reflected else a for (a,_),reflected in zip(parsed,reflection)]
        alternatives=[[None]+[r for r in records if provider_available(r,line)] for line in effective]
        for providers in itertools.product(*alternatives):
            orders=[Q(r['order']) if r else Q(0) for r in providers]
            upper=tuple(min(Q(1),b/q) if q else Q(0) for (_,b),q in zip(parsed,orders))
            vk=('vertices',upper)
            if vk not in cache:cache[vk]=allocation_vertices(upper,meter)
            for weights in cache[vk]:
                examined+=1;height=Q(1);eps=Q(0);trace=[]
                for (a,b),line,refl,provider,q,w in zip(parsed,effective,reflection,providers,orders,weights):
                    rem=b-q*w
                    require(rem>=0 and (not w or provider and provider_available(provider,line)),
                            'licensed moment allocation and positive remainder')
                    fe=b*(Q(1,2)-a) if refl else Q(0)
                    pointwise=rem*(1-line)/2
                    height+=fe+pointwise;eps+=rem+w
                    trace.append(dict(original_real_part=str(a),power=str(b),reflected=refl,
                        effective_real_part=str(line),provider_id=provider['id'] if provider else None,
                        moment_order=str(q),holder_weight=str(w),convexity_power=str(rem),
                        reflection_height_power=str(fe),convexity_height_power=str(pointwise)))
                    meter.charge(90)
                trial=dict(factors=trace,holder_unused=str(1-sum(weights,Q(0))),
                           integral_height_power=str(height),epsilon_coefficient=str(eps))
                # Affine primary and secondary objectives each attain minima
                # at active-constraint vertices. First exact tie is retained.
                if optimum is None or (height,eps)<(Q(optimum['integral_height_power']),Q(optimum['epsilon_coefficient'])):
                    optimum=trial
    expected=dict(best=optimum,allocations_examined=examined,
                  completeness='all supplied moment regions, reflections and Holder box-simplex vertices')
    cache[key]=expected
    return expected


def verify_product_bound(factors,ids,result,meter,cache=None):
    expected=product_optimum(factors,ids,meter,cache)
    equal(result,expected,meter,'complete allocation optimum, licensed moment domains and exact costs')
    return dict(verified=True,allocations_examined=expected['allocations_examined'])


def contour_grid(theta,maximum):
    integer(maximum,2,48)
    require(0<theta<1,'fractional kernel pole')
    return sorted({Q(n,d) for d in range(2,maximum+1) for n in range(1,d)
                   if Q(n,d)<min(Q(1,2),theta)})


def verify_candidate(p,m,theta,rho,sigma,ids,result,meter,cache=None):
    integer(p,0,16);integer(m,2,64)
    theta,rho,sigma=map(Q,(theta,rho,sigma))
    require(0<rho<1 and 0<sigma<min(Q(1,2),theta) and theta<1,
            'belowhalf contour, integrable lower tail and growing cutoff')
    factors=[[dict(real_part=str(sigma+1-theta),power='2')],
             [dict(real_part=str(sigma),power=str(2*m)),dict(real_part=str(sigma+1-theta),power='2')]]
    require(type(result) is dict and type(result.get('moment_branches')) is list and len(result['moment_branches'])==2,
            'both finite-power envelope branches and compact head')
    for f,branch in zip(factors,result['moment_branches']):verify_product_bound(f,ids,branch,meter,cache)
    branches=result['moment_branches']
    tails=[Q(b['best']['integral_height_power'])-2 for b in branches]
    slack=max(Q(b['best']['epsilon_coefficient']) for b in branches)
    epsilon=min(Q(1),-max(tails)/(2*(1+slack))) if max(tails)<0 else None
    paid=[h+epsilon*Q(b['best']['epsilon_coefficient']) for h,b in zip(tails,branches)] if epsilon else None
    require(paid is None or max(paid)<0,'strict dyadic convergence after all epsilon and logarithmic costs')
    up=2*(p+m)*(1-sigma);residue=2*(p+m)*(1-theta)
    energy=2*sigma-1+rho*up
    failures=[]
    if epsilon is None:failures.append('global_Mellin_height_tail_not_summable')
    if energy>0:failures.append('finite_factor_cost_exceeds_subpower_target')
    require(residue<=up and 2+2*sigma-2*theta>0,'residue and complete integer-cell correction fit uniform norm')
    expected=dict(sigma=str(sigma),moment_branches=branches,mellin_height_powers=list(map(str,tails)),
        epsilon=str(epsilon) if epsilon else None,paid_height_powers=list(map(str,paid)) if paid else None,
        full_finite_factor_U_power=str(up),residue_squared_U_power=str(residue),
        recovered_energy_N_power=str(energy),target_met=not failures,failed_premises=failures,
        centering=dict(kind='analytic_residue',ordinary_coefficient_moment_required=False,
            ordinary_coefficient_moment_claimed=False,exact_moment='A(theta)^p*E(theta)^m',
            coefficient='K*A^p*E^m-(A(theta)^p*E(theta)^m/theta)*J_theta',
            unit_included=True,whole_x_below_one_tail_included=True,
            pole_at_one_removed_by='c=A(1) in E(s)=1+zeta(s)*(c-A(s))'),
        norm_statement='sum_(n>=1)|complete centered prefix(n)|^2*n^(-2sigma-1)<=C_norm*U^b',
        integer_cell_correction=dict(integral_multiplier='8',residue_multiplier='32',
            residue_denominator=str(2+2*sigma-2*theta)),
        constants_uniform_in=['U','N','X'],constants_may_depend_on=['p','m','theta','sigma','epsilon'],
        generic_bounded_weights_same_U_power=True)
    equal(result,expected,meter,'complete analytic centering, uniform constants, height and energy budgets')
    return dict(verified=True,target_met=not failures)


def optimistic_diagnostic(p,m,rho):
    r=Q(rho)*(p+m)
    floor=(-1+r*(m+1))/m if r<Q(1,2) else min(2*r-1,r)
    return dict(assumption='hypothetically grant all moments O(T^(1+epsilon)) on every fixed line >=1/2',
        reflected_tail_requires_sigma_above=str(Q(m-1,2*m)),optimistic_energy_infimum=str(floor),
        cutoff_alone_obstructs=r>=Q(1,2),stronger_moment_library_alone_insufficient=floor>=0,
        scope='only the full finite absolute-mass envelope in this belowhalf contour grammar',
        arithmetic_impossibility_claimed=False,
        next_mechanism='signed finite-factor or joint-correlation control; preserve source cross terms')


def verify_targets(parent,join,targets,spec,meter):
    rho=rational(parent['selected_source_representation']['alpha'],meter)
    eligible=[t for t in join['collected_terms'] if t['powers'][2]==1 and t['powers'][3]>=2 and
              all(t['powers'][i]==0 for i in (1,4,5,6,7))]
    old=parent['auxiliary_bound_targets']
    require(type(old) is list and type(targets) is list and len(old)==len(targets)==len(eligible),
            'all pure residual AST targets present exactly once')
    require(len({t['target_id'] for t in old})==len(old),'unique inherited target identifiers')
    inherited_paid=parent['complete_source_reduction']['new_paid_components']
    require(type(inherited_paid) is list and len({t['target_id'] for t in inherited_paid})==len(inherited_paid),
            'unique inherited published paid components')
    paid_lookup={t['target_id']:t['source_term'] for t in inherited_paid}
    require(set(paid_lookup)<=set(t['target_id'] for t in old),'known inherited payments')
    cache={}
    for inherited,term,t in zip(old,eligible,targets):
        p=integer(inherited['p'],0,16);m=integer(inherited['m'],2,64)
        require(inherited['theta']=='2/3' and (p,m)==(term['powers'][0],term['powers'][3]),
                'actual K shift1/3 and pure source powers')
        require(type(inherited['component_bound_proved']) is bool,'inherited proof status')
        equal(inherited['source_term'],term,meter,'actual complete signed source coefficient')
        require(inherited['target_id']=='centered_A'+str(p)+'_E'+str(m),'source-derived target identifier')
        require(inherited['component_bound_proved']==(inherited['target_id'] in paid_lookup),
                'inherited proof status cannot suppress or duplicate source payments')
        if inherited['component_bound_proved']:
            equal(paid_lookup[inherited['target_id']],term,meter,'published inherited payment bound to source')
        grid=contour_grid(Q(2,3),spec['sigma_denominator_max'])
        require(type(t['trials']) is list and len(t['trials'])==len(grid),'complete rational contour grammar')
        for sigma,c in zip(grid,t['trials']):
            verify_candidate(p,m,Q(2,3),rho,sigma,spec['library_ids'],c,meter,cache)
        feasible=[i for i,c in enumerate(t['trials']) if c['target_met']]
        best=min(feasible,key=lambda i:(Q(t['trials'][i]['recovered_energy_N_power']),
            max(map(Q,t['trials'][i]['paid_height_powers'])),i)) if feasible else None
        expected=dict(target_id=inherited['target_id'],p=p,m=m,theta='2/3',source_term=term,
            inherited_component_paid=inherited['component_bound_proved'],trials=t['trials'],selected=best,
            analytic_centered_bound_proved=best is not None,
            new_source_payment=best is not None and not inherited['component_bound_proved'],
            optimistic_moment_diagnostic=optimistic_diagnostic(p,m,rho),
            constant='C_region_'+inherited['target_id'] if best is not None else None)
        equal(t,expected,meter,'optimal contour, analytic payment and proof-language obstruction')


def channel_constant(channels,sigma,meter):
    require(type(channels) is list and bool(channels),'complete nonempty channel vector')
    total=Q(0)
    for ch in channels:
        eta=rational(ch['eta'],meter);require(eta>=0,'nonnegative inherited logarithmic normalization')
        coeff=ch['polynomial'];require(type(coeff) is list and bool(coeff),'full channel polynomial including unit')
        coeff=[rational(c,meter) for c in coeff]
        endpoint=sum(map(abs,coeff),Q(0));derivative=sum((j*abs(c) for j,c in enumerate(coeff)),Q(0))
        total+=(Q(2)**ceil(eta)*(endpoint+2*(1+1/sigma)*derivative))**2
        meter.charge(100+50*len(coeff))
    return total


def original_transport(binding):
    visited=set()
    while 'transport_program' not in binding:
        require(type(binding) is dict and id(binding) not in visited and len(visited)<64,
                'finite noncyclic original transport ancestry')
        visited.add(id(binding));binding=binding['inherited_binding']
    return binding['transport_program']


def verify_reduction(parent,context,targets,result,meter):
    old=parent['generated_bound_obligations'];programs=context['channel_programs']
    require(type(old) is list and len(old)==144 and len({b['parent_obligation_id'] for b in old})==144,
            'every distinct original144 recovery binding')
    require(type(programs) is list and len(programs)==144 and len({p['id'] for p in programs})==144,
            'all distinct original channel constructions')
    lookup={p['id']:p for p in programs}
    require(set(lookup)=={b['parent_obligation_id'] for b in old},'exact original program membership')
    rho=Q(parent['selected_source_representation']['alpha'])
    paid=[t for t in targets if t['new_source_payment']];bindings=[]
    for index,b in enumerate(old):
        require(b['recovery']=='S_g<=4*S_Z+4*C_new+2*C_old; S_Z<=4*S_g+4*C_old+2*C_new',
                'licensed inherited forward and reverse recovery')
        require(rational(b['sufficient_goal']['p'],meter)>=0,'constant payments fit the inherited residual log budget')
        program=lookup[b['parent_obligation_id']]
        equal(original_transport(b),program['transport_program'],meter,'same original transport')
        costs=[]
        for t in paid:
            c=t['trials'][t['selected']];sigma=Q(c['sigma']);up=Q(c['full_finite_factor_U_power'])
            require(Q(c['recovered_energy_N_power'])<=0,'uniform paid constant from nonpositive energy power')
            cc=channel_constant(program['construction']['channels'],sigma,meter)
            local=Q(2)**ceil(2*sigma+1+2*rho*up)
            scalar=rational(t['source_term']['coefficient'],meter)
            costs.append(dict(target_id=t['target_id'],constant=t['constant'],channel_squared_constant=str(cc),
                local_cutoff_constant=str(local),rational_multiplier=str(len(paid)*scalar*scalar*cc*local),
                energy_X_power=c['recovered_energy_N_power']))
        bindings.append(dict(parent_obligation_id=b['parent_obligation_id'],inherited_binding_index=index,
            paid_constant_terms=costs,residual_goal=dict(b['sufficient_goal'],
                expression='S_Z033(X), complete signed residual after all listed payments',status='open'),
            forward='S_g<=8*S_Z033+8*C_033+4*C_prev+2*C_old',
            reverse='S_Z033<=8*S_g+8*C_old+4*C_prev+2*C_033',whole_signed_bound_proved=False,RH_proved=False))
    expected=dict(exact_identity='g=P_old+P_033+Z033; Z033=Z_previous-P_033',
        paid_components=[dict(target_id=t['target_id'],source_term=t['source_term'],
            centered_component='source_coefficient*(K*A^p*E^m-M_analytic*J_theta/theta)',
            retained_opposite_drift='source_coefficient*M_analytic*J_theta/theta',ordinary_coefficient_moment_claimed=False)
            for t in paid],bindings=bindings,complete_source_retained=True,all_cross_terms_retained=True,
        transport_error_retained='-e',common_horizon='N=4X-1 for BOTH blocks; same U',
        new_residual_expression='Z_previous minus only the listed analytic-centered paid components',
        whole_signed_bound_proved=False,RH_proved=False)
    equal(result,expected,meter,'all channel squares, exact source/drift and correctly composed recovery')


def verify_cube(parent,targets,result,meter):
    old=parent['cutoff_work_targets'][0]
    require((old['p'],old['m'],old['theta'])==(2,3,'2/3'),'actual complete cube adapter')
    matches=[t for t in targets if t['target_id']==old['target_id']]
    require(len(matches)==1,'current cube belongs to independently bound original targets')
    t=matches[0];rho=rational(parent['selected_source_representation']['alpha'],meter)
    require(rho==Q(1,24),'declared current complete cube cutoff domain')
    saved=parent['complete_convolution_search']['centered_transfer']
    require((saved['p'],saved['theta'],saved['rho'],saved['profile'])==(2,'2/3','1/24','mobius'),
            'same actual inherited tail transfer')
    TRANSFER.verify_transfer(saved,meter)
    chosen=saved['trials'][saved['selected']] if saved['selected'] is not None else None
    head=old['head_bound']
    require((head['atom'],head['convolution_power'],head['c_power'],head['centered_prefix_U_power'],
             head['centered_prefix_constant'])==('One',1,3,'1','12'),'complete finite centered-K head bound')
    equal(old['source_term'],t['source_term'],meter,'unchanged original cube coefficient')
    component=[];finite=[]
    if t['selected'] is not None:
        selected=t['trials'][t['selected']]
        component=[dict(constant=t['constant'],multiplier='2',N_power=selected['recovered_energy_N_power'],log_degree=0),
                   dict(constant='1',multiplier='288',N_power=str(2*rho-1),log_degree=0)]
        if chosen is not None:
            finite=[dict(r,multiplier=str(2*Q(r['multiplier']))) for r in component]
            finite.extend(dict(constant='1',multiplier=str(2*Q(r['constant'])),N_power=r['N_power'],
                               log_degree=r['log_degree']) for r in chosen['normalized_error_energy'])
    require(all(Q(r['N_power'])<=0 for r in component) and
            all(Q(r['N_power'])<0 for r in finite[2:]),'paid head and inherited strict padding')
    expected=dict(target_id=t['target_id'],full_source='F=A^2*E^3-c^3*One_[1,U]',
        finite_source='F_R=A^2*(E restricted<=floor(N^beta))^3-c^3*One_[1,U]',
        analytic_full_moment='A(theta)^2*E(theta)^3-c^3*D(theta)',
        same_head_and_full_moment_defect_retained=True,selected_transfer=copy.deepcopy(chosen),
        full_component_energy_terms=component,finite_cube_energy_terms=finite,
        complete_component_bound_proved=bool(component),finite_cube_bound_proved=bool(finite),
        original_fixed_sigma_low_Gram_proved=False,full_core_bound_proved=False,
        energy='N^-2*sum_(1<=n<=N)|complete centered prefix(n)|^2',
        domain='integer U,N>=1, U<=N^(1/24); same N and r over whole prefix',
        ordinary_cubic_coefficient_moment_claimed=False)
    equal(result,expected,meter,'whole component and finite cube retain head, defect, cross and moment scopes')


def graph(targets,cube):
    nodes=[dict(id='supplied_moments',dependencies=[],proved=True),
           dict(id='analytic_residue_bridge',dependencies=[],proved=True),
           dict(id='inherited_head_and_transfer',dependencies=[],proved=True)]
    nodes.extend(dict(id='norm:'+t['target_id'],dependencies=['supplied_moments','analytic_residue_bridge'],
                      proved=t['analytic_centered_bound_proved']) for t in targets)
    nodes.extend([dict(id='source_reduction',dependencies=['norm:'+t['target_id'] for t in targets if t['new_source_payment']],proved=True),
        dict(id='finite_cube',dependencies=['norm:'+cube['target_id'],'inherited_head_and_transfer'],proved=cube['finite_cube_bound_proved']),
        dict(id='remaining_joint_residual',dependencies=[],proved=False),
        dict(id='full_signed_core',dependencies=['source_reduction','remaining_joint_residual'],proved=False)])
    return nodes


def verify_graph(nodes,targets,cube,meter):
    require(type(nodes) is list and all(type(n) is dict and set(n)=={'id','dependencies','proved'} for n in nodes),
            'typed proof graph')
    require(all(type(n['id']) is str and type(n['dependencies']) is list and type(n['proved']) is bool for n in nodes),
            'explicit boolean statuses and dependencies')
    lookup={n['id']:n for n in nodes};require(len(lookup)==len(nodes),'unique proof nodes')
    finished=set();active=set()
    def visit(ident):
        require(type(ident) is str and ident in lookup and ident not in active,'known acyclic dependencies')
        if ident in finished:return
        active.add(ident);node=lookup[ident]
        require(len(set(node['dependencies']))==len(node['dependencies']),'unique dependency edges')
        for dep in node['dependencies']:
            visit(dep);require(not node['proved'] or lookup[dep]['proved'],'paid proof cannot depend on an open premise')
            meter.charge(30)
        active.remove(ident);finished.add(ident)
    for ident in lookup:visit(ident)
    equal(nodes,graph(targets,cube),meter,'norm independent of cube and explicit unpaid full complement')


def ablation():
    return dict(weights='arbitrary complex |a_n|<=1, c=sum_(n<=U)a_n/n',
        finite_A_bound='U^(1-sigma)/(1-sigma)',finite_c_minus_A_bound='2*U^(1-sigma)/(1-sigma)',
        identical_moment_trials=True,identical_U_powers=True,additional_logU_loss=0,arithmetic_power_advantage=False,
        generic_centers_are_their_own_analytic_residues=True,generic_finite_cube_composition_claimed=False)


def verify_search(parent,context,result,meter):
    require(type(parent) is dict and parent.get('schema')=='core-complete-convolution-feedback-v1',
            'current accepted complete convolution source')
    require(parent.get('whole_signed_bound_proved') is False and parent.get('RH_proved') is False,'original signed core open')
    require(type(context) is dict and set(context)=={'complete_signed_join','channel_programs'},'original independent source/channel context')
    join=_source(parent,meter)
    equal(context['complete_signed_join'],join,meter,'independent original inverse and all centering expansions')
    equal(parent['complete_source_reduction']['inherited_complete_signed_join'],join,meter,'unchanged saved original join')
    require(type(result) is dict and result.get('schema')=='core-moment-region-search-v1','moment region result schema')
    spec=result['spec']
    require(type(spec) is dict and set(spec)=={'sigma_denominator_max','library_ids','target_energy_power'},'bounded declared search grammar')
    integer(spec['sigma_denominator_max'],2,48);licensed(spec['library_ids'])
    require(spec['target_energy_power']=='0','implemented constant-energy source recovery')
    equal(result['library'],library(),meter,'unconditional providers with strict high-order gates')
    rho=rational(parent['selected_source_representation']['alpha'],meter)
    require(0<rho<1,'actual growing cutoff')
    verify_targets(parent,join,result['targets'],spec,meter)
    verify_reduction(parent,context,result['targets'],result['source_reduction'],meter)
    verify_cube(parent,result['targets'],result['cube_composition'],meter)
    verify_graph(result['proof_dependencies'],result['targets'],result['cube_composition'],meter)
    trials=[c for t in result['targets'] for c in t['trials']]
    expected=dict(schema='core-moment-region-search-v1',spec=spec,library=library(),
        supplied_rules=['CORE_MOMENT_REGION_REVIEW_033.txt','CORE_MOMENT_REGION_CHECK_033.txt'],rho=str(rho),
        targets=result['targets'],source_reduction=result['source_reduction'],cube_composition=result['cube_composition'],
        ablation=ablation(),proof_dependencies=result['proof_dependencies'],
        statistics=dict(targets=len(result['targets']),contour_trials=len(trials),
            moment_allocations=sum(b['allocations_examined'] for c in trials for b in c['moment_branches']),
            paid_analytic_components=sum(t['analytic_centered_bound_proved'] for t in result['targets']),
            new_source_payments=sum(t['new_source_payment'] for t in result['targets']),original_bindings=144,
            actual_source_observations=0,runtime_model_calls=0,fitted_constants=0),
        formal_proof_assistant_verified=False,whole_signed_bound_proved=False,RH_proved=False)
    equal(result,expected,meter,'full moment-region payments, structural ablation and open original source')
    return dict(verified=True,targets=len(result['targets']),
                new_source_payments=expected['statistics']['new_source_payments'],original_bindings=144,
                finite_cube_bound_proved=result['cube_composition']['finite_cube_bound_proved'],whole_signed_bound_proved=False,RH_proved=False)


def verify_feedback(parent,result,out,artifact,meter):
    """Publication preservation; caller first audits verify_search with context."""
    require(type(artifact) is str and bool(artifact),'immutable proof artifact reference')
    require(result['whole_signed_bound_proved'] is False and result['RH_proved'] is False,'no full core publication claim')
    expected=copy.deepcopy(parent)
    expected.update(schema='core-moment-region-feedback-v1',status='moment_regions_verified_core_open',
        parent_obligation_file='candidate10_complete_convolution_obligation.json',moment_region_artifact=artifact,
        moment_region_search=copy.deepcopy(result),new_component_bounds_proved=result['statistics']['new_source_payments'])
    expected['inherited_moment_region_tasks']=copy.deepcopy(parent['next_search_tasks'])
    tasks=[dict(parent['next_search_tasks'][0],residual_reference='moment_region_search.source_reduction',
        next_action='search joint control of the complete residual Z033, including all opposite analytic drifts')]
    for t in result['targets']:
        if t['analytic_centered_bound_proved']:continue
        impossible=t['optimistic_moment_diagnostic']['stronger_moment_library_alone_insufficient']
        tasks.append(dict(priority=1,search_kind='unpaid_analytic_centered_component',target_id=t['target_id'],
            p=t['p'],m=t['m'],theta=t['theta'],status='open',moment_library_alone_insufficient=impossible,
            requirement='signed finite-factor/correlation control with complete source recovery' if impossible
            else 'new moment or signed finite-factor/correlation control with complete source recovery'))
    tasks.extend([dict(priority=1,search_kind='joint_opposite_analytic_drift_control',status='open',
        paid_components=[t['target_id'] for t in result['targets'] if t['new_source_payment']],
        requirement='retain and bound drift jointly with the remaining original source, not separately erase it'),
        dict(priority=2,search_kind='original_fixed_sigma_Mellin_target',status='open',
        target_id=parent['cutoff_work_targets'][0]['target_id'],
        requirement='alternate physical component proof does not pay the old fixed-line U^(12/5) Gram claim')])
    expected['next_search_tasks']=tasks
    equal(out,expected,meter,'full inherited source, bindings, head, drifts and open priority retained')
    return dict(verified=True,new_source_payments=result['statistics']['new_source_payments'],whole_signed_bound_proved=False,RH_proved=False)
