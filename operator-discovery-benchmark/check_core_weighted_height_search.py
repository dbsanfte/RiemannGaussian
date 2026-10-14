"""Independent exact applications of reviewed weighted moment rules.

No new producer is imported. The common-height optimizer is audited as an
exact one-variable linear program, including all length and decay premises.
"""
from fractions import Fraction as Q
from math import ceil, comb

from check_core_split_bound_search import _require, _same, _rational
from check_core_bound_goal_search import _source
from check_core_moment_bound_search import _audit_graph


def _integer(v,lo,hi):
    _require(type(v) is int and lo<=v<=hi,'bounded exact integer grammar')
    return v


def _grid(bound,maximum):
    return sorted({Q(n,d) for d in range(2,maximum+1) for n in range(1,d) if Q(n,d)<bound})


def _spec(spec,meter):
    _require(type(spec) is dict and set(spec)=={'sigma_denominator_max','kappa_denominator_max',
        'epsilon_fractions','maximum_tau','dilation_max','amplitude_max'},'complete declared weighted language')
    for key,lo,hi in [('sigma_denominator_max',3,32),('kappa_denominator_max',5,24),
                     ('dilation_max',2,12),('amplitude_max',1,16)]:_integer(spec[key],lo,hi)
    _require(0<_rational(spec['maximum_tau'],meter)<=1024,'bounded common height exponent')
    fs=spec['epsilon_fractions']
    _require(type(fs) is list and 1<=len(fs)<=8 and len(set(fs))==len(fs) and
        all(0<_rational(f,meter)<1 for f in fs),'distinct strictly positive saving fractions')


def _branches(p,m,theta,sigma,meter):
    _integer(p,0,16);_integer(m,2,64)
    _require(0<theta<1 and 0<sigma<min(Q(1,2),theta),'nonpole belowhalf Mellin contour')
    u=1-theta;rows=[]
    for j in range(m+1):
        # Time integration contributes 1, shifted convexity contributes
        # 1-sigma-u, and Perron contributes -2. Reflection contributes
        # 2j*(1/2-sigma); abovehalf excess convexity contributes (j-2)sigma.
        height=1+(1-sigma-u)-2
        if j:height+=2*j*(Q(1,2)-sigma)
        if j>=2:height+=(j-2)*sigma
        r=p+j
        rows.append(dict(j=j,r=r,support_U_power=r,coefficient_envelope=dict(multiplier=str(3**j),
            divisor_order=r,constant_polynomial=r==0),height_power=str(height),
            weight_U_power=str(2*r*(Q(1,2)-sigma))))
        meter.charge(100)
    return rows


def verify_line(p,m,theta,alpha,sigma,spec,line,meter):
    """Check every plan and prove its tau is the smallest feasible one."""
    _spec(spec,meter);_require(0<alpha<1,'strict arithmetic short cutoff')
    bs=_branches(p,m,theta,sigma,meter);saving=min(-Q(b['height_power']) for b in bs)
    failures=[];plans=[]
    if saving<=0:failures.append('at_least_one_complete_branch_has_no_strict_height_saving')
    else:
        for kappa in _grid(Q(1,4),spec['kappa_denominator_max']):
            _require(0<kappa<Q(1,4),'strict twisted fourth polynomial length range')
            for fraction in spec['epsilon_fractions']:
                epsilon=_rational(fraction,meter)*saving
                # Constraints a*tau>=b. All a>0, hence the feasible ray
                # starts at max(b/a); at least one active constraint proves
                # every smaller tau infeasible, not just absent from a grid.
                constraints=[(kappa,Q(b['r'])) for b in bs]
                constraints += [(-Q(b['height_power'])-epsilon,Q(b['weight_U_power'])) for b in bs]
                _require(all(a>0 for a,_ in constraints),'strict full height saving after epsilon')
                tau=max(b/a for a,b in constraints)
                _require(all(a*tau>=b for a,b in constraints) and any(a*tau==b for a,b in constraints),
                    'minimum common tau certified by active affine constraint')
                pb=[]
                for b in bs:
                    length=tau*kappa-b['r'];tail=Q(b['height_power'])+epsilon
                    power=Q(b['weight_U_power'])+tau*tail
                    _require(length>=0 and tail<0 and power<=0,'every branch satisfies common length and tail premises')
                    pb.append(dict(j=b['j'],length_slack=str(length),tail_height_power=str(tail),tail_U_power=str(power)))
                    meter.charge(100)
                low=2*(p+m)*(1-sigma);error=2*(p+m)*(1-theta)
                energy=2*sigma-1+alpha*low;ee=-1+alpha*error;cap=tau<=Q(spec['maximum_tau'])
                plans.append(dict(kappa=str(kappa),epsilon_fraction=fraction,epsilon=str(epsilon),tau=str(tau),
                    branches=pb,within_tau_cap=cap,high_U_power=str(max(Q(b['tail_U_power']) for b in pb)),
                    high_energy_X_power=str(2*sigma-1),required_low_U_power=str((1-2*sigma)/alpha),
                    generic_low_U_power=str(low),generic_low_energy_X_power=str(energy),integer_error_U_power=str(error),
                    integer_error_X_power=str(ee),high_auxiliary_proved=cap,
                    generic_complete_component_proved=cap and energy<=0 and ee<=0,
                    low_obligation_status='proved_by_generic_fallback' if energy<=0 else 'open_actual_Mobius_bound'))
        if not any(p['within_tau_cap'] for p in plans):failures.append('every_valid_common_height_exceeds_declared_tau_cap')
    eligible=[i for i,p in enumerate(plans) if p['high_auxiliary_proved']]
    selected=min(eligible,key=lambda i:(Q(plans[i]['tau']),-Q(plans[i]['epsilon']),-Q(plans[i]['kappa']),i)) if eligible else None
    expected=dict(sigma=str(sigma),branches=bs,plans=plans,selected_plan=selected,failed_premises=failures)
    _require(_same(line,expected),'complete j0/j1/higher branches, common height optimization, costs and plan ranking')
    return dict(verified=True,selected_plan=selected)


def _witnesses(spec,meter):
    """Independent nullspace audit, without enumerating the producer pairs.

    d*x+y=0 has primitive positive-first integer direction (1,-d).
    It occurs in [-A,A]^2 iff d<=A. Infinity normalization gives (1/d,-1).
    Thus this lists exactly every normalized nonzero direction in the cube.
    """
    accepted=[]
    for d in range(2,min(spec['dilation_max'],spec['amplitude_max'])+1):
        x,y=Q(1,d),Q(-1)
        _require(x+y/d==0 and abs(x)<=1 and abs(y)<=1 and d>=2,'unit, disjoint dilation and exact harmonic nullness')
        accepted.append(dict(dilation=d,x=str(x),y=str(y),harmonic_tail='0',c='1',unit='1',
            seed_interval='Q<n<=2Q',image_interval='n -> dilation*n',horizon='U=2*dilation*Q',
            quantifier='every integer Q>=2',tail_factor=dict(constant=str(x),dilation_coefficient=str(y),dilation=d),
            uniform_magnitude_gap='abs(y)*dilation^(-sigma)-abs(x)>0 for 0<sigma<1',
            lower_U_power='2*(p+m)*(1-sigma)',
            proof='paired harmonic identity, rotated seed sum, zeta nonzero on real (0,1), fixed-window continuity',
            status='proved_generic_class_obstruction',applies_to_actual_Mobius=False,applies_to_prescribed_X_block=False,
            applies_to_arbitrary_projected_channel=False,applies_to_full_signed_core=False))
        meter.charge(150)
    return dict(integer_pairs_examined=(spec['dilation_max']-1)*(2*spec['amplitude_max']+1)**2,witnesses=accepted,
        scope='generic bounded finite weights with harmonic cancellation',ordinary_moment_convergence_not_assumed=True)


def _low(p,m,theta,sigma,alpha,plan):
    return dict(kind='complete_zeta_weighted_low_Mellin_Gram',
        parameters=dict(p=p,m=m,theta=str(theta),sigma=str(sigma),alpha=str(alpha)),
        source_weights=dict(A='mu(n)*1_(n<=U)',c='sum_(n<=U)mu(n)/n',T='c*delta-A',E='delta+One*T',B_j='A^p*T^j'),
        height=dict(prefactor='2',U_power=plan['tau'],interval='abs(t)<H'),measure='dt/(2*pi)',
        kernel='abs(zeta(s+1-theta)/s)^2*zeta(s)^j*conj(zeta(s)^k)',
        finite_polynomial_product='B_j(s)*conj(B_k(s))',
        matrix_entries=[dict(j=j,k=k,contraction=str(comb(m,j)*comb(m,k))) for j in range(m+1) for k in range(m+1)],
        integer_pairs='all ordered d,e, with actual signed B_j(d)*B_k(e)',
        unweighted_Gaussian_substitution_allowed=False,diagonal_only_allowed=False,
        required_upper=dict(constant='C_low',U_power=plan['required_low_U_power'],log_degree=0,
            quantifier='every integer U>=1, one fixed finite C_low independent of U,X,N'),
        status=plan['low_obligation_status'],generic_fallback_U_power=plan['generic_low_U_power'],complete_cross_terms_retained=True)


def _channels(channels,sigma,theta,meter):
    _require(type(channels) is list and bool(channels),'complete original channel vector')
    h=e=Q(0)
    for channel in channels:
        eta=_rational(channel['eta'],meter);_require(eta>=0,'nonnegative channel log normalization')
        cs=channel['polynomial'];_require(type(cs) is list and bool(cs),'full channel coefficient list including unit')
        cs=[_rational(c,meter) for c in cs];p0=sum(map(abs,cs),Q(0));p1=sum((i*abs(c) for i,c in enumerate(cs)),Q(0))
        h+=(2**ceil(eta)*(p0+2*(1+1/sigma)*p1))**2
        e+=(2**ceil(eta)*(p0+2*(1+1/(1-theta))*p1))**2;meter.charge(100)
    return h,e


def _context(parent,context,meter):
    _require(type(context) is dict and set(context)=={'complete_signed_join','channel_programs'},'full source/channel context')
    join=_source(parent,meter);_require(_same(join,context['complete_signed_join']),'independent full inverse and signed source replay')
    reduction=parent['complete_source_reduction']
    _require(_same(reduction['inherited_complete_signed_join'],join) and
        _same(reduction['bindings'],parent['generated_bound_obligations']),'unchanged inherited complete source and all recoveries')
    _require(reduction['transport_error_retained']=='-e' and reduction['whole_join_cross_terms_retained'] is True and
        reduction['common_horizon']=='N=4X-1 for BOTH blocks; same coefficients and cutoffs','full transport, same cutoffs and signed histories')
    paid=[t for t in parent['auxiliary_bound_targets'] if t['component_bound_proved'] is True]
    expected_paid=[dict(target_id=t['target_id'],source_term=t['source_term'],
        centered_component='source_coefficient*(K*A^p*E^m - M/theta*J_theta)',
        retained_opposite_drift='source_coefficient*M/theta*J_theta',ordinary_moment_proved=True) for t in paid]
    _require(_same(reduction['new_paid_components'],expected_paid),
        'inherited payment flags agree with retained complete centered pieces and opposite drifts')
    programs=context['channel_programs'];bindings=parent['generated_bound_obligations']
    _require(type(programs) is list and type(bindings) is list and len({p['id'] for p in programs})==len(programs) and
        len({b['parent_obligation_id'] for b in bindings})==len(bindings),'unique authoritative channel and binding ids')
    lookup={p['id']:p for p in programs}
    _require(set(lookup)=={b['parent_obligation_id'] for b in bindings},'every original channel route retained')
    for binding in bindings:
        node=binding;seen=set()
        while 'transport_program' not in node:
            _require(id(node) not in seen and type(node.get('inherited_binding')) is dict,'uncyclic inherited transport ancestry')
            seen.add(id(node));node=node['inherited_binding'];meter.charge(30)
        _require(_same(node['transport_program'],lookup[binding['parent_obligation_id']]['transport_program']),
            'original transport preserved under nested recoveries')
        _require(binding.get('whole_signed_bound_proved') is False and binding.get('RH_proved') is False,
            'inherited original core stays open')
    return join,lookup


def _bindings(parent,lookup,target,line,plan,meter):
    sigma=Q(line['sigma']);theta=Q(target['theta']);alpha=Q(parent['selected_source_representation']['alpha'])
    scalar=Q(target['source_term']['coefficient'])**2;b=Q(plan['required_low_U_power']);err=Q(plan['integer_error_U_power'])
    rows=[]
    for old in parent['generated_bound_obligations']:
        h,e=_channels(lookup[old['parent_obligation_id']]['construction']['channels'],sigma,theta,meter)
        rows.append(dict(parent_obligation_id=old['parent_obligation_id'],source_coefficient_squared=str(scalar),
            channel_Hardy_constant=str(h),channel_error_constant=str(e),
            low_constant_multiplier=str(scalar*64*h*Q(4)**ceil(alpha*b)),high_constant_multiplier=str(scalar*64*h),
            error_constant_multiplier=str(scalar*4*e*Q(4)**ceil(alpha*err)),low_energy_X_power='0',
            high_energy_X_power=plan['high_energy_X_power'],error_energy_X_power=plan['integer_error_X_power'],
            constant_symbols=['C_low','C_high','C_residue_squared'],numerical_value=None,
            status='conditional_on_complete_low_Gram_bound',complete_history=True,parent_and_child_common_horizon='N=4X-1'))
    return rows


def _targets(parent,join,lookup,targets,spec,meter):
    eligible=[t for t in join['collected_terms'] if t['powers'][2]==1 and t['powers'][3]>=2 and
        all(t['powers'][i]==0 for i in (1,4,5,6,7))]
    inherited=parent['auxiliary_bound_targets']
    _require(type(inherited) is list and type(targets) is list and len(inherited)==len(eligible)==len(targets),
        'complete source target membership without omission')
    alpha=_rational(parent['selected_source_representation']['alpha'],meter)
    for old,term,target in zip(inherited,eligible,targets):
        p=_integer(old['p'],0,16);m=_integer(old['m'],2,64);theta=_rational(old['theta'],meter)
        _require(theta==Q(2,3) and p==term['powers'][0] and m==term['powers'][3] and _same(old['source_term'],term) and
            old['target_id']=='centered_A'+str(p)+'_E'+str(m) and type(old['component_bound_proved']) is bool,
            'actual source kernel, full scalar, inverse power and inherited target identity')
        grid=_grid(min(Q(1,2),theta),spec['sigma_denominator_max']);lines=target['lines']
        _require(type(lines) is list and len(lines)==len(grid),'all declared contour lines including rejections')
        for sigma,line in zip(grid,lines):verify_line(p,m,theta,alpha,sigma,spec,line,meter)
        feasible=[i for i,l in enumerate(lines) if l['selected_plan'] is not None]
        def rank(i):
            plan=lines[i]['plans'][lines[i]['selected_plan']]
            return (-Q(plan['required_low_U_power']),Q(plan['tau']),i)
        selected=min(feasible,key=rank) if feasible else None
        low=None;bindings=[]
        if selected is not None:
            line=lines[selected];plan=line['plans'][line['selected_plan']]
            low=_low(p,m,theta,Q(line['sigma']),alpha,plan);bindings=_bindings(parent,lookup,old,line,plan,meter)
        expected=dict(target_id=old['target_id'],p=p,m=m,theta=str(theta),source_term=term,
            inherited_component_bound_proved=old['component_bound_proved'],lines=lines,selected_line=selected,
            high_auxiliary_proved=selected is not None,new_source_payment=False,low_obligation=low,
            conditional_recovery_bindings=bindings,
            centering=dict(kind='analytic_residue',M='A(theta)^p*E(theta)^m',
                centered_coefficient='K*A^p*E^m-(M/theta)*J_theta',retained_opposite_drift='source_coefficient*(M/theta)*J_theta',
                ordinary_moment_established_by_inherited_prefix_rule=Q(m-1,m)<theta,ordinary_prefix_power=str(Q(m-1,m)),
                ordinary_convergence_required_for_this_route=False,unit_J_theta_1='1',
                continuous_small_x_tail='-(M/theta)*x^theta on 0<x<1',pole_at_1_removed_in_complete_E=True),
            source_head_identity=dict(domain='every integer 1<=n<=U',expression='(A^p*E^m)(n)',scalar='c^m',
                coefficient=dict(atom='One' if m>=p else 'mu',convolution_power=abs(m-p)),zero_power='delta',
                derivation='mu*One=delta on n<=U and E(n)=c',supplies_full_Gram_bound=False))
        _require(_same(target,expected),'analytic versus ordinary centering, complete low Gram, conditional recovery and exact source head')


def _graph(targets,witnesses):
    found=bool(witnesses['witnesses'])
    nodes=[dict(id='reviewed_weighted_rules',status='reviewed_and_imported',depends_on=[]),
        dict(id='inherited_verified_frontier',status='reviewed_and_imported',depends_on=[]),
        dict(id='generic_weight_class_obstruction',status='proved' if found else 'open',
            depends_on=['reviewed_weighted_rules'])]
    for t in targets:
        ident=t['target_id']
        if t['selected_line'] is None:
            nodes.append(dict(id='route_'+ident,status='open',depends_on=[]));continue
        line=t['lines'][t['selected_line']];plan=line['plans'][line['selected_plan']]
        nodes.extend([dict(id='high_'+ident,status='proved',depends_on=['reviewed_weighted_rules']),
            dict(id='low_'+ident,status='proved' if t['low_obligation']['status']=='proved_by_generic_fallback' else 'open',depends_on=['reviewed_weighted_rules']),
            dict(id='integer_'+ident,status='proved' if Q(plan['integer_error_X_power'])<=0 else 'open',depends_on=['reviewed_weighted_rules']),
            dict(id='route_'+ident,status='proved' if plan['generic_complete_component_proved'] else 'conditional',
                depends_on=['high_'+ident,'low_'+ident,'integer_'+ident])])
    nodes.extend([dict(id='complete_signed_complement',status='open',depends_on=['inherited_verified_frontier']),
        dict(id='actual_signed_core',status='open',depends_on=['route_'+t['target_id'] for t in targets]+['complete_signed_complement']),
        dict(id='original_RH_recovery',status='conditional',depends_on=['actual_signed_core'])])
    return nodes


def _tasks(targets):
    rows=[dict(target_id='actual_signed_core',priority=0,status='open',search_kind='joint_signed_core_control',
        preserve='complete inherited residual Z, every source cross, drift, unit, -e and recovery',componentwise_routes_are_optional=True)]
    for t in targets:
        if t['inherited_component_bound_proved']:continue
        rows.append(dict(target_id=t['target_id'],priority=1,status='open',
            search_kind='bound_actual_signed_low_Gram' if t['low_obligation'] else 'discover_joint_weighted_provider',
            exact_missing_estimate=t['low_obligation'],source_head_constraint=t['source_head_identity'],
            available_constructions=['signed pairing','finite inverse head subtraction with full restoration',
                'joint Hermitian Gram domination','scale recurrence','correlation reduction'],
            generic_sharpness_is_not_an_actual_Mobius_disproof=True,increasing_tau_requires_rebounding_the_expanded_low_head=True))
    return rows


def _rules():
    return dict(twisted_fourth=dict(status='unconditional_import',critical_real_part='1/2',zeta_power='4',polynomial_power='2',
        height_power='1+epsilon',coefficient_class='abs(alpha_n)<=C_nu*n^nu for every nu>0, uniformly in U and phases',
        length_premise='R<=(Y/2)^kappa; fixed 0<kappa<1/4',source='https://arxiv.org/html/1609.02539v1',
        original_source='https://doi.org/10.1006/jnth.1995.1086'),
        transfer=dict(review='CORE_WEIGHTED_MOMENT_RULE_REVIEW_020.txt',
            method='positive strip Poisson kernels for pole-removed zeta squared; phase-uniform boundary moments',
            polynomial_squared_normalization='R^(1-2sigma)',below_length_threshold_licensed=False),
        recovery=dict(review='CORE_WEIGHTED_MOMENT_RULE_REVIEW_020.txt',
            method='analytic-residue Gaussian Perron, global Mellin norm, integer-cell averaging, full-history Hardy/Abel',
            ordinary_moment_not_inferred_from_residue=True,all_source_cross_terms_and_compensations_retained=True),
        generic_sharpness=dict(review='CORE_WEIGHTED_MOMENT_SHARPNESS_REVIEW_021.txt',
            method='exact harmonic-null dilation and fixed small-height lower bound',
            scope='generic bounded finite weights, not actual Mobius or the complete signed source'),formal_proof_assistant_verified=False)


def verify_search(parent,context,result,meter):
    _require(type(parent) is dict and parent.get('schema')=='core-moment-bound-feedback-v1' and parent.get('status')=='open' and
        parent.get('whole_signed_bound_proved') is False and parent.get('RH_proved') is False,'complete open inherited publication')
    join,lookup=_context(parent,context,meter)
    _require(type(result) is dict and set(result)=={'schema','spec','supplied_rules','targets','generic_weight_test',
        'inherited_complete_source_reduction','inherited_bindings','inherited_proof_dependencies','proof_dependencies',
        'next_search_tasks','statistics','actual_source_observations','fitted_constants','model_calls_in_search',
        'detector_has_general_analytic_prover','whole_signed_bound_proved','RH_proved'},'complete weighted-height artifact')
    _require(result['schema']=='core-weighted-height-search-v1','weighted-height schema');_spec(result['spec'],meter)
    _require(_same(result['supplied_rules'],_rules()),'explicit unconditional provider and reviewed rule trust base')
    _targets(parent,join,lookup,result['targets'],result['spec'],meter)
    witnesses=_witnesses(result['spec'],meter)
    _require(_same(result['generic_weight_test'],witnesses),'complete exact generic nullspace search and scoped obstruction')
    for key,original in [('inherited_complete_source_reduction','complete_source_reduction'),
                         ('inherited_bindings','generated_bound_obligations'),('inherited_proof_dependencies','proof_dependencies')]:
        _require(_same(result[key],parent[original]),'unchanged complete inherited signed source, recovery and frontier')
    _audit_graph(result['proof_dependencies'],meter)
    _require(_same(result['proof_dependencies'],_graph(result['targets'],witnesses)),'no open low Gram becomes a payment or full core proof')
    _require(_same(result['next_search_tasks'],_tasks(result['targets'])),'next actual arithmetic tasks follow exact open leaves')
    ts=result['targets'];stats=dict(targets=len(ts),candidate_lines=sum(len(t['lines']) for t in ts),
        height_plans=sum(len(l['plans']) for t in ts for l in t['lines']),high_auxiliary_bounds_proved=sum(t['high_auxiliary_proved'] for t in ts),
        open_low_Gram_obligations=sum(t['low_obligation'] is not None and t['low_obligation']['status']=='open_actual_Mobius_bound' for t in ts),
        generic_witnesses=len(witnesses['witnesses']),new_component_bounds_proved=0,
        inherited_component_bounds_proved=sum(t['inherited_component_bound_proved'] for t in ts),inherited_bindings=len(parent['generated_bound_obligations']))
    _require(_same(result['statistics'],stats),'auxiliary proofs excluded from new source payments')
    _require(all(type(result[k]) is int and result[k]==0 for k in ('actual_source_observations','fitted_constants','model_calls_in_search')) and
        all(result[k] is False for k in ('detector_has_general_analytic_prover','whole_signed_bound_proved','RH_proved')),
        'no fitted source experiments or false closure')
    meter.live(100*stats['candidate_lines']+200*stats['height_plans']+100*stats['inherited_bindings'])
    return dict(verified=True,targets=stats['targets'],high_auxiliary_bounds_proved=stats['high_auxiliary_bounds_proved'],
        open_low_Gram_obligations=stats['open_low_Gram_obligations'],new_component_bounds_proved=0,RH_proved=False)


def verify_feedback(parent,result,next_input,input_file,artifact,meter):
    _require(type(input_file) is str and bool(input_file) and type(artifact) is str and bool(artifact),'explicit immutable references')
    expected=dict(schema='core-weighted-height-feedback-v1',status='open',parent_obligation_file=input_file,complete_search_artifact=artifact,
        selected_source_representation=parent['selected_source_representation'],generated_bound_obligations=parent['generated_bound_obligations'],
        auxiliary_bound_targets=parent['auxiliary_bound_targets'],weighted_height_targets=result['targets'],generic_weight_test=result['generic_weight_test'],
        proof_dependencies=result['proof_dependencies'],inherited_proof_dependencies=parent['proof_dependencies'],next_search_tasks=result['next_search_tasks'],
        complete_source_reduction=parent['complete_source_reduction'],retained_original_proof_frontier=parent['retained_original_proof_frontier'],
        new_component_bounds_proved=0,
        next_priority='bound the complete signed residual; search the actual signed low Gram or a new joint construction, preserving the high/low dependency',
        whole_signed_bound_proved=False,RH_proved=False)
    _require(_same(next_input,expected),'complete inherited source plus open weighted obligations retained in feedback')
    meter.charge(100*len(result['targets'])+500)
    return dict(verified=True,status='open',new_component_bounds_proved=0)
