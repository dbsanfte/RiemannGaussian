"""Independent exact checker for moment allocations and source recovery.

Allocation vertices are obtained from active linear constraints, not from
the producer's box-corner construction.  No new generator is imported.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from math import ceil

from check_core_split_bound_search import _require, _same, _rational
from check_core_bound_goal_search import _source


def _integer(value,lo,hi):
    _require(type(value) is int and lo<=value<=hi,'bounded exact integer')
    return value


def _solve(matrix,right,meter):
    n=len(right);rows=[list(row)+[c] for row,c in zip(matrix,right)]
    for col in range(n):
        pivot=next((i for i in range(col,n) if rows[i][col]),None)
        if pivot is None:return None
        rows[col],rows[pivot]=rows[pivot],rows[col]
        divisor=rows[col][col];rows[col]=[v/divisor for v in rows[col]]
        for i in range(n):
            if i==col:continue
            c=rows[i][col]
            if c:rows[i]=[v-c*w for v,w in zip(rows[i],rows[col])]
            meter.charge(15*(n+1))
    return tuple(row[-1] for row in rows)


def allocation_vertices(upper,meter):
    """Every vertex of bounded box intersected with sum(lambda)<=1.

    At any vertex n linearly independent active supporting hyperplanes
    exist. Enumerating all such n-element systems is complete even for
    degenerate boxes with zero-width coordinates.
    """
    upper=tuple(map(Q,upper));n=len(upper)
    _require(1<=n<=4 and all(0<=u<=1 for u in upper),'bounded Holder allocation polytope')
    constraints=[]
    for i,u in enumerate(upper):
        row=tuple(Q(int(i==j)) for j in range(n))
        constraints.append((row,Q(0)));constraints.append((row,u))
    constraints.append((tuple(Q(1) for _ in range(n)),Q(1)))
    vertices=set()
    for active in combinations(constraints,n):
        point=_solve([row for row,_ in active],[c for _,c in active],meter)
        if point is not None and all(0<=v<=u for v,u in zip(point,upper)) and sum(point,Q(0))<=1:
            vertices.add(point)
        meter.charge(20*n)
    _require(bool(vertices),'nonempty compact allocation polytope')
    return sorted(vertices)


def _orders(orders):
    _require(type(orders) is list and orders in ([],['2'],['4'],['2','4']),'only supplied unconditional moments')
    return [Q(c) for c in orders]


def verify_product_moment(factors,orders,result,meter,cache=None):
    _require(type(factors) is list and 1<=len(factors)<=4,'bounded generic zeta product')
    qs=_orders(orders);parsed=[]
    for factor in factors:
        _require(type(factor) is dict and set(factor)=={'real_part','power'},'exact factor-moment schema')
        a=_rational(factor['real_part'],meter);b=_rational(factor['power'],meter)
        _require(0<a<1 and 0<b<=128,'positive fractional moment power on non-pole line')
        parsed.append((a,b))
    cache={} if cache is None else cache;best=None;examined=0
    for reflected in product((False,True),repeat=len(parsed)):
        effective=[1-a if r else a for (a,_),r in zip(parsed,reflected)]
        choices=[[Q(0)]+qs if a>=Q(1,2) else [Q(0)] for a in effective]
        for orders_used in product(*choices):
            upper=tuple(min(Q(1),b/q) if q else Q(0) for (_,b),q in zip(parsed,orders_used))
            if upper not in cache:cache[upper]=allocation_vertices(upper,meter)
            meter.charge(10*len(parsed))
            for weights in cache[upper]:
                examined+=1;rows=[];height=Q(1);slack=Q(0)
                for (a,b),line,r,q,weight in zip(parsed,effective,reflected,orders_used,weights):
                    remainder=b-q*weight
                    _require(remainder>=0 and (not weight or q in qs and line>=Q(1,2)),
                        'licensed moment factors and nonnegative convexity remainder')
                    fe=b*(Q(1,2)-a) if r else Q(0)
                    pointwise=remainder*(1-line)/2
                    height+=fe+pointwise;slack+=remainder+weight
                    rows.append(dict(original_real_part=str(a),power=str(b),reflected=r,effective_real_part=str(line),
                        moment_order=str(q),holder_weight=str(weight),convexity_power=str(remainder),
                        reflection_height_power=str(fe),convexity_height_power=str(pointwise)))
                    meter.charge(100)
                candidate=dict(factors=rows,holder_unused=str(1-sum(weights,Q(0))),integral_height_power=str(height),
                    epsilon_coefficient=str(slack))
                # Compact polytope + affine objective => a vertex attains the
                # global minimum; secondary affine epsilon cost uses same rule.
                if best is None or (height,slack)<(Q(best['integral_height_power']),Q(best['epsilon_coefficient'])):
                    best=candidate
    expected=dict(best=best,allocations_examined=examined,
        completeness='every reflection/order and every Holder box-simplex vertex')
    _require(_same(result,expected),'global product-moment optimum, full reflection/order allocation coverage and exact costs')
    return dict(verified=True,integral_height_power=best['integral_height_power'],
        epsilon_coefficient=best['epsilon_coefficient'],allocations_examined=examined)


def _moment(p,m,theta):
    rho=Q(m-1,m)
    return dict(rule='complete E^m hyperbola prefix then finite A^p convolution and Abel tail',
        residual_prefix_power=str(rho),theta=str(theta),finite_factor_degree=p,ordinarily_convergent=rho<theta,
        analytic_residue_is_not_ordinary_convergence=True,full_infinite_tail_retained=True)


def _candidate(p,m,theta,alpha,sigma,orders,goal,candidate,meter,cache):
    _integer(p,0,16);_integer(m,2,64)
    _require(0<alpha<1 and 0<theta<1,'licensed finite arithmetic powers and strict fractional cutoff')
    _require(0<sigma<min(Q(1,2),theta),'belowhalf non-pole contour and integrable small-x centering')
    _require(type(candidate) is dict and type(candidate.get('moment_branches')) is list and len(candidate['moment_branches'])==2,
        'both complete E-power branches')
    factors=[[dict(real_part=str(sigma+1-theta),power='2')],
        [dict(real_part=str(sigma),power=str(2*m)),dict(real_part=str(sigma+1-theta),power='2')]]
    branches=candidate['moment_branches']
    for inputs,branch in zip(factors,branches):verify_product_moment(inputs,orders,branch,meter,cache)
    heights=[Q(b['best']['integral_height_power'])-2 for b in branches]
    slack=max(Q(b['best']['epsilon_coefficient']) for b in branches)
    strict=max(heights)<0
    epsilon=min(Q(1),-max(heights)/(2*(1+slack))) if strict else None
    if strict:
        _require(all(h+epsilon*Q(b['best']['epsilon_coefficient'])<0 for h,b in zip(heights,branches)),
            'every full dyadic tail strictly summable after epsilon and fixed logs')
    power=2*(p+m)*(1-sigma);energy=2*sigma-1+alpha*power;moment=_moment(p,m,theta)
    failures=[]
    if not strict:failures.append('dyadic_Mellin_tail_not_summable_by_this_plan')
    if not moment['ordinarily_convergent']:failures.append('ordinary_centering_moment_unproved')
    if energy>goal:failures.append('cutoff_cost_exceeds_target_energy_power')
    expected=dict(sigma=str(sigma),moment_branches=branches,mellin_height_powers=list(map(str,heights)),
        epsilon=str(epsilon) if epsilon is not None else None,strict_tail_summation=strict,
        full_finite_factor_U_power=str(power),residue_squared_U_power=str(2*(p+m)*(1-theta)),
        complete_centering=moment,recovered_energy_X_power=str(energy),energy_log_degree=0,
        target_met=not failures,failed_premises=failures,constants_uniform_in=['U','X','N'],
        constants_may_depend_on=['p','m','theta','sigma','epsilon'],
        pole_removal='T(1)=c-A(1)=0 before estimating E(s)=1+zeta(s)T(s)',
        analytic_residue='A(theta)^p E(theta)^m/theta',
        centered_coefficient='K*A^p*E^m - A(theta)^p E(theta)^m*J_theta/theta',
        full_unit_and_small_x_tail_retained=True)
    _require(_same(candidate,expected),'all centering, finite weight, height, energy and uniformity premises')


def _grid(theta,maximum):
    return sorted({Q(n,d) for d in range(2,maximum+1) for n in range(1,d) if 0<Q(n,d)<min(Q(1,2),theta)})


def _targets(parent,join,result,spec,meter):
    alpha=Q(parent['selected_source_representation']['alpha'])
    eligible=[t for t in join['collected_terms'] if t['powers'][2]==1 and t['powers'][3]>=2 and
        all(t['powers'][i]==0 for i in (1,4,5,6,7))]
    old=parent['auxiliary_bound_targets']
    _require(type(old) is list and len(old)==len(eligible) and type(result) is list and len(result)==len(old),
        'all actual pure residual target terms, no source removal')
    cache={}
    for inherited,term,target in zip(old,eligible,result):
        p=_integer(inherited['p'],0,16);m=_integer(inherited['m'],2,64);theta=_rational(inherited['theta'],meter)
        _require(p==term['powers'][0] and m==term['powers'][3] and theta==Q(2,3) and
            _same(inherited['source_term'],term) and inherited['id']=='centered_A'+str(p)+'_E'+str(m),
            'each inherited target bound to its actual full source coefficient and kernel')
        grid=_grid(theta,spec['sigma_denominator_max']);candidates=target['candidate_lines']
        _require(type(candidates) is list and len(candidates)==len(grid),'every rational contour in declared grid')
        for sigma,candidate in zip(grid,candidates):
            _candidate(p,m,theta,alpha,sigma,spec['moment_orders'],Q(spec['target_energy_power']),candidate,meter,cache)
        passing=[i for i,c in enumerate(candidates) if c['target_met']]
        selected=min(passing,key=lambda i:(Q(candidates[i]['recovered_energy_X_power']),
            max(map(Q,candidates[i]['mellin_height_powers'])),i)) if passing else None
        constant=dict(name='C_norm_'+inherited['id'],kind='fixed_finite_theorem_constant',
            statement='sum_(n>=1)|complete centered prefix(n)|^2*n^(-2sigma-1)<=C_norm*U^b',
            numerical_value=None,uniform_in=['U','X','N']) if selected is not None else None
        expected=dict(target_id=inherited['id'],p=p,m=m,theta=str(theta),source_term=term,candidate_lines=candidates,
            selected=selected,component_bound_proved=selected is not None,proof_constant=constant,all_source_compensations_retained=True)
        _require(_same(target,expected),'exact contour selection and fully proved component versus open target')


def _channel_constant(channels,sigma,meter):
    _require(type(channels) is list and bool(channels),'full polynomial channel vector')
    total=Q(0)
    for channel in channels:
        eta=_rational(channel['eta'],meter);_require(eta>=0,'nonnegative channel log normalization')
        coefficients=channel['polynomial'];_require(type(coefficients) is list and bool(coefficients),'all channel coefficients including unit')
        coefficients=[_rational(c,meter) for c in coefficients]
        p0=sum(map(abs,coefficients),Q(0));p1=sum((j*abs(c) for j,c in enumerate(coefficients)),Q(0))
        total+=(2**ceil(eta)*(p0+2*(1+1/sigma)*p1))**2;meter.charge(100+50*len(coefficients))
    return total


def _reduction(parent,context,targets,meter):
    paid=[t for t in targets if t['component_bound_proved']];programs=context['channel_programs']
    _require(type(programs) is list and len({p['id'] for p in programs})==len(programs),'unique original channel programs')
    lookup={p['id']:p for p in programs};old=parent['generated_bound_obligations']
    _require(type(old) is list and len({b['parent_obligation_id'] for b in old})==len(old) and
        set(lookup)=={b['parent_obligation_id'] for b in old},'all and only inherited original routes')
    alpha=Q(parent['selected_source_representation']['alpha']);bindings=[]
    for binding in old:
        program=lookup[binding['parent_obligation_id']]
        _require(_same(program['transport_program'],binding['transport_program']),'unchanged full original transport')
        costs=[]
        for target in paid:
            chosen=target['candidate_lines'][target['selected']];sigma=Q(chosen['sigma']);up=Q(chosen['full_finite_factor_U_power'])
            _require(Q(chosen['recovered_energy_X_power'])<=0,'uniform constant recovery from nonpositive energy power')
            cc=_channel_constant(program['construction']['channels'],sigma,meter)
            cutoff=Q(2)**ceil(2*sigma+1+2*alpha*up)
            scalar=Q(target['source_term']['coefficient'])
            costs.append(dict(target_id=target['target_id'],constant=target['proof_constant']['name'],
                rational_multiplier=str(len(paid)*scalar*scalar*cc*cutoff),channel_Hardy_constant=str(cc),
                local_and_cutoff_constant=str(cutoff),energy_X_power=chosen['recovered_energy_X_power']))
        _require(_rational(binding['sufficient_goal']['p'],meter)>=0,'paid constants fit inherited nonnegative residual log target')
        bindings.append(dict(parent_obligation_id=binding['parent_obligation_id'],inherited_binding=binding,
            new_paid_constant=dict(kind='positive_linear_combination_of_uniform_theorem_constants',terms=costs),
            sufficient_goal=dict(expression='S_Z(X), complete signed residual after old and new paid pieces',
                upper=binding['sufficient_goal']['upper'],p=binding['sufficient_goal']['p'],
                quantifier=binding['sufficient_goal']['quantifier'],status='open'),
            recovery='S_g<=4*S_Z+4*C_new+2*C_old; S_Z<=4*S_g+4*C_old+2*C_new' if paid else binding['recovery'],
            all_history_and_units_retained=True,whole_signed_bound_proved=False,RH_proved=False))
    return dict(inherited_complete_signed_join=context['complete_signed_join'],
        inherited_original_frontier=parent['retained_original_proof_frontier'],
        new_paid_components=[dict(target_id=t['target_id'],source_term=t['source_term'],
            centered_component='source_coefficient*(K*A^p*E^m - M/theta*J_theta)',
            retained_opposite_drift='source_coefficient*M/theta*J_theta',ordinary_moment_proved=True) for t in paid],
        exact_identity='g=P_old+P_new+Z; Z=R_old-P_new; R_old is the inherited complete signed residual',
        whole_join_cross_terms_retained=True,transport_error_retained='-e',
        common_horizon='N=4X-1 for BOTH blocks; same coefficients and cutoffs',bindings=bindings)


def _next_tasks(targets):
    tasks=[dict(target_id='actual_signed_core',priority=0,status='open',search_kind='joint_signed_core_control',
        preserve='complete new residual Z, every drift, signed cross term, transport error and inherited recovery')]
    for target in targets:
        if target['component_bound_proved']:continue
        eligible=[c for c in target['candidate_lines'] if Q(c['recovered_energy_X_power'])<=0]
        c=min(eligible,key=lambda c:max(map(Q,c['mellin_height_powers']))) if eligible else None
        missing=dict(sigma=c['sigma'],expression='integral_T^2T |zeta(s+1-theta)|^2*(1+|zeta(s)|^(2m)) dt',
            required_height_power='strictly less than 2',current_height_power=str(2+max(map(Q,c['mellin_height_powers']))),
            quantifiers='one fixed positive saving; every T>=2; constants independent of U,X,N',
            ordinary_centering_moment_also_required=not c['complete_centering']['ordinarily_convergent']) if c else None
        tasks.append(dict(target_id=target['target_id'],priority=1,status='open',
            search_kind='search_joint_moment_or_short_factor_gain',missing_estimate=missing,
            alternative='retain the actual finite A,T weights inside the moment; prove a smaller U cost or a joint signed recurrence',
            finite_language_failure_is_not_arithmetic_disproof=True))
    return tasks


def _rules():
    return dict(imported_fourth_moment=dict(status='unconditional_import',order='4',real_part='1/2',dyadic_power='1',
        logarithmic_power=4,source='https://arxiv.org/html/1609.02539v1',original_source='https://doi.org/10.1112/plms/s2-27.1.273',
        constant='fixed finite B4; no numerical value asserted'),
        moment_transfer=dict(orders=['2','4'],real_part_domain='[1/2,1)',power='1+epsilon',
            derivation='Gaussian pole-removed L2 three-lines; lower moments by Holder'),
        reflection=dict(power_per_factor='1/2-real_part',source='https://dlmf.nist.gov/25.4.E2'),
        convexity=dict(real_part_domain='(0,1)',power_per_factor='(1-real_part)/2+epsilon'),
        analytic_bridge=dict(review='JOINT_REMAINDER_MOMENT_REVIEW_018.txt',
            contour='Gaussian Perron, cross only theta, then Mellin Plancherel',
            integer_correction='complete J_theta and weighted integer cells, including n=1',
            channel_transfer='global weighted Hardy/Abel; orthogonal cell projection',formal_proof_assistant_verified=False))


def _graph(targets):
    nodes=[dict(id='analytic_rule_library',status='reviewed_and_imported',depends_on=[])]
    nodes.extend(dict(id='moment_'+t['target_id'],status='proved' if t['component_bound_proved'] else 'open',
        depends_on=['analytic_rule_library'] if t['component_bound_proved'] else []) for t in targets)
    nodes.extend([dict(id='complete_signed_complement',status='open',depends_on=[]),
        dict(id='actual_signed_core',status='open',depends_on=['moment_'+t['target_id'] for t in targets]+['complete_signed_complement']),
        dict(id='original_RH_recovery',status='conditional',depends_on=['actual_signed_core'])])
    return nodes


def _audit_graph(nodes,meter):
    lookup={n['id']:n for n in nodes};_require(len(lookup)==len(nodes),'unique proof dependency nodes')
    done=set();active=set()
    def visit(ident):
        _require(ident in lookup and ident not in active,'known acyclic proof dependencies')
        if ident in done:return
        active.add(ident);node=lookup[ident]
        _require(node['status'] in ('reviewed_and_imported','proved','open','conditional'),'explicit trust and proof status')
        for dep in node['depends_on']:
            visit(dep)
            _require(node['status'] not in ('proved','reviewed_and_imported') or
                lookup[dep]['status'] in ('proved','reviewed_and_imported'),'paid proof cannot depend on an open arithmetic premise')
            meter.charge(30)
        active.remove(ident);done.add(ident)
    for ident in lookup:visit(ident)


def verify_search(parent,context,result,meter):
    _require(type(parent) is dict and parent.get('whole_signed_bound_proved') is False and parent.get('RH_proved') is False,
        'complete inherited signed core remains open')
    _require(type(context) is dict and set(context)=={'complete_signed_join','channel_programs'},'complete independent source and channel context')
    join=_source(parent,meter);_require(_same(context['complete_signed_join'],join),'independent complete source inverse/substitution replay')
    _require(type(result) is dict and set(result)=={'schema','spec','supplied_rules','targets','source_reduction','proof_dependencies',
        'next_search_tasks','statistics','actual_source_observations','fitted_constants','model_calls_in_search',
        'detector_has_general_analytic_prover','whole_signed_bound_proved','RH_proved'},'complete moment-search certificate')
    _require(result['schema']=='core-moment-bound-search-v1','moment-search schema')
    spec=result['spec'];_require(type(spec) is dict and set(spec)=={'sigma_denominator_max','moment_orders','target_energy_power'},'declared bounded moment grammar')
    _integer(spec['sigma_denominator_max'],3,32);_orders(spec['moment_orders'])
    _require(_rational(spec['target_energy_power'],meter)==0,'implemented uniform constant-energy source recovery')
    _require(_same(result['supplied_rules'],_rules()),'explicit unconditional provider and reviewed analytical trust base')
    _targets(parent,join,result['targets'],spec,meter)
    reduction=_reduction(parent,context,result['targets'],meter)
    _require(_same(result['source_reduction'],reduction),'every old/new payment, source scalar, channel cost, drift, error and recovery retained')
    _audit_graph(result['proof_dependencies'],meter)
    _require(_same(result['proof_dependencies'],_graph(result['targets'])),'whole signed complement stays an explicit open dependency')
    _require(_same(result['next_search_tasks'],_next_tasks(result['targets'])),'unpaid moment requests derived from certified costs, not claimed proved')
    stats=dict(targets=len(result['targets']),candidate_lines=sum(len(t['candidate_lines']) for t in result['targets']),
        moment_allocations_examined=sum(b['allocations_examined'] for t in result['targets'] for c in t['candidate_lines'] for b in c['moment_branches']),
        new_component_bounds_proved=sum(t['component_bound_proved'] for t in result['targets']),inherited_bindings=len(reduction['bindings']))
    _require(_same(result['statistics'],stats),'conditional requests excluded from theorem count')
    _require(all(type(result[k]) is int and result[k]==0 for k in ('actual_source_observations','fitted_constants','model_calls_in_search')) and
        result['detector_has_general_analytic_prover'] is False and result['whole_signed_bound_proved'] is False and result['RH_proved'] is False,
        'no fitted constants, source observations or false core closure')
    meter.live(100*stats['candidate_lines']+100*len(reduction['bindings'])+50*len(join['collected_terms']))
    return dict(verified=True,targets=stats['targets'],new_component_bounds_proved=stats['new_component_bounds_proved'],
        inherited_bindings=stats['inherited_bindings'],complete_signed_core_proved=False,RH_proved=False)


def verify_feedback(parent,result,next_input,input_file,artifact,meter):
    _require(type(input_file) is str and bool(input_file) and type(artifact) is str and bool(artifact),'explicit immutable parent/artifact references')
    expected=dict(schema='core-moment-bound-feedback-v1',status='open',parent_obligation_file=input_file,complete_search_artifact=artifact,
        selected_source_representation=parent['selected_source_representation'],generated_bound_obligations=result['source_reduction']['bindings'],
        auxiliary_bound_targets=result['targets'],proof_dependencies=result['proof_dependencies'],next_search_tasks=result['next_search_tasks'],
        complete_source_reduction=result['source_reduction'],retained_original_proof_frontier=parent['retained_original_proof_frontier'],
        new_component_bounds_proved=result['statistics']['new_component_bounds_proved'],
        next_priority='discover a bound for the complete signed residual Z; feed explicit unpaid moment obligations back into search',
        whole_signed_bound_proved=False,RH_proved=False)
    _require(_same(next_input,expected),'complete new residual, all open ordinary moments and original recovery retained in feedback')
    meter.charge(500+100*len(result['targets']))
    return dict(verified=True,status='open',new_component_bounds_proved=result['statistics']['new_component_bounds_proved'])
