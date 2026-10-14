"""Independent polynomial, moment and norm-composition certificate auditor.

No new producer or numerical arithmetic source is imported. Sparse source
algebra and the moment optimizer are replayed by frozen independent checkers.
"""
from copy import deepcopy
from fractions import Fraction as Q

from check_core_split_bound_search import _require, _same, _rational
import check_core_cutoff_work_search as ALG
import check_core_cutoff_prefix_projections as PREFIX
from check_core_moment_bound_search import verify_product_moment

SPEC = dict(event_weights=['-1','-1/2','0','1/6','1/3','1/2','2/3','1','3/2','2'],
            moment_orders=['2','4'],epsilon='1/1000')
PRESENTATIONS = ['collected_sectors','signed_virtual_branches','substituted_virtual_branches',
                 'polarized_increment','two_child_energies']
RULES = dict(
    imported_fourth_moment=dict(status='unconditional_import', order='4',real_part='1/2',dyadic_power='1',
        logarithmic_power=4,source='https://arxiv.org/html/1609.02539v1',
        original_source='https://doi.org/10.1112/plms/s2-27.1.273',constant='fixed finite B4; no numerical value asserted'),
    moment_transfer=dict(orders=['2','4'],real_part_domain='[1/2,1)',power='1+epsilon',
        derivation='Gaussian pole-removed L2 three-lines; lower moments by Holder'),
    reflection=dict(power_per_factor='1/2-real_part',source='https://dlmf.nist.gov/25.4.E2'),
    convexity=dict(real_part_domain='(0,1)',power_per_factor='(1-real_part)/2+epsilon'),
    analytic_bridge=dict(review='JOINT_REMAINDER_MOMENT_REVIEW_018.txt',
        contour='Gaussian Perron, cross only theta, then Mellin Plancherel',
        integer_correction='complete J_theta and weighted integer cells, including n=1',
        channel_transfer='global weighted Hardy/Abel; orthogonal cell projection',formal_proof_assistant_verified=False))


def _substitute(poly,replacements,meter):
    out={}
    for names,coefficient in poly.items():
        term={():coefficient}
        for name in names: term=ALG._product(term,replacements.get(name,ALG._atom(name)),meter)
        out=ALG._add(out,term)
    return out


def _sum(*values):
    out={}
    for value in values:
        for key,c in value.items():out[key]=out.get(key,Q(0))+c
    return {key:c for key,c in out.items() if c}


def _multiply(left,right,meter):
    out={}
    for (r,k),c in left.items():
        for (s,j),d in right.items():
            key=(r+s,k+j);out[key]=out.get(key,Q(0))+c*d;meter.charge(35)
    return out


def _rows(value):
    return [dict(q_power=str(r),zeta_power=k,constant=str(c)) for (r,k),c in sorted(value.items())]


def _absolute(poly,sigma,meter):
    """Multiply each symbol's positive envelope, retaining all ordered pairs."""
    sigma=Q(sigma);_require(0<sigma<1,'strict finite polynomial strip')
    d=1-sigma; C=1/d; one={(Q(0),0):Q(1)}
    atoms={name:{(d,0):C} for name in ('A','Abar','D','Dbar')}
    atoms.update({name:{(Q(0),0):Q(1),(d,1):2+C} for name in ('E','Ebar')})
    atoms.update(c={(Q(0),0):Q(2)},a={(Q(-1),0):Q(1)},v=one,
        b={(-sigma,0):Q(1)},bbar={(-sigma,0):Q(1)},z={(Q(0),1):Q(1)},zbar={(Q(0),1):Q(1)})
    out={}
    for names,coefficient in poly.items():
        term={(Q(0),0):abs(coefficient)}
        for name in names:
            _require(name in atoms,'every source letter has a supplied finite majorant')
            term=_multiply(term,atoms[name],meter)
        out=_sum(out,term)
    return out


def _branch_max(values):
    return {key:max(value.get(key,Q(0)) for value in values) for key in set().union(*(set(v) for v in values))}


def source_envelopes(transition,sigma,meter):
    child=ALG._decode(transition['child'],meter)
    branches={sign:_substitute(child,dict(x={():Q(sign)},v={():Q(1)}),meter) for sign in (0,1,-1)}
    squared={sign:ALG._product(value,ALG._conjugate(value),meter) for sign,value in branches.items()}
    joined={sign:ALG._add(squared[sign],ALG._scale(squared[0],-1)) for sign in (1,-1)}
    sectors=[ALG._decode(p,meter,False) for p in transition['work_sectors']]
    _require(len(sectors)==3,'zero, odd and even complete source sectors')
    for sign in (1,-1):
        expected=_substitute(ALG._add(ALG._scale(sectors[1],sign),sectors[2]),dict(v={():Q(1)}),meter)
        _require(expected==joined[sign],'all signed work equals actual child minus complete zero child')
    E=ALG._add({():Q(1)},{('c','z'):Q(1)},{('A','z'):Q(-1)})
    replaced={s:_substitute(value,dict(E=E,Ebar=ALG._conjugate(E)),meter) for s,value in joined.items()}
    zero=_absolute(branches[0],sigma,meter);polar=[];separate=[]
    for sign in (1,-1):
        increment=ALG._add(branches[sign],ALG._scale(branches[0],-1))
        delta=_absolute(increment,sigma,meter);cross=_multiply(zero,delta,meter)
        polar.append(_sum({key:2*c for key,c in cross.items()},_multiply(delta,delta,meter)))
        full=_absolute(branches[sign],sigma,meter)
        separate.append(_sum(_multiply(full,full,meter),_multiply(zero,zero,meter)))
    values=[_sum(*[_absolute(value,sigma,meter) for value in sectors[1:]]),
        _branch_max([_absolute(value,sigma,meter) for value in joined.values()]),
        _branch_max([_absolute(value,sigma,meter) for value in replaced.values()]),_branch_max(polar),_branch_max(separate)]
    return dict(branches={str(sign):ALG._encode(joined[sign]) for sign in (1,-1)},
        representations=[dict(id=name,envelope=_rows(value),squared_envelope=_rows(_multiply(value,value,meter)))
            for name,value in zip(PRESENTATIONS,values)],
        meaning='abs(j_q) <= sum constant*q^q_power*abs(zeta(s))^zeta_power',
        source_signs_retained=True,mu_zero_joined_work_is_zero=True,zero_mu_history_and_head_retained=True,cached_samples_used=False)


def summed_power(power):
    power=Q(power)
    return dict(B_power=str(power+1 if power>-1 else Q(0)),log_degree='1' if power==-1 else '0')


def _bound(power,logs=0):return dict(B_power=str(Q(power)),log_degree=str(Q(logs)))
def _cost(bound):return Q(bound['B_power']),Q(bound['log_degree'])
def _largest(values):return max(values,key=_cost) if values else _bound(0)


def height_bound(moment,tau,epsilon):
    h=Q(moment['best']['integral_height_power'])-2;c=Q(moment['best']['epsilon_coefficient'])
    tau=Q(tau);eps=Q(epsilon)
    _require(tau>0 and eps>0 and c>=0,'strict epsilon and finite common-height premises')
    if h<0:eps=min(eps,-h/(2*(1+c)))
    exponent=h+c*eps
    return dict(dyadic_power_before_epsilon=str(h),epsilon=str(eps),epsilon_coefficient=str(c),dyadic_power=str(exponent),
        compact_head_retained=True,measure='dt/(2*pi)',denominator='abs(s)^2',common_height='2*(2*B)^tau',tau=str(tau),
        bound=_bound(tau*max(Q(0),exponent),int(exponent==0)),full_height_bound_available=exponent<0,
        constant='fixed finite; depends on contour and chosen epsilon, never B,V,X,N')


def direct_bound(rows,heights,meter):
    terms=[];floors=[]
    for row in rows:
        q=summed_power(row['q_power']);h=heights[row['zeta_power']]['bound'];floors.append(q)
        terms.append(dict(q_power=row['q_power'],zeta_power=row['zeta_power'],constant=row['constant'],
            bound=_bound(Q(q['B_power'])+Q(h['B_power']),Q(q['log_degree'])+Q(h['log_degree']))));meter.charge(80)
    bound=_largest([t['bound'] for t in terms])
    return dict(method='sum_event_L1',term_count=len(terms),bottleneck_terms=[t for t in terms if _cost(t['bound'])==_cost(bound)],bound=bound,
        coefficient_cost_floor=_largest(floors),coefficient_floor_is_not_a_bound_on_actual_work=True,
        theorem='M_common(B) <= sum_(q=2..2B) integral kappa*abs(j_q) dt/(2*pi)',uniform_in=['B','V','projection','X','N'])


def label_weight(program,gamma):
    gamma=Q(gamma);_require(gamma>=0,'nonnegative reciprocal label weight')
    fixed=program['projection']=='smooth' and program['prime_program']['kind']=='fixed'
    return dict(q_power='0' if fixed else str(gamma),
        multiplier='max(1,p^gamma), p='+str(program['prime_program']['fixed_prime']) if fixed else '1',
        rule='label in {1,p}' if fixed else '1 <= label <= q',constant_may_depend_on_fixed_prime=fixed,
        constant_may_depend_on_gamma=True)


def gram_attempt(rep,weight,heights,method,alpha,meter):
    g=Q(weight['q_power']);terms=[];floors=[]
    if method=='weighted_event_Cauchy':
        _require(type(alpha) is str,'rational event weight parameter');a=Q(alpha);mass=summed_power(-a)
        for row in rep['squared_envelope']:
            q=summed_power(Q(row['q_power'])+a+g);h=heights[row['zeta_power']]['bound']
            floors.append(_bound(Q(q['B_power'])+Q(mass['B_power']),Q(q['log_degree'])+Q(mass['log_degree'])))
            terms.append(dict(q_power=row['q_power'],zeta_power=row['zeta_power'],constant=row['constant'],
                bound=_bound(Q(q['B_power'])+Q(mass['B_power'])+Q(h['B_power']),
                             Q(q['log_degree'])+Q(mass['log_degree'])+Q(h['log_degree']))));meter.charge(80)
        rule='Q_gamma <= sup_label(sum_in_label q^(-alpha))*sum_q label(q)^gamma*q^alpha*integral kappa*abs(j_q)^2'
    else:
        _require(method=='weighted_label_Minkowski' and alpha is None,'licensed direct-sum Minkowski route')
        mass=None
        for row in rep['envelope']:
            q=summed_power(Q(row['q_power'])+g/2);h=heights[2*row['zeta_power']]['bound']
            floors.append(_bound(2*Q(q['B_power']),2*Q(q['log_degree'])))
            terms.append(dict(q_power=row['q_power'],zeta_power=2*row['zeta_power'],constant=row['constant'],
                bound=_bound(2*Q(q['B_power'])+Q(h['B_power']),2*Q(q['log_degree'])+Q(h['log_degree']))));meter.charge(80)
        rule='sqrt(Q_gamma) <= sum_q label(q)^(gamma/2)*norm_L2(kappa)(j_q); retain complete vector norm'
    bound=_largest([t['bound'] for t in terms])
    return dict(representation=rep['id'],method=method,event_weight=alpha,label_weight=weight,event_mass=mass,term_count=len(terms),
        bottleneck_terms=[t for t in terms if _cost(t['bound'])==_cost(bound)],bound=bound,rule=rule,
        coefficient_cost_floor=_largest(floors),coefficient_floor_is_not_a_bound_on_actual_work=True,every_signed_cross_in_source=True,proved_uniform_bound=True,
        constant='fixed finite; no numerical value fitted',target_assumed_in_proof=False)


def source_binding(parent,meter):
    _require(parent['schema']=='core-cutoff-prefix-projection-feedback-v1','current complete projection input')
    view=dict(parent,schema='core-cutoff-prime-orbit-feedback-v1')
    binding=PREFIX.source_binding(view,meter)
    _require(_same(binding,parent['prefix_projection_search']['binding']) and
        _same(parent['prefix_projection_search']['catalogue'],PREFIX.program_catalogue()),'full unchanged work and all projection targets')
    PREFIX.verify_proof_search(view,binding,parent['prefix_projection_search']['proof_search'],meter)
    return binding


def verify_search(parent,result,meter):
    _require(type(result) is dict and _same(result.get('spec'),SPEC),'sealed proof language; no arithmetic observations')
    binding=source_binding(parent,meter);target=parent['cutoff_work_targets'][0]
    _require((target['p'],target['m'],target['sigma'],target['theta'])==(2,3,'9/20','2/3'),'supported full actual source')
    program=target['programs'][target['selected_program']]
    source=source_envelopes(program['transition'],Q(target['sigma']),meter)
    _require(_same(result['source'],source),'all five exact source presentations and complete squared envelopes')
    tau=parent['prefix_projection_search']['proof_search']['common_window']['H']['U_power']
    powers=sorted({r['zeta_power'] for rep in source['representations'] for key in ('envelope','squared_envelope') for r in rep[key]} |
        {2*r['zeta_power'] for rep in source['representations'] for r in rep['envelope']})
    library=result['moment_library'];_require(type(library) is list and len(library)==len(powers),'every used unsquared and squared moment')
    cache={};heights={}
    for k,entry in zip(powers,library):
        factors=([dict(real_part=target['sigma'],power=str(k))] if k else [])+[
            dict(real_part=str(Q(target['sigma'])+1-Q(target['theta'])),power='2')]
        verify_product_moment(factors,SPEC['moment_orders'],entry['moment'],meter,cache)
        height=height_bound(entry['moment'],tau,SPEC['epsilon'])
        _require(_same(entry,dict(zeta_power=k,factors=factors,moment=entry['moment'],height=height)),
            'one outer zeta factor, complete compact/epsilon and common-height costs')
        heights[k]=height
    direct=[dict(representation=rep['id'],**direct_bound(rep['envelope'],heights,meter)) for rep in source['representations']]
    selected_direct=min(range(len(direct)),key=lambda i:(*_cost(direct[i]['bound']),direct[i]['term_count'],i))
    classes=[];tasks=[];lookup={}
    for p,route in zip(PREFIX.program_catalogue(),parent['prefix_projection_search']['proof_search']['programs']):
        for g in route['gram_auxiliaries']:
            weight=label_weight(p,g['gamma']);key=tuple(sorted(weight.items()))
            if key not in lookup:
                choices=[]
                for rep in source['representations']:
                    for a in SPEC['event_weights']:choices.append(gram_attempt(rep,weight,heights,'weighted_event_Cauchy',a,meter))
                    choices.append(gram_attempt(rep,weight,heights,'weighted_label_Minkowski',None,meter))
                chosen=min(range(len(choices)),key=lambda i:(*_cost(choices[i]['bound']),choices[i]['term_count'],i))
                lookup[key]=len(classes);classes.append(dict(id=len(classes),label_weight=weight,candidates=choices,selected=chosen))
            ident=lookup[key];best=classes[ident]['candidates'][classes[ident]['selected']];closed=_cost(best['bound'])<=_cost(g['sufficient_bound'])
            floor=min((c['coefficient_cost_floor'] for c in classes[ident]['candidates']),key=_cost)
            tasks.append(dict(program_id=p['id'],gamma=g['gamma'],attempt_id=ident,required=deepcopy(g['sufficient_bound']),
                established=deepcopy(best['bound']),best_coefficient_cost_floor=floor,
                excluded_by_coefficient_cost_floor=_cost(floor)>_cost(g['sufficient_bound']),requested_bound_proved=closed,
                gap_B_power=str(Q(best['bound']['B_power'])-Q(g['sufficient_bound']['B_power'])),
                uniform_domain='all dyadic B>=1 and every integer B<V<=2B',
                status='requested_bound_proved' if closed else 'weaker_uniform_bound_proved_target_open'))
    expected=dict(schema='core-work-moment-proof-search-v1',spec=deepcopy(SPEC),binding=binding,source=source,moment_library=library,
        direct_attempts=direct,selected_direct=selected_direct,Gram_attempt_classes=classes,targets=tasks,
        trust=dict(review='CORE_WORK_MOMENT_PROOF_RULE_REVIEW_028.txt',inherited_moment_rules=RULES,formal_proof_assistant_verified=False),
        statistics=dict(source_presentations=len(source['representations']),moment_products=len(library),distinct_Gram_proof_searches=len(classes),
            Gram_argument_candidates=sum(len(c['candidates']) for c in classes),requested_Gram_bounds=len(tasks),
            requested_Gram_bounds_proved=sum(t['requested_bound_proved'] for t in tasks),
            targets_excluded_even_without_height_cost=sum(t['excluded_by_coefficient_cost_floor'] for t in tasks),direct_grouped_bound_proved=True,
            direct_grouped_goal_proved=_cost(direct[selected_direct]['bound'])<=(Q(binding['inherited_bound']['power']),Q(0))),
        scope='uniform bounds conditional only on declared unconditional analytic trust base; no finite-source observations',
        whole_signed_bound_proved=False,RH_proved=False)
    _require(_same(result,expected),'complete unconditional proof costs, exact optimality, all targets and no false closure')
    return dict(verified=True,requested_Gram_bounds=len(tasks),requested_Gram_bounds_proved=sum(t['requested_bound_proved'] for t in tasks),
        direct_grouped_bound=direct[selected_direct]['bound'],whole_signed_bound_proved=False,RH_proved=False)


def verify_feedback(parent,result,out,artifact,meter):
    _require(type(artifact) is str and bool(artifact),'immutable symbolic search artifact')
    verify_search(parent,result,meter)
    expected=deepcopy(parent);expected.update(schema='core-work-moment-proof-feedback-v1',status='automatic_work_moment_proof_attempts_complete',
        parent_obligation_file='candidate10_cutoff_prefix_projection_obligation.json',complete_search_artifact=artifact)
    expected['work_moment_proof_search']=deepcopy(result);expected['inherited_work_moment_tasks']=deepcopy(parent['next_search_tasks'])
    _require(parent['next_search_tasks'][0]['target_id']=='actual_signed_core' and parent['next_search_tasks'][0]['priority']==0,
        'complete original signed core remains first')
    tasks=[deepcopy(parent['next_search_tasks'][0])]
    for winner in parent['prefix_projection_search']['selection']['selected']:
        ident=winner['program_id'];attempted=[t for t in result['targets'] if t['program_id']==ident]
        tasks.append(dict(priority=1,target_id=result['binding']['target_id'],search_kind='search_signed_work_arguments_after_uniform_moment_attempts',
            status='open',program=parent['prefix_projection_search']['catalogue'][ident],precise_Gram_attempts=attempted,
            best_direct_grouped_bound=result['direct_attempts'][result['selected_direct']]['bound'],
            signed_source_ref='work_moment_proof_search.binding.inherited_bound.R_q',
            allowed_next_mechanisms=['exact_signed_group_identity','controlled_cross_correlation','uniform_scale_recurrence'],
            failure_scope='only the enumerated absolute-polynomial and unconditional moment proof language',arithmetic_bound_refuted=False,
            complete_source_preserved=True,original_goal_and_all_alternatives_retained=True))
    tasks.extend(deepcopy(parent['next_search_tasks'][1:]));expected['next_search_tasks']=tasks
    _require(_same(out,expected),'all history, source complements, opposite drifts, channels and open signed tasks preserved')
    meter.charge(500+len(tasks)*100)
    return dict(verified=True,whole_signed_bound_proved=False,RH_proved=False)


def verify_height(moment,tau,epsilon,result,meter):
    _require(_same(result,height_bound(moment,tau,epsilon)),'compact, strict epsilon, denominator and common-height costs')
    meter.charge(100)
    return dict(verified=True)


def verify_gram_attempt(rep,weight,heights,method,alpha,result,meter):
    _require(_same(result,gram_attempt(rep,weight,heights,method,alpha,meter)),
        'complete source envelope, reciprocal event mass, every row and all norm costs')
    return dict(verified=True)
