"""Independent exact discrete-primitive and bound-certificate audit.

Transition columns use three ordinary polynomial specializations, and
feasibility is certified by primal or left-null identities, not a solver.
No new producer or arithmetic numerical archive is imported.
"""
from collections import Counter
from copy import deepcopy
from fractions import Fraction as Q

from check_core_split_bound_search import _require,_same,_rational
import check_core_cutoff_work_search as ALG
import check_core_work_moment_proof_search as MOM

STATE={'A','Abar','c','D','Dbar'}
FIXED={'z','zbar'}
EVENT={'a','b','bbar','x'}
INCREMENTS={'A':('b','x'),'Abar':('bbar','x'),'c':('a','x'),'D':('b',),'Dbar':('bbar',)}
SPEC=dict(inverse_increment_depth=1,potential_coefficients='rational',
    basis='real conjugate orbits inferred from source monomials',
    search='all endpoint/residual cost thresholds plus requested cost',free_variables='zero',numerical_samples=False)


def canonical(poly,meter):
    E={():Q(1),('c','z'):Q(1),('A','z'):Q(-1)}
    value=MOM._substitute(poly,dict(E=E,Ebar=ALG._conjugate(E),v={():Q(1)}),meter)
    _require(all(set(k)<=STATE|FIXED|EVENT and k.count('x')<=2 for k in value),'full reduced canonical state language')
    return value


def joined_source(transition,meter):
    _require(len(transition['work_sectors'])==3,'complete zero/odd/even sectors')
    odd,even=[ALG._decode(p,meter,False) for p in transition['work_sectors'][1:]]
    value=ALG._add({tuple(sorted(k+('x',))):v for k,v in odd.items()},
                   {tuple(sorted(k+('x','x'))):v for k,v in even.items()})
    value=canonical(value,meter)
    _require(value==ALG._conjugate(value),'complete real actual signed event')
    return value


def primitive_basis(source,meter):
    representatives=set()
    for key in source:
        counts=Counter(key)
        for variable,increment in INCREMENTS.items():
            needed=Counter(increment)
            if all(counts[s]>=n for s,n in needed.items()):
                rest=counts-needed
                if set(rest)<=STATE|FIXED:
                    names=tuple(sorted(list(rest.elements())+[variable]))
                    star=next(iter(ALG._conjugate({names:Q(1)})))
                    representatives.add(min(names,star))
            meter.charge(15+len(key))
    out=[]
    for key in sorted(representatives):
        star=next(iter(ALG._conjugate({key:Q(1)})))
        out.append({key:Q(1)} if key==star else {key:Q(1),star:Q(1)})
    return out


def delta(potential,meter):
    _require(all(set(k)<=STATE|FIXED for k in potential),'potential independent of the current event')
    samples=[]
    for sign in (0,1,-1):
        replacements={name:ALG._add(ALG._atom(name),{('a',):Q(sign)}) if name=='c' else
            ALG._add(ALG._atom(name),{('bbar' if name.endswith('bar') else 'b',):Q(1 if name.startswith('D') else sign)})
            for name in STATE}
        child=MOM._substitute(potential,replacements,meter)
        samples.append(ALG._add(child,ALG._scale(potential,-1)))
    zero,odd,even=ALG._interpolate(*samples)
    return ALG._add(zero,{tuple(sorted(k+('x',))):v for k,v in odd.items()},
                         {tuple(sorted(k+('x','x'))):v for k,v in even.items()})


def initialized(potential,meter):
    unit=MOM._substitute(potential,{name:{():Q(1)} for name in STATE},meter)
    return ALG._add(potential,ALG._scale(unit,-1))


def term_cost(key,sigma,heights,endpoint=False):
    sigma=Q(sigma);_require(0<sigma<1 and set(key)<=STATE|FIXED|(set() if endpoint else EVENT),'licensed strict-strip term')
    r=sum(key.count(s) for s in ('A','Abar','D','Dbar'))*(1-sigma)-key.count('a')-sigma*(key.count('b')+key.count('bbar'))
    k=key.count('z')+key.count('zbar');_require(k in heights,'every invariant moment power retained')
    h=heights[k]['bound'];_require(Q(h['B_power'])>=0 and Q(h['log_degree'])>=0,'compact head forbids negative height credit')
    q=MOM._bound(r) if endpoint else MOM.summed_power(r)
    return MOM._bound(Q(q['B_power'])+Q(h['B_power']),Q(q['log_degree'])+Q(h['log_degree']))


def bound(poly,sigma,heights,endpoint=False):
    return MOM._largest([term_cost(key,sigma,heights,endpoint) for key in poly])


def _solution(basis,solution,allowed,meter):
    _require(type(solution) is list,'complete rational potential coordinates')
    previous=-1;potential={}
    for item in solution:
        _require(type(item) is dict and set(item)=={'basis_id','coefficient'} and type(item['basis_id']) is int and
            previous<item['basis_id']<len(basis) and item['basis_id'] in allowed,'ordered unique affordable basis coordinates')
        c=_rational(item['coefficient'],meter);_require(c!=0,'omit zero solution coefficients')
        potential=ALG._add(potential,ALG._scale(basis[item['basis_id']],c));previous=item['basis_id']
    return potential


def _linear_certificate(source,basis,columns,constrained,allowed,item,meter):
    _require(item['status'] in ('feasible','infeasible'),'primal or dual status')
    if item['status']=='feasible':
        _require(set(item)=={'status','solution'},'complete feasible certificate')
        potential=_solution(basis,item['solution'],allowed,meter);image={}
        for coordinate in item['solution']:
            image=ALG._add(image,ALG._scale(columns[coordinate['basis_id']],Q(coordinate['coefficient'])))
        _require(all(image.get(key,Q(0))==source.get(key,Q(0)) for key in constrained),'every costly signed row cancels exactly')
        meter.charge(25*(len(image)+len(constrained)))
        return potential
    _require(set(item)=={'status','dual','contradiction'},'complete left-null obstruction certificate')
    dual=ALG._decode(item['dual'],meter)
    _require(bool(dual) and set(dual)<=set(constrained),'dual supported only on all declared constrained rows')
    for index in allowed:
        dot=sum((dual.get(key,Q(0))*value for key,value in columns[index].items()),Q(0))
        _require(dot==0,'dual annihilates every complete affordable column');meter.charge(30*len(columns[index]))
    contradiction=sum((value*source.get(key,Q(0)) for key,value in dual.items()),Q(0))
    _require(contradiction!=0 and _rational(item['contradiction'],meter)==contradiction,'nonzero exact dual contradiction')
    return None


def certificate(source,potential,sigma,heights,meter):
    residual=ALG._add(source,ALG._scale(delta(potential,meter),-1));boundary=initialized(potential,meter)
    endpoint=bound(boundary,sigma,heights,True);remaining=bound(residual,sigma,heights)
    return dict(potential=ALG._encode(potential),boundary=ALG._encode(boundary),residual=ALG._encode(residual),
        endpoint_bound=endpoint,residual_bound=remaining,bound=MOM._largest([endpoint,remaining]),
        identity='sum_(q=2..V) W_q = F(state_V)-F(state_1)+sum_(q=2..V) R_q',
        every_event_and_zero_mu_history_retained=True,target_bound_assumed=False)


def _check_number(value,meter):
    """Exact-size guard using the common charge-only meter interface."""
    _require(type(value) in (int,Q),'exact integer or rational source coefficient')
    bits=abs(value).bit_length() if type(value) is int else max(abs(value.numerator).bit_length(),value.denominator.bit_length())
    limit=getattr(meter,'max_bits',4096)
    _require(type(limit) is int and 1<=limit<=4096,'bounded configured rational bit limit')
    meter.charge(1+bits//64)
    _require(bits<=limit,'bounded exact source coefficient')
    if hasattr(meter,'maximum_rational_bits'):
        meter.maximum_rational_bits=max(meter.maximum_rational_bits,bits)
    return value


def verify_synthesis(source,sigma,heights,requested,result,meter):
    _require(type(source) is dict and source==ALG._conjugate(source) and
        all(set(key)<=STATE|FIXED|EVENT and key.count('x')<=2 for key in source),'complete Hermitian ternary source')
    _require(all(type(key) is tuple and tuple(sorted(key))==key and type(value) in (int,Q) and value!=0 for key,value in source.items()),'canonical exact nonzero source monomials')
    for value in source.values():_check_number(value,meter)
    _require(0<Q(sigma)<1 and Q(requested['B_power'])>=0,'strict contour and nonnegative target cost')
    basis=primitive_basis(source,meter);columns=[delta(p,meter) for p in basis]
    endpoints=[bound(initialized(p,meter),sigma,heights,True) for p in basis]
    universe=sorted(set(source).union(*(set(col) for col in columns)))
    row_costs={key:term_cost(key,sigma,heights) for key in universe}
    costs=sorted({MOM._cost(c) for c in list(row_costs.values())+endpoints+[requested,MOM._bound(0)]})
    trials=result['trials'];_require(type(trials) is list and len(trials)==len(costs),'complete finite threshold catalogue')
    feasible=[];chosen_potentials={}
    for i,((power,logs),trial) in enumerate(zip(costs,trials)):
        threshold=MOM._bound(power,logs)
        allowed=[j for j,c in enumerate(endpoints) if MOM._cost(c)<=(power,logs)]
        constrained=[key for key in universe if MOM._cost(row_costs[key])>(power,logs)]
        fixed=dict(threshold=threshold,allowed_basis=allowed,constrained_rows=len(constrained))
        _require(all(_same(trial[k],v) for k,v in fixed.items()),'complete allowed columns and costly row domain')
        item={k:v for k,v in trial.items() if k not in fixed}
        potential=_linear_certificate(source,basis,columns,constrained,allowed,item,meter)
        if potential is not None:feasible.append(i);chosen_potentials[i]=potential
    _require(bool(feasible),'complete baseline is feasible')
    selected=feasible[0];proved=certificate(source,chosen_potentials[selected],sigma,heights,meter)
    _require(MOM._cost(proved['bound'])<=costs[selected],'both endpoint and residual are paid')
    signed_rows=[key for key in universe if 'x' in key]
    exact=result['unconstrained_signed_elimination'];linear={k:v for k,v in exact.items() if k!='certificate'}
    potential=_linear_certificate(source,basis,columns,signed_rows,list(range(len(basis))),linear,meter)
    if potential is None:_require('certificate' not in exact,'no certificate for an infeasible signed primitive')
    else:_require(_same(exact['certificate'],certificate(source,potential,sigma,heights,meter)),'complete exact signed primitive still pays endpoint and deterministic residual')
    expected=dict(spec=SPEC,source=ALG._encode(source),sigma=str(Q(sigma)),requested=requested,
        basis=[ALG._encode(p) for p in basis],basis_endpoint_costs=endpoints,trials=trials,selected_trial=selected,
        certificate=proved,unconstrained_signed_elimination=exact,baseline=bound(source,sigma,heights),
        requested_bound_proved=MOM._cost(proved['bound'])<=MOM._cost(requested),finite_grammar_only=True,arithmetic_bound_refuted=False,
        uniform_domain='all dyadic B>=1 and every integer B<V<=2B; common height fixed during telescoping')
    _require(_same(result,expected),'minimum certified threshold, full telescoping identity, endpoint scope and no arithmetic refutation')
    return dict(verified=True,basis=len(basis),thresholds=len(trials),bound=proved['bound'],requested_bound_proved=expected['requested_bound_proved'])


def source_binding(parent,meter):
    _require(parent['schema']=='core-work-moment-proof-feedback-v1','published full-source input')
    binding=MOM.source_binding(dict(parent,schema='core-cutoff-prefix-projection-feedback-v1'),meter)
    _require(_same(binding,parent['work_moment_proof_search']['binding']),'unchanged full signed source')
    return binding


def verify_search(parent,result,meter):
    binding=source_binding(parent,meter);target=parent['cutoff_work_targets'][0]
    transition=target['programs'][target['selected_program']]['transition'];source=joined_source(transition,meter)
    library=parent['work_moment_proof_search']['moment_library'];heights={t['zeta_power']:t['height'] for t in library}
    _require(len(heights)==len(library),'unique already verified parent moment powers')
    tau=parent['prefix_projection_search']['proof_search']['common_window']['H']['U_power']
    for item in library:
        _require(_same(item['height'],MOM.height_bound(item['moment'],tau,parent['work_moment_proof_search']['spec']['epsilon'])),
            'accepted parent moment norm costs retain compact and epsilon loss')
    requested=MOM._bound(binding['inherited_bound']['power'])
    verify_synthesis(source,target['sigma'],heights,requested,result['search'],meter)
    exact=result['search']['unconstrained_signed_elimination']
    p=canonical(ALG._decode(transition['parent'],meter),meter);energy=ALG._product(p,ALG._conjugate(p),meter)
    restatement=exact['status']=='feasible' and ALG._decode(exact['certificate']['boundary'],meter)==initialized(energy,meter)
    search=result['search']
    expected=dict(schema='core-signed-primitive-search-v1',binding=binding,search=search,inherited_height_library=deepcopy(library),
        common_window=deepcopy(parent['prefix_projection_search']['proof_search']['common_window']),
        exact_primitive_is_original_energy_restatement=restatement,
        supplied_rules=dict(review='CORE_SIGNED_PRIMITIVE_SEARCH_REVIEW_029.txt',
            Mobius_reciprocal_bound='N*c_N=1+sum_(d<=N) mu(d)*{N/d}; abs(c_N)<=2',
            moment_library='unchanged independently verified parent certificates',formal_proof_assistant_verified=False),
        statistics=dict(source_monomials=len(source),inferred_potential_basis=len(search['basis']),cost_thresholds=len(search['trials']),
            infeasible_thresholds=sum(t['status']=='infeasible' for t in search['trials']),
            signed_elimination_found=exact['status']=='feasible',requested_bound_proved=search['requested_bound_proved'],
            actual_arithmetic_observations=0,fitted_constants=0,runtime_model_calls=0),whole_signed_bound_proved=False,RH_proved=False)
    _require(_same(result,expected),'complete source/library binding, exact endpoint restatement detection and no full-core claim')
    return dict(verified=True,requested_bound_proved=search['requested_bound_proved'],whole_signed_bound_proved=False,RH_proved=False)


def verify_feedback(parent,result,out,artifact,meter):
    _require(type(artifact) is str and bool(artifact),'immutable proof artifact')
    verify_search(parent,result,meter)
    expected=deepcopy(parent);expected.update(schema='core-signed-primitive-feedback-v1',status='signed_primitive_proof_search_complete',
        parent_obligation_file='candidate10_work_moment_proof_obligation.json',complete_search_artifact=artifact)
    expected['signed_primitive_search']=deepcopy(result);expected['inherited_signed_primitive_tasks']=deepcopy(parent['next_search_tasks'])
    _require(parent['next_search_tasks'][0]['target_id']=='actual_signed_core' and parent['next_search_tasks'][0]['priority']==0,'full core remains priority zero')
    requested=next(t for t in result['search']['trials'] if t['threshold']==result['search']['requested'])
    tasks=[deepcopy(parent['next_search_tasks'][0]),dict(priority=1,search_kind='supply_arithmetic_endpoint_control_or_extend_signed_primitive_language',
        target_id=result['binding']['target_id'],status='open',exact_failed_requested_threshold=requested,
        best_proved_bound=result['search']['certificate']['bound'],original_energy_restatement=result['exact_primitive_is_original_energy_restatement'],
        failure_scope='only source-inferred polynomial primitives with existing endpoint and residual majorants',
        arithmetic_bound_refuted=False,complete_source_and_alternatives_preserved=True)]
    tasks.extend(deepcopy(parent['next_search_tasks'][1:]));expected['next_search_tasks']=tasks
    _require(_same(out,expected),'full source, all drifts, units, original channel routes and open alternatives retained')
    return dict(verified=True,whole_signed_bound_proved=False,RH_proved=False)
