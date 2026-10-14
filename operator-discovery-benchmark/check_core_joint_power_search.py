"""Independent auditor for finite signed power-kernel centering certificates.

This module reads no source observations and imports no certificate generator.
Its bounds come from the supplied all-real integral remainder theorem, complete
finite convolution moments, and exact symbolic source coefficients.
"""
from fractions import Fraction as Q
from math import ceil, comb
import re

from check_core_prefix_proof_search import verify_nodes as _verify_prior_nodes

PROFILES = tuple(map(Q,('1/6','1/3','1/2','2/3','5/6','1')))


def _require(condition,message):
    if not condition:raise ValueError(message)


def _rational(text,meter):
    _require(type(text) is str and 0<len(text)<=1235 and re.fullmatch(r'-?\d+(?:/\d+)?',text) is not None,
             'canonical bounded rational string')
    meter.charge(len(text)+1)
    try:value=Q(text)
    except (ValueError,ZeroDivisionError) as error:raise ValueError('exact rational') from error
    _require(str(value)==text,'canonical rational')
    if hasattr(meter,'number'):return meter.number(value)
    _require(max(abs(value.numerator).bit_length(),value.denominator.bit_length())<=4096,'exact scalar bit cap')
    return value


def _integer(value,lower=0,upper=1000):
    _require(type(value) is int and lower<=value<=upper,'bounded exact integer')
    return value


def _finite_moment_bound(s,r):
    """(constant,N power,log degree) for complete finite cutoff moments."""
    _require(s>=0 and 0<r<1,'nonnegative moment exponent and strict cutoff')
    if s<1:return (1/(1-s),r*(1-s),0)
    if s==1:return (Q(1),Q(0),1)
    return (s/(s-1),Q(0),0)


def _payment(constant,power,degree,meter):
    if power>0 or power==0 and degree:return None
    if degree==0:return constant
    ratio=Q(degree)/(-power)
    _require(degree*(max(abs(ratio.numerator).bit_length(),ratio.denominator.bit_length())+1)+
             max(abs(constant.numerator).bit_length(),constant.denominator.bit_length())+2<=4096,
             'uniform payment exact bit cap')
    meter.charge(10*degree+10)
    return constant*2**degree*(1+ratio**degree)


def _energy(constant,power,degree,meter):
    c=4*constant**2;e=2*power-1;k=2*degree
    paid=_payment(c,e,k,meter)
    return dict(constant=str(c),power=str(e),log_degree=k,uniform_constant=None if paid is None else str(paid))


def _abel(construction,meter):
    channels=construction['channels']
    _require(type(channels) is list and bool(channels),'all channels')
    total=Q(0)
    for channel in channels:
        eta=_rational(channel['eta'],meter)
        _require(0<=eta<=100,'nonnegative bounded channel eta')
        coefficients=channel['polynomial']
        _require(type(coefficients) is list and 0<len(coefficients)<=100,'complete channel polynomial')
        values=[_rational(v,meter) for v in coefficients]
        variation=abs(values[0])+2*sum((abs(v) for v in values[1:]),Q(0))
        total+=(2**ceil(eta)*variation)**2
        meter.charge(20+len(values))
    return total


def _ref_key(ref):
    _require(type(ref) is dict and set(ref)=={'source_key','depth','piece'},'complete source piece reference')
    key=ref['source_key']
    _require(type(key) is dict and set(key)=={'mode','a','b'} and type(key['mode']) is str,'source key')
    _integer(key['a'],0,20);_integer(key['b'],0,20)
    _integer(ref['depth'],0,20);_integer(ref['piece'],0,20)
    return key['mode'],key['a'],key['b'],ref['depth'],ref['piece']


def _current_pieces(row,prefix_result,remaining_refs,meter):
    _require(type(row) is dict and type(prefix_result) is dict,'verified source geometry and prefix artifact')
    _require(prefix_result['geometry_id']==row['id'] and prefix_result['alpha']==row['alpha'] and
             prefix_result['gamma']==row['gamma'],'same source geometry')
    alpha=_rational(row['alpha'],meter);gamma=_rational(row['gamma'],meter)
    _require(0<alpha<1 and 0<gamma<1,'strict cutoff exponents')
    checked_nodes=_verify_prior_nodes(prefix_result['nodes'],alpha,gamma,meter)
    modes={};source_terms={}
    for case in row['cases']:
        mode=case['mode'];name=mode['name']
        _require(type(name) is str and name not in modes,'unique original source mode')
        _require(mode['coefficient'] in ('beta','-beta','-R_u'),'retained original signed scalar')
        _integer(mode['p'],0,16);_integer(mode['q'],0,16)
        modes[name]=mode
        for t in case['program']['terms']:
            _integer(t['a'],0,20);_integer(t['b'],0,20)
            _require((name,t['a'],t['b']) not in source_terms,'unique original source monomial')
            source_terms[name,t['a'],t['b']]=_rational(t['coefficient'],meter)
    selected={};expected_refs=[];seen_sources=set()
    for term in prefix_result['terms']:
        key=term['key'];source_key=(key['mode'],key['a'],key['b'])
        _require(source_key in source_terms and term['source_scalar']==modes[key['mode']]['coefficient'] and
                 _rational(term['inverse_coefficient'],meter)==source_terms[source_key],'source sign and inverse coefficient binding')
        _require(source_key not in seen_sources,'unique current source term')
        seen_sources.add(source_key)
        depth=_integer(term['selected_depth'],0,key['a'])
        alt=term['alternatives'][depth]
        _require(alt['depth']==depth and type(alt['pieces']) is list and len(alt['pieces'])==depth+1,
                 'complete selected current source depth')
        recovered=set()
        for i,piece in enumerate(alt['pieces']):
            ref=dict(source_key=key,depth=depth,piece=i);rkey=_ref_key(ref)
            _require(rkey not in selected,'unique selected source pieces')
            mode=modes[key['mode']];expr=piece['expression']
            _require(type(expr) is list and expr==sorted(expr),'selected binomial expression')
            j=expr.count('E')
            _require(0<=j<=depth and j not in recovered,'each selected binomial and drift term once')
            recovered.add(j)
            base=['A']*mode['p']+['B']*mode['q']+['S']*key['b']+['R']*(key['a']-depth)
            if mode['positive_shift'] is not None:base+=['K']
            expected_expr=sorted(base+['E']*j+['C','O']*(depth-j))
            coefficient=_rational(piece['coefficient'],meter)
            _require(expr==expected_expr and coefficient==source_terms[source_key]*comb(depth,j)*(-1)**(depth-j),
                     'selected source binomial recovery and complete compensating drift')
            ident=piece['prefix_proof']
            _require(type(ident) is int and ident in checked_nodes and checked_nodes[ident][:2]==(tuple(expr),'prefix'),
                     'independently replayed matching prior prefix proof')
            _,_,cost=checked_nodes[ident]
            scalar=Q(5) if term['source_scalar']=='-R_u' else Q(9,2)
            _require(piece['energy']==_energy(scalar*abs(coefficient)*cost[2],cost[0],cost[1],meter),
                     'prior selected piece energy and paid flag replay')
            selected[rkey]=(piece,term['source_scalar'],mode['positive_shift'])
            if piece['energy']['uniform_constant'] is None:expected_refs.append(rkey)
            meter.charge(10)
    _require(seen_sources==set(source_terms),'complete inherited source modes and unit rows')
    _require(type(remaining_refs) is list,'complete current remaining refs')
    refs=[_ref_key(ref) for ref in remaining_refs]
    _require(len(set(refs))==len(refs) and set(refs)==set(expected_refs),'all and only current unpaid source pieces')
    current=[];eligible=[]
    for index,(ref,rkey) in enumerate(zip(remaining_refs,refs)):
        piece,scalar,shift=selected[rkey];expression=piece['expression']
        _require(type(expression) is list and expression==sorted(expression) and
                 all(type(f) is str and f in 'ABCEKORS' for f in expression),'complete sorted current expression')
        coefficient=_rational(piece['coefficient'],meter)
        _require(coefficient!=0,'nonzero source coefficient')
        current.append(dict(reference=ref,piece=piece,scalar=scalar,shift=shift))
        if expression.count('K')==1 and set(expression)<={'A','B','C','K'}:
            _require(shift is not None,'kernel shift read from source mode')
            a=_rational(shift,meter)
            _require(0<=a<1,'integral theorem kernel domain')
            _require(a==Q(1,3),'prior certified K registry has the actual source shift1/3')
            factors=expression.copy();factors.remove('K')
            eligible.append(dict(id=index,reference=ref,source_scalar=scalar,coefficient=piece['coefficient'],
                factors=factors,kernel_shift=shift,old_energy=piece['energy']))
    _require(len(eligible)<=12,'bounded exhaustive subset language')
    meter.live(100*len(selected)+100*len(eligible)+4096)
    return alpha,gamma,current,eligible


def _profile_certificates(eligible,meter):
    shifts=sorted({p['kernel_shift'] for p in eligible},key=Q)
    expected=[]
    for shift in shifts:
        leading=1-Q(shift)
        for theta in PROFILES:
            supported=theta==leading
            expected.append(dict(kernel_shift=shift,theta=str(theta),
                status='supported' if supported else 'unmatched_power_profile',
                leading_power=str(leading),leading_coefficient=str(1/leading),
                solved_multiplier=str(1/leading) if supported else None,
                universal_remainder_constant=str(1/leading) if supported else None))
            meter.charge(20)
    return expected


def _signed_moment(piece,meter):
    coefficient=_rational(piece['coefficient'],meter)
    if piece['source_scalar']=='-R_u':coefficient=-coefficient;ru=1
    else:coefficient*=Q(9,2)*(1 if piece['source_scalar']=='beta' else -1);ru=0
    return tuple(piece['factors'].count(f) for f in ('A','B','C'))+(ru,),coefficient


def _audit_alternative(mask,eligible,profiles,alpha,gamma,alternative,meter):
    _require(type(alternative) is dict,'subset certificate')
    supported={p['kernel_shift']:Q(p['theta']) for p in profiles if p['status']=='supported'}
    chosen=[piece for position,piece in enumerate(eligible) if (mask//2**position)%2]
    unchanged=[piece for position,piece in enumerate(eligible) if not (mask//2**position)%2]
    if any(piece['kernel_shift'] not in supported for piece in chosen):
        _require(alternative==dict(mask=mask,status='unsupported_power_profile'),'retain unsupported subset without a disproof claim')
        return None
    drift_terms={};remainders=[]
    for piece in chosen:
        theta=supported[piece['kernel_shift']]
        powers,coefficient=_signed_moment(piece,meter)
        p,q,r,ru=powers
        prefix_c=abs(coefficient)/theta*3**q*2**r*5**ru
        prefix_e=p*alpha+q*gamma/3
        remainders.append(dict(eligible_id=piece['id'],theta=str(theta),
            definition='signed K*h minus its complete signed moment/theta times J_theta',
            prefix_bound=dict(constant=str(prefix_c),power=str(prefix_e),log_degree=0),
            energy=_energy(prefix_c,prefix_e,0,meter)))
        polynomial=drift_terms.setdefault(theta,{})
        polynomial[powers]=polynomial.get(powers,Q(0))+coefficient/theta
        meter.charge(80)
    drifts=[]
    for theta,terms in sorted(drift_terms.items()):
        nonzero={powers:coefficient for powers,coefficient in terms.items() if coefficient}
        if not nonzero:continue
        polynomial=[dict(powers=list(powers),coefficient=str(coefficient)) for powers,coefficient in sorted(nonzero.items())]
        factor_costs=(_finite_moment_bound(theta,alpha),_finite_moment_bound(theta+Q(2,3),gamma),
                      (Q(2),Q(0),0),(Q(5),Q(0),0))
        constants=[];exponents=[];degrees=[]
        for powers,coefficient in sorted(nonzero.items()):
            c=abs(coefficient);e=Q(0);k=0
            for index,count in enumerate(powers):
                fc,fe,fk=factor_costs[index]
                c*=fc**count;e+=fe*count;k+=fk*count
                meter.charge(20)
            constants.append(c);exponents.append(e);degrees.append(k)
        prefix_c=sum(constants,Q(0));prefix_e=theta+max(exponents);prefix_k=max(degrees)
        drifts.append(dict(theta=str(theta),polynomial=polynomial,
            prefix_bound=dict(constant=str(prefix_c),power=str(prefix_e),log_degree=prefix_k),
            energy=_energy(prefix_c,prefix_e,prefix_k,meter)))
    unpaid=[p['old_energy'] for p in unchanged if p['old_energy']['uniform_constant'] is None]
    unpaid.extend(r['energy'] for r in remainders if r['energy']['uniform_constant'] is None)
    unpaid.extend(d['energy'] for d in drifts if d['energy']['uniform_constant'] is None)
    worst=max([(Q(0),0)]+[(_rational(e['power'],meter),e['log_degree']) for e in unpaid])
    score=(worst[0],worst[1],len(unpaid),len(chosen),mask)
    expected=dict(mask=mask,status='exact_decomposition_with_bound_certificates',
        centered_ids=[p['id'] for p in chosen],unchanged_ids=[p['id'] for p in unchanged],
        remainders=remainders,joint_drifts=drifts,score=[str(score[0]),*score[1:]],
        comparison_scope='eligible finite-factor subsum only; other full-core pieces are unchanged',
        whole_signed_bound_proved=False)
    _require(alternative==expected,'exact joint recovery, complete moments, source signs, and bound costs')
    return score


def verify_search(row,prefix_result,remaining_refs,result,meter):
    alpha,gamma,current,eligible=_current_pieces(row,prefix_result,remaining_refs,meter)
    _require(type(result) is dict and set(result)=={'schema','geometry_id','alpha','gamma','remaining_refs','eligible',
        'profile_trials','alternatives','selected_mask','statistics','whole_signed_bound_proved','RH_proved',
        'moment_variable_order','operator_definition'},'exact joint-search schema')
    _require(result['schema']=='core-joint-power-search-v1' and type(result['geometry_id']) is int and
             result['geometry_id']==row['id'] and result['alpha']==row['alpha'] and result['gamma']==row['gamma'],
             'joint search geometry binding')
    _require(result['moment_variable_order']==['m_theta_A','m_theta_B','c_U','R_u'] and
             result['operator_definition']=='J_theta(n)=n^theta-(n-1)^theta; complete finite moments multiply under Dirichlet convolution',
             'complete moment variables and prefix increment definition')
    _require(result['whole_signed_bound_proved'] is False and result['RH_proved'] is False,'signed core and RH remain open')
    _require(result['remaining_refs']==remaining_refs and result['eligible']==eligible,'complete eligible current source subsum')
    profiles=_profile_certificates(eligible,meter)
    _require(result['profile_trials']==profiles,'exhaustive compatible and incompatible power equations')
    alternatives=result['alternatives']
    _require(type(alternatives) is list and len(alternatives)==2**len(eligible),'every subset including no change')
    scores=[]
    for mask,alternative in enumerate(alternatives):
        score=_audit_alternative(mask,eligible,profiles,alpha,gamma,alternative,meter)
        if score is not None:scores.append(score)
    selected=min(scores)[-1]
    _require(type(result['selected_mask']) is int and result['selected_mask']==selected,'certified subset optimum')
    alt=alternatives[selected]
    statistics=dict(eligible_pieces=len(eligible),profile_trials=len(profiles),
        rejected_profiles=sum(p['status']!='supported' for p in profiles),subsets=len(alternatives),
        selected_centered=len(alt['centered_ids']),selected_joint_drifts=len(alt['joint_drifts']),
        selected_paid_remainders=sum(r['energy']['uniform_constant'] is not None for r in alt['remainders']))
    _require(result['statistics']==statistics,'exact exhaustive-search accounting')
    meter.live(200*len(alternatives)+100*len(current)+4096)
    return dict(verified=True,geometry_id=row['id'],eligible_pieces=len(eligible),subsets=len(alternatives),
        selected_mask=selected,exact_signed_recovery_verified=True,complete_finite_moments_verified=True,
        selected_paid_remainders=statistics['selected_paid_remainders'],whole_signed_bound_proved=False,RH_proved=False)


def verify_reduction(parent_prefix_reduction,construction,result,reduction,meter):
    parent=parent_prefix_reduction
    _require(parent['geometry_id']==result['geometry_id'] and parent['remaining_signed_pieces']==result['remaining_refs'],
             'exact inherited current signed vector')
    _require(parent.get('transport_error_retained') is True and parent.get('all_remaining_crosses_retained') is True and
             parent.get('whole_signed_bound_proved') is False and parent.get('original_fixed_recurrence_discharged') is False,
             'retained prior transport, crosses, and open fixed recurrence')
    selected=result['alternatives'][result['selected_mask']]
    by_id={piece['id']:piece for piece in result['eligible']}
    centered={_ref_key(by_id[i]['reference']) for i in selected['centered_ids']}
    unchanged=[ref for ref in result['remaining_refs'] if _ref_key(ref) not in centered]
    paid=[];unpaid_remainders=[];unpaid_drifts=[]
    for remainder in selected['remainders']:
        constant=remainder['energy']['uniform_constant']
        if constant is None:unpaid_remainders.append(remainder['eligible_id'])
        else:paid.append(dict(kind='remainder',eligible_id=remainder['eligible_id'],uniform_energy_constant=constant))
    for drift in selected['joint_drifts']:
        constant=drift['energy']['uniform_constant']
        if constant is None:unpaid_drifts.append(drift['theta'])
        else:paid.append(dict(kind='drift',theta=drift['theta'],uniform_energy_constant=constant))
    channel=_abel(construction,meter)
    _require(_rational(parent['channel_abel_constant'],meter)==channel,'same verified inherited Abel cost')
    degree=parent['goal']['p']
    _require(_rational(degree,meter)>=0 and parent['goal']['status']=='open' and parent['goal']['same_finite_constant'] is True,
             'nonnegative inherited all-scale target degree')
    total=len(paid)*channel*sum((_rational(piece['uniform_energy_constant'],meter) for piece in paid),Q(0))
    expected=dict(schema='core-joint-power-reduction-v1',parent_obligation_id=parent['parent_obligation_id'],
        geometry_id=result['geometry_id'],selected_mask=result['selected_mask'],newly_paid=paid,
        remaining_source_refs=unchanged,remaining_centered_remainders=unpaid_remainders,
        remaining_joint_drifts=unpaid_drifts,channel_abel_constant=str(channel),combined_paid_constant=str(total),
        exact_split='Z_old=P_new+Z_new; Z_new retains all untouched pieces, unpaid centered remainders, complete joint drifts, and -e where e=f-g',
        recovery='S_old<=2*S_new+2*C_new; S_new<=2*S_old+2*C_new',
        goal=dict(expression='S_new(X)<=C*(1+log2X)^p for every dyadicX>=1',p=degree,status='open',same_finite_constant=True),
        full_finite_moments_retained=True,all_remaining_crosses_retained=True,transport_error_retained=True,
        original_fixed_recurrence_discharged=False,whole_signed_bound_proved=False,RH_proved=False)
    _require(reduction==expected,'complete paid/unpaid signed join, Cauchy count, inherited target and transport')
    return dict(verified=True,geometry_id=result['geometry_id'],newly_paid=len(paid),
        remaining_source_pieces=len(unchanged),remaining_centered_remainders=len(unpaid_remainders),
        remaining_joint_drifts=len(unpaid_drifts),channel_abel_constant=str(channel),combined_paid_constant=str(total),
        whole_signed_bound_proved=False,RH_proved=False)
