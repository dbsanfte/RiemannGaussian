"""Independent rational multiplier/PSD and whole-source relation replay.

No producer or symbolic solver is imported. Scalar prices are checked
separately; a positive quadratic certificate can retain unpaid arithmetic.
"""
from fractions import Fraction as Q

import check_arithmetic_prefix_relations as RELATIONS


def matrix(data):
    if type(data) is not list or not data or len(data)>12:
        raise ValueError('nonempty bounded matrix')
    if type(data[0]) is not list or not 1<=len(data[0])<=12:
        raise ValueError('bounded nonempty matrix width')
    width=len(data[0]);rows=[]
    for row in data:
        if type(row) is not list or len(row)!=width:raise ValueError('rectangular matrix')
        result=[]
        for value in row:
            if type(value) is not str or len(value)>2500:raise ValueError('rational text')
            q=Q(value)
            if str(q)!=value:raise ValueError('canonical rational')
            result.append(q)
        rows.append(result)
    return rows


def psd(data):
    a=matrix(data);n=len(a)
    if any(len(row)!=n for row in a) or any(a[i][j]!=a[j][i] for i in range(n) for j in range(n)):
        raise ValueError('symmetric square form')
    pivots=[]
    while a:
        if any(a[i][i]<0 for i in range(len(a))):raise ValueError('negative Schur diagonal')
        pivot=next((i for i in range(len(a)) if a[i][i]>0),None)
        if pivot is None:
            if any(x for row in a for x in row):raise ValueError('zero diagonal with nonzero cross')
            break
        if pivot:
            a[0],a[pivot]=a[pivot],a[0]
            for row in a:row[0],row[pivot]=row[pivot],row[0]
        value=a[0][0];pivots.append(str(value))
        a=[[a[i][j]-a[i][0]*a[0][j]/value for j in range(1,len(a))] for i in range(1,len(a))]
    return dict(PSD=True,positive_Schur_pivots=pivots)


def verify_quadratic(form,relations,certificate):
    if certificate.get('status')!='exact_PSD_modulo_relations':raise ValueError('positive certificate required')
    if certificate.get('form')!=form or certificate.get('relations')!=relations:
        raise ValueError('bound to the requested form and complete relation')
    target=matrix(form);L=matrix(relations);P=matrix(certificate['PSD']);Y=matrix(certificate['multipliers'])
    n=len(target)
    if len(P)!=n or any(len(row)!=n for row in target+P+L+Y) or len(Y)!=len(L):
        raise ValueError('complete matching dimensions')
    for i in range(n):
        for j in range(n):
            if target[i][j]!=P[i][j]+sum((L[k][i]*Y[k][j]+Y[k][i]*L[k][j] for k in range(len(L))),Q(0)):
                raise ValueError('false exact relation-multiplier identity')
    positivity=psd(certificate['PSD'])
    if certificate.get('uniform_bound_proved') is not False:
        raise ValueError('quadratic identity alone does not pay its forcing')
    return dict(verified=True,positivity=positivity,forcing_still_requires_independent_prices=True)


def expected_whole_source_relation(source,relations_certificate):
    RELATIONS.verify_certificate(source,relations_certificate)
    groups={}
    for relation in relations_certificate['relations']:
        key=tuple(f['exponent'] for f in relation['rhs']['factors'])
        a,b=map(Q,relation['weight'])
        previous=groups.get(key,(Q(0),Q(0)));groups[key]=(previous[0]-a,previous[1]-b)
    groups={k:w for k,w in groups.items() if any(w)}
    return dict(source_binding=source,
        target='complete original prefix F(n)=sum_j W_j(n)',
        tail='T(n)=sum_j sum_(2<=d<=n)D_j(d)*W_j(floor(n/d))',
        forcing=[dict(power_factors=list(key),weight=list(map(str,weight))) for key,weight in sorted(groups.items())],
        identity='F+T+sum forcing=0',domain='every integer n>=1',
        all_floor_terms_and_source_channels=True,tail_status='OPEN')


def verify_whole_source_relation(source,relations_certificate,proposal):
    expected=expected_whole_source_relation(source,relations_certificate)
    if expected!=proposal:raise ValueError('complete source, unit, kernel-tail and forcing binding')
    return True


def verify_formal_witness(form,relations,vector):
    A=matrix(form);L=matrix(relations);v=[Q(x) for x in vector]
    if len(v)!=len(A) or any(len(row)!=len(v) for row in A+L) or any(sum((a*b for a,b in zip(row,v)),Q(0)) for row in L):
        raise ValueError('witness must obey admitted linear relations')
    value=sum((v[i]*A[i][j]*v[j] for i in range(len(v)) for j in range(len(v))),Q(0))
    if value>=0:raise ValueError('strict negative quadratic witness')
    return dict(verified=True,value=str(value),scope='finite multiplier grammar free-vector witness',
                actual_arithmetic_counterexample=False)


def verify_rhs_price(rhs, proposal, R_interval=('1','5')):
    """Independent integral/envelope proof with the whole block cost retained."""
    if proposal.get('rhs')!=rhs or proposal.get('R_interval')!=list(R_interval):
        raise ValueError('exact RHS and independently licensed scalar interval')
    low,high=map(Q,R_interval);a,b=map(Q,rhs['weight'])
    if low>high:raise ValueError('ordered scalar interval')
    ceiling=max(abs(a+b*low),abs(a+b*high))
    exponents=list(map(Q,rhs['power_factors']))
    common=dict(rhs=rhs,R_interval=list(R_interval),weight_ceiling=str(ceiling),
                norm='X^-2 sum_(X<=n<2X) value(n)^2',domain='every integer X>=1')
    if len(exponents)>1:
        expected=dict(**common,status='OPEN',reason='multiple power factors have no admitted price')
    else:
        logs=0
        if not exponents:
            rule='delta_prefix';constant=ceiling**2;power=Q(-1)
        else:
            e=exponents[0]
            if e<-1:
                rule='convergent_power_integral';constant=ceiling**2*(e/(e+1))**2;power=Q(-1)
            elif e==-1:
                rule='harmonic_integral';constant=4*ceiling**2;power=Q(-1);logs=2
            else:
                v=e+1;ceil_v=(v.numerator+v.denominator-1)//v.denominator
                rule='decreasing_power_integral' if e<0 else 'increasing_power_envelope'
                constant=ceiling**2*Q(2)**(2*ceil_v)/(v*v if e<0 else 1)
                power=1+2*e
        expected=dict(**common,status='PROVED',rule=rule,
                      energy=dict(constant=str(constant),power=str(power),log_power=logs),
                      subpower_eligible=power<=0)
    if proposal!=expected:raise ValueError('false complete all-integer RHS price or growth claim')
    return True


def _vector(data, size):
    row=matrix([data])[0]
    if len(row)!=size:raise ValueError('vector dimension')
    return row


def _unit(size,index):return ['1' if i==index else '0' for i in range(size)]


def _dot(a,b):return sum((x*y for x,y in zip(a,b)),Q(0))


def _rank(rows):
    a=matrix(rows);pivot=0
    for column in range(len(a[0])):
        found=next((r for r in range(pivot,len(a)) if a[r][column]),None)
        if found is None:continue
        a[pivot],a[found]=a[found],a[pivot]
        value=a[pivot][column];a[pivot]=[x/value for x in a[pivot]]
        for r in range(pivot+1,len(a)):
            value=a[r][column]
            a[r]=[x-value*y for x,y in zip(a[r],a[pivot])]
        pivot+=1
        if pivot==len(a):break
    return pivot


def verify_span_obstruction(target, relations, providers, obstruction):
    n=len(target);t=_vector(target,n);L=matrix(relations)
    v=_vector(obstruction['vector'],n)
    if any(len(row)!=n for row in L) or any(_dot(row,v) for row in L):
        raise ValueError('formal witness violates admitted complete relation')
    if _dot(t,v)!=1 or any(_dot(_vector(p['vector'],n),v) for p in providers):
        raise ValueError('formal witness must kill every provider and preserve the target')
    expected=dict(vector=obstruction['vector'],target_value='1',all_provider_values='0',
        relation_values='0',scope='this finite relation/template relaxation',
        excludes_all_nonnegative_forcing_weights=True,actual_arithmetic_counterexample=False)
    if obstruction!=expected:raise ValueError('formal span obstruction scope')
    return True


def verify_equivalence(target, auxiliary, relations, paid, claim):
    n=len(target)
    if claim.get('status')!='equivalent_subpower_obligation' or claim.get('new_bound_proved') is not False:
        raise ValueError('equivalence is not a proved bound')
    if claim.get('auxiliary')!=auxiliary or claim.get('paid_ids')!=[p['id'] for p in paid]:
        raise ValueError('exact auxiliary and provider linkage')
    for provider in paid:
        price=provider['price']
        if price['status']!='PROVED' or not price['subpower_eligible']:
            raise ValueError('equivalence recovery needs independently paid subpower terms')
    a=_vector([claim['target_coefficient']],1)[0]
    b=_vector(claim['paid_coefficients'],len(paid)) if paid else []
    c=_vector(claim['relation_coefficients'],len(relations)) if relations else []
    if not a:raise ValueError('nonzero target coefficient for two-way recovery')
    rows=[_vector(target,n)]+[_vector(p['vector'],n) for p in paid]+matrix(relations)
    values=[a]+b+c
    actual=[sum((v*row[i] for v,row in zip(values,rows)),Q(0)) for i in range(n)]
    if actual!=_vector(auxiliary,n):raise ValueError('false exact endpoint equivalence')
    return True


def verify_case(case, target, relations, providers):
    if case.get('target')!=target or case.get('relations')!=relations or case.get('providers')!=providers:
        raise ValueError('bound search target, source relation and providers must match')
    if case.get('whole_signed_bound_proved') is not False or case.get('RH_proved') is not False:
        raise ValueError('a case cannot assert a complete RH/source proof')
    if case['status']=='no_bound_in_provider_span':
        if case.get('coefficient_trials')!=0:raise ValueError('symbolic pre-search obstruction')
        verify_span_obstruction(target,relations,providers,case['obstruction'])
        return dict(span_obstruction_verified=True,actual_source_refuted=False)
    raw=case['search']
    if 'certificate' not in raw:
        raise ValueError('finite grid failure without a certificate is diagnostic only')
    coeffs=_vector(raw['coefficients'],len(providers));n=len(target)
    grid=[Q(x) for x in case['coefficient_grid']]
    if any(c<0 or c not in grid for c in coeffs):raise ValueError('allowed nonnegative coefficients')
    t=_vector(target,n);vectors=[_vector(p['vector'],n) for p in providers]
    form=[[str(sum((c*v[i]*v[j] for c,v in zip(coeffs,vectors)),Q(0))-t[i]*t[j])
           for j in range(n)] for i in range(n)]
    replay=verify_quadratic(form,relations,raw['certificate'])
    unpaid=[p['id'] for c,p in zip(coeffs,providers) if c and p['price']['status']!='PROVED']
    excess=[p['id'] for c,p in zip(coeffs,providers) if c and p['price']['status']=='PROVED'
            and not p['price']['subpower_eligible']]
    if raw['unpaid']!=unpaid or case['open_providers']!=unpaid or case['excess_growth_providers']!=excess:
        raise ValueError('all active forcing and growth debts must survive')
    meets=not(unpaid or excess)
    expected_status='conditional_energy_implication' if unpaid else 'proved_bound_with_excess_growth' if excess else 'proved_subpower_bound_for_case_target'
    if case['meets_subpower_target'] is not meets or case['status']!=expected_status:
        raise ValueError('paid bounds still have to meet the target growth')
    if case['coefficient_trials']!=len(raw['attempts']):raise ValueError('reported trial count')
    paid_terms=[dict(provider=p['id'],constant=str(c*Q(p['price']['energy']['constant'])),
                    power=p['price']['energy']['power'],log_power=p['price']['energy']['log_power'])
                for c,p in zip(coeffs,providers) if c and p['price']['status']=='PROVED']
    return dict(quadratic_verified=replay['verified'],paid_contributions=paid_terms,
                open_providers=unpaid,excess_growth_providers=excess,meets_subpower_target=meets)


def verify_floor_template(source, certificate, item):
    RELATIONS.verify_certificate(source,certificate)
    t=item['template'];channel=t['channel']
    if type(channel) is not int or not 0<=channel<len(certificate['relations']):raise ValueError('source channel')
    stencil=t['stencil'];previous=0
    for d,c in stencil:
        if type(d) is not int or d<=previous or d.bit_length()>4096 or not _vector([c],1)[0]:
            raise ValueError('complete canonical finite stencil')
        previous=d
    row=certificate['relations'][channel]
    expected=dict(schema='global-floor-multiplier-039-v1',source_binding=source,channel=channel,stencil=stencil,
        lhs=[dict(coefficient=c,outer_divisor=d,kernel=row['kernel'],inner_domain='1<=k<=floor(N/outer_divisor)',
                  prefix_argument='floor(N/(outer_divisor*k))',prefix_kind='weighted_channel') for d,c in stencil],
        rhs=[dict(coefficient=c,outer_divisor=d,argument='floor(N/outer_divisor)',prefix=row['rhs'],weight=row['weight'])
             for d,c in stencil],domain='every integer N>=0; prefix below1 zero',complete_tail_retained=True,
        identity_proved=True,uniform_bound_proved=False,
        scalar_scope='formal affine R identity; actual bound requires fixed exact source normalization')
    if t!=expected:raise ValueError('complete all-N floor composition with RHS and unit')
    split=item['split'];cutoff=split['cutoff']
    if type(cutoff) is not int or cutoff<1:raise ValueError('positive cutoff')
    if split!=dict(identity=t,cutoff=cutoff,head_domain='1<=k<=min(cutoff,floor(N/outer_divisor))',
                   tail_domain='cutoff<k<=floor(N/outer_divisor)',tail_cost_status='OPEN',unit_retained=True,all_N=True):
        raise ValueError('complete split with unpaid tail')
    if not stencil or stencil[0]!=[1,'1']:raise ValueError('this inverse gate requires unit1')
    factors=row['kernel']['factors'];gate=item['finite_inverse']
    if not factors:
        expected_gate=(dict(status='delta_kernel',exact_inverse=True,scope='fixed finite inverse')
            if stencil==[[1,'1']] else dict(status='rejected',reason='delta kernel leaves extra nonzero stencil coefficients',
                                           exact_inverse=False,scope='fixed finite inverse'))
    else:
        expected_gate=dict(status='rejected',reason='fresh-prime coefficient strictly positive',
            support_max=max(d for d,c in stencil),prime_domain='every prime p>support_max',
            residual_prime_polynomial=[dict(coefficient='1',exponent=f['exponent']) for f in factors],
            proof='(U*D)(p)=U(1)D(p)=sum power factors>0',
            scope='fixed finite exact inverse only; moving support/approximate inverse not excluded')
    if gate!=expected_gate:raise ValueError('false finite-inverse gate')
    return True


def verify_search(source, certificate, proposal):
    if proposal.get('schema')!='complete-source-global-multiplier-search-v1' or proposal.get('source_binding')!=source:
        raise ValueError('complete search and source binding')
    joined=expected_whole_source_relation(source,certificate)
    verify_whole_source_relation(source,certificate,proposal['joined_relation'])
    dim=2+len(joined['forcing']);target=_unit(dim,0);tail=_unit(dim,1);L=[['1']*dim]
    if proposal['coordinate_order']!=['complete_original_prefix_F','complete_joined_tail_T']+['rhs_'+str(i) for i in range(dim-2)]:
        raise ValueError('source-generated coordinate meanings')
    if proposal['norm']!='X^-2 sum_(X<=n<2X) coordinate(n)^2, every integer X>=1':
        raise ValueError('all-scale original target norm')
    if proposal['source_parameter_requirement']!='fixed exact R, replayed separately by normalization guard':
        raise ValueError('exact scalar required for actual source')
    forcing=proposal['cases'][1]['providers']
    if len(forcing)!=len(joined['forcing']):raise ValueError('every RHS term retained')
    for i,(provider,rhs) in enumerate(zip(forcing,joined['forcing'])):
        if set(provider)!={'id','vector','price'} or provider['id']!='rhs_'+str(i) or provider['vector']!=_unit(dim,i+2):
            raise ValueError('exact forcing coordinate')
        verify_rhs_price(rhs,provider['price'])
    paid=[p for p in forcing if p['price']['status']=='PROVED' and p['price']['subpower_eligible']]
    tail_provider=dict(id='complete_joined_tail',vector=tail,price=dict(status='OPEN',meaning=joined['tail']))
    expected_cases=[('critical_paid_forcing',paid),('all_rhs_paid_but_growth_charged',forcing),
                    ('complete_tail_explicitly_unpaid',forcing+[tail_provider])]
    if len(proposal['cases'])!=len(expected_cases):raise ValueError('complete mandatory cases')
    replays=[]
    for case,(name,providers) in zip(proposal['cases'],expected_cases):
        if case['name']!=name:raise ValueError('case role')
        replays.append(dict(name=name,**verify_case(case,target,L,providers)))
    coefficients=proposal['rational_auxiliary_coefficients']
    if not coefficients or len(coefficients)!=len(set(coefficients)):raise ValueError('finite distinct rational schedule')
    for x in coefficients:_vector([x],1)
    expected_constructions=[(p,q) for p in forcing for q in coefficients]
    if len(proposal['auxiliary_cases'])!=len(expected_constructions):raise ValueError('declared auxiliary enumeration coverage')
    equivalents=0
    for case,(provider,value) in zip(proposal['auxiliary_cases'],expected_constructions):
        construction=dict(tail='complete_joined_tail',rhs_id=provider['id'],coefficient=value)
        vector=[str(Q(x)+Q(value)*Q(y)) for x,y in zip(tail,provider['vector'])]
        auxiliary=dict(id='tail_plus_'+value+'_'+provider['id'],vector=vector,
                       price=dict(status='OPEN',construction=construction))
        if case['construction']!=construction or case['name']!=auxiliary['id']:raise ValueError('exact auxiliary construction')
        replay=verify_case(case,target,L,paid+[auxiliary])
        claim=case['equivalent_obligation']
        recovery_rows=[p['vector'] for p in paid]+L
        rank=_rank(recovery_rows)
        expected_equivalence=(_rank(recovery_rows+[target])>rank and
            _rank(recovery_rows+[vector])>rank and
            _rank(recovery_rows+[target,vector])==rank+1)
        if (claim is not None)!=expected_equivalence:
            raise ValueError('complete independent endpoint-equivalence detection')
        if claim is not None:
            verify_equivalence(target,vector,L,paid,claim);equivalents+=1
        replays.append(dict(name=case['name'],equivalent_obligation=claim is not None,**replay))
    calibration_replays=[]
    if len(proposal['calibrations'])!=len(certificate['relations']):raise ValueError('all source calibration targets')
    for row,case in zip(certificate['relations'],proposal['calibrations']):
        rhs=dict(power_factors=[f['exponent'] for f in row['rhs']['factors']],weight=row['weight'])
        if len(case['providers'])!=1:raise ValueError('one exact convolved RHS')
        provider=case['providers'][0];verify_rhs_price(rhs,provider['price'])
        if provider['id']!='channel_rhs_'+str(row['channel']) or provider['vector']!=['0','1']:
            raise ValueError('source convolved calibration provider')
        if case['channel']!=row['channel'] or case['calibration_only'] is not True or case['target_kind']!='complete convolved prefix, not original F':
            raise ValueError('calibration is a different target')
        calibration_replays.append(verify_case(case,['1','0'],[['1','-1']],[provider]))
    stencils=[[[1,'1']],[[1,'1'],[2,'-1']],[[1,'1'],[2,'-1/2'],[3,'1/257']]]
    expected_templates=[(row['channel'],stencil) for row in certificate['relations'] for stencil in stencils]
    if len(proposal['floor_templates'])!=len(expected_templates):raise ValueError('complete floor-template coverage')
    for item,(channel,stencil) in zip(proposal['floor_templates'],expected_templates):
        if item['template']['channel']!=channel or item['template']['stencil']!=stencil:
            raise ValueError('every declared source-channel/stencil pair')
        verify_floor_template(source,certificate,item)
    for flag in ('source_observations_used','whole_signed_bound_proved','RH_proved'):
        if proposal.get(flag) is not False:raise ValueError('search scope or proof flag')
    return dict(verified=True,case_replays=replays,calibration_replays=calibration_replays,
                exact_endpoint_equivalences=equivalents,floor_templates_verified=len(proposal['floor_templates']),
                whole_signed_bound_proved=False,RH_proved=False)
