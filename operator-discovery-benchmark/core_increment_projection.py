"""Proof-guided synthesis of complete coarse energy and paid local variation.

The candidate is an orthogonal block projection of a generated storage AST.
Proof rules pay its detail; they do not bound the full signed coarse moment.
All existing prefixes/log banks and internal cross terms remain complete.
"""
from fractions import Fraction as Q
from flint import arb

MESH_POWERS=('1/6','1/3','1/2','2/3','5/6','1')
K=Q(37,2)


def rational(s):
    if type(s) is not str or len(s)>128:raise ValueError('canonical rational string')
    try:q=Q(s)
    except (ValueError,ZeroDivisionError) as e:raise ValueError('rational') from e
    if str(q)!=s:raise ValueError('canonical rational')
    return q


def real(s):
    q=rational(s);return arb(q.numerator)/q.denominator


def validate(program):
    if type(program) is not dict or set(program)!={'auxiliary','mix','reserve'}:raise ValueError('complete storage AST')
    a,w=rational(program['mix']),rational(program['reserve'])
    if w<=0:raise ValueError('strict positive reserve')
    aux=program['auxiliary']
    if aux is None:
        if a or w!=1:raise ValueError('canonical baseline')
    elif type(aux) is not dict or set(aux)!={'kind','alpha'} or aux['kind'] not in ('log_bank','half_delay','transport_error') or not 0<=rational(aux['alpha'])<=Q(1,3):
        raise ValueError('reviewed auxiliary derivative domain')


def mesh(X,power,H):
    r=rational(power)
    if type(X) is not int or X<1 or X&(X-1) or 2*X-1>H:raise ValueError('complete dyadic source block')
    if not 0<r<=1:raise ValueError('mesh exponent in(0,1]')
    return 1<<(r.numerator*(X.bit_length()-1)//r.denominator)


def prepare(state,program,meter):
    validate(program);H=state['H']
    if type(H) is not int or H<1 or (H+1)&H:raise ValueError('complete closed dyadic horizon')
    for key in ('g','G','Bg','D'):
        if len(state[key])!=H+1 or not state[key][0].is_zero() or any(not v.is_finite() for v in state[key]):
            raise ValueError('full finite source prefixes and zero dummy')
    a,w=real(program['mix']),real(program['reserve']);aux=program['auxiliary']
    U=[arb(0)]*(H+1);V=[arb(0)]*(H+1)
    for n in range(1,H+1):
        if aux is not None:
            if aux['kind']=='log_bank':v=state['Bg'][n]/arb(2*n).log()
            elif aux['kind']=='half_delay':v=state['G'][n//2]
            else:v=state['D'][n]
            alpha=rational(aux['alpha']);V[n]=v/arb(n).root(alpha.denominator)**alpha.numerator
        U[n]=state['G'][n]+a*V[n];meter.charge(180 if aux else 12)
    # Prefix sums of values, complete squared values and local derivative
    # moments let every projected block be evaluated without pair tables.
    names=('U','Q','energy','gradient0','gradient1','gradient2')
    sums={name:[arb(0)]*(H+1) for name in names}
    for n in range(1,H+1):
        d=(U[n]-U[n-1])**2+w*(V[n]-V[n-1])**2
        values=(U[n],V[n],U[n]**2+w*V[n]**2,d,n*d,n*n*d)
        for name,value in zip(names,values):sums[name][n]=sums[name][n-1]+value
        meter.charge(65)
    meter.live(15*(H+1)+4096)
    return dict(H=H,U=U,Q=V,weight=w,program=program,sums=sums)


def project(prepared,X,mesh_power,meter):
    H=prepared['H'];L=mesh(X,mesh_power,H);s=prepared['sums'];w=prepared['weight']
    full=(s['energy'][2*X-1]-s['energy'][X-1])/X**2
    coarse=arb(0);path=arb(0);means=[]
    for lo in range(X,2*X,L):
        hi=lo+L;u=(s['U'][hi-1]-s['U'][lo-1])/L;q=(s['Q'][hi-1]-s['Q'][lo-1])/L
        coarse+=L*(u*u+w*q*q)
        d0,d1,d2=(s[name][hi-1]-s[name][lo] for name in ('gradient0','gradient1','gradient2'))
        path+=(-d2+(2*lo+L)*d1-lo*(lo+L)*d0)/2
        means.append(dict(start=lo,stop=hi,U_mean=u,Q_mean=q));meter.charge(65)
    coarse/=X**2;path/=X**2
    if L==1:coarse=full;detail=arb(0);path=arb(0)
    else:detail=full-coarse
    identity=full-coarse-detail
    return dict(X=X,L=L,mesh_power=mesh_power,cell_means=means,full_storage=full,coarse_storage=coarse,detail_storage=detail,
        path_bound=path,identity_residual=identity,
        path_comparison='pass' if detail<=path else 'fail' if detail>path else 'unresolved')


def certificate(program,mesh_power,meter):
    validate(program);r=rational(mesh_power)
    if not 0<r<=1:raise ValueError('mesh exponent in(0,1]')
    a,w=rational(program['mix']),rational(program['reserve']);aux=program['auxiliary']
    if aux is None:b=None;C=2*K*K
    else:
        alpha=rational(aux['alpha']);b=2*alpha+(4 if aux['kind']=='log_bank' else 0)
        C=4*K*K*(1+(2*a*a+w)*(1+b*b))
    e=2*r-1;bounded=e<0;paid=e<=0
    effective=0 if bounded else 3 if paid else None
    constant=C*96/(-e)**3 if bounded else None
    meter.charge(180)
    return dict(rule='orthogonal_cell_projection_with_paid_discrete_derivative',source_coefficient_constant=str(K),
        coefficient_majorant_premise='|g(n)| and |f(n)-g(n)| <= (37/2)*d2(n), full unit and all integers',
        coefficient_majorant_premise_verified=False,program=program,mesh_power=mesh_power,
        auxiliary_derivative_factor=None if b is None else str(b),
        detail_constant=str(C),detail_power=str(e),raw_log_degree=3,cofinal_recovery=paid,bounded_detail=bounded,
        bounded_detail_constant=None if constant is None else str(constant),effective_detail_log_degree=effective,
        full_exact_split='A(X)=S(X)+V(X), S=E_(P U)+w E_(P Q), V=E_((I-P)U)+w E_((I-P)Q)>=0',
        path_identity='sum_cell(y-mean)^2=(1/L)sum_i<j(y_i-y_j)^2 <=sum_t t(L-t)/2*(Delta y_t)^2',
        source_rules=['pointwise d2(n)^2<=d4(n)','sum_(n<=x)d4(n)<=x*(1+logx)^3','weighted full-prefix derivative product rule'],
        paid_detail='V(X)<=detail_constant*X^detail_power*(1+log2X)^3 for every dyadic X>=1',
        bounded_detail_rule='(1+j)^3*2^(-delta*j)<=96/delta^3, delta=1-2r in(0,1)',
        increment_identity='Delta_rho A(X)=Delta_rho S(X)+V(2X)-rho V(X)',
        increment_upper='Delta_rho A(X)<=Delta_rho S(X)+paid_detail(2X), rho>=0',
        full_source_histories_retained=True,coarse_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False)


def generate(obligations,meter):
    """Consume actual open storage lemmas; no fitted constant or score is used."""
    rows=[]
    for ob in obligations:
        if ob['schema']!='detector-generated-core-control-obligation-v1' or ob['status']!='open_uniform_increment' or ob['uniform_premise_established']:
            raise ValueError('explicit unresolved complete storage input')
        for r in MESH_POWERS:
            cert=certificate(ob['storage_program'],r,meter)
            rows.append(dict(id=len(rows),parent_obligation=ob['id'],transport_program=ob['transport_program'],
                storage_program=ob['storage_program'],mesh_power=r,certificate=cert,
                status='paid_detail_open_coarse' if cert['cofinal_recovery'] else 'unpaid_detail_power',
                previous_uniform_increment_still_open=True))
    return rows


def proof_select(rows):
    """Exact partition inclusion, then the uniform log cost, decides geometry."""
    chosen=[]
    for parent in dict.fromkeys(row['parent_obligation'] for row in rows):
        eligible=[r for r in rows if r['parent_obligation']==parent and r['certificate']['cofinal_recovery']]
        for lane,max_log in (('preserve_log_degree_two',2),('allow_any_fixed_polylog',None)):
            options=[r for r in eligible if max_log is None or r['certificate']['effective_detail_log_degree']<=max_log]
            if not options:continue
            winner=max(options,key=lambda r:rational(r['mesh_power']))
            chosen.append(dict(winner,lane=lane,selection_reason='nested orthogonal projections reduce coarse storage; choose largest mesh with separately paid recovery'))
        analytic=[r for r in rows if r['parent_obligation']==parent and r.get('analytic_recovery',{}).get('admitted')]
        if analytic:
            winner=max(analytic,key=lambda r:rational(r['mesh_power']))
            chosen.append(dict(winner,lane='source_specific_analytic_RH_bridge',
                selection_reason='largest nested mesh with detail holomorphic throughout Re>1/2 and a separately checked complete-source RH bridge'))
    return chosen


def coarse_pole_guard(row,witness_verified,meter):
    """Compile the zero-cell-mean Mellin strip, not an energy-bound shortcut."""
    r=rational(row['mesh_power']);theta=rational(row['transport_program']['theta'])
    detail_power=2*r-1
    absolute_mass_power=Q(3,2)+detail_power/2
    boundary=absolute_mass_power+r-2
    known=bool(witness_verified and boundary<Q(1,2) and theta<=Q(5,6))
    meter.charge(150)
    return dict(rule='zero_cell_mean_preserves_original_critical_pole',
        prefix_detail_annular_absolute_mass_power=str(absolute_mass_power),
        detail_mellin_holomorphic_Re_s_greater_than=str(boundary),
        mean_zero_scope='sum_(n in each COMPLETE cell)(G(n)-mean_cellG)=0; unit-cell step extension',
        analytic_argument='subtract weight at cell start, use derivative of x^(-s-1); compact-uniform annular series',
        original_core_pole_witness_verified=bool(witness_verified),
        transport_boundary_argument='theta5/6 error has Mellin radial growth O(delta^-1), so cannot cancel the original double pole',
        coarse_minimum_log_degree=2 if known else None,
        stronger_holomorphy_is_not_automatically_a_critical_energy_bound=True,
        all_scale_coarse_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False)


def weak_fact_countermodels(program,meter):
    """Disprove an inference from weak facts, NEVER the actual-core claim."""
    validate(program);a,w=rational(program['mix']),rational(program['reserve']);c=1+a*a/w
    rows=[]
    for m in range(2,17):
        start=1
        while start<24*m:start*=2
        rows.append(dict(cofactor=m,coefficient='h(1)=c in(-10,0); h(n)=1 if m divides n and n>=2m; zero otherwise',
            complete_prefix='H(n)=c+floor(n/m)-1 for n>=2m',
            satisfies=['same allowed full unit range','|h(n)|<=(37/2)d2(n)','h(p)=0 for EVERY actual prime p',
                       'all proved projection variance bounds'],
            prefix_lower_bound='H(n)>=n/(2m) for every n>=24m',
            projected_storage_lower_constant=str(1/(4*m*m*c)),
            projected_storage_lower_bound='S_h(X)>=projected_storage_lower_constant*X for every dyadicX>=start',
            start=start,weak_facts_cannot_prove_cofinal_coarse_control=True,
            complete_actual_source_AST_satisfied=False,actual_core_bound_disproved=False,RH_disproved=False))
        meter.charge(100)
    return rows


def source_holomorphy_bridge(source,scalars,meter):
    """A meromorphic-source implication; no unproved coarse bound is supplied.

Choose a hypothetical zero within the smallest positive shift of the
supremum real part of all zeros. Every shifted factor is then nonzero,
and a unique leading inverse zeta(s) power cannot cancel there.
"""
    terms=source['terms'];orders=[];positive=[]
    for term in terms:
        c=scalars[term['coefficient']]
        if not isinstance(c,arb) or not c.is_finite() or c.contains(0):
            return dict(verified=False,reason='all finite nonzero scalar coefficients need certificates')
        order=Q(0)
        for shift,exponent in term['zeta_factors']:
            s,e=rational(shift),rational(exponent)
            if s<0 or e.denominator!=1:
                return dict(verified=False,reason='negative shifts or fractional zeta powers require other rules')
            if s==0:order-=e
            elif e:positive.append(s)
            meter.charge(60)
        orders.append(int(order))
    if not orders or max(orders)<=0 or orders.count(max(orders))!=1:
        return dict(verified=False,reason='no unique dominant inverse zeta(s) power')
    return dict(verified=True,rule='rightmost_zero_supremum_and_unique_inverse_order',
        zero_orders_per_multiplicity=orders,leading_term=terms[orders.index(max(orders))]['name'],
        smallest_positive_shift=str(min(positive)) if positive else None,
        premise='the COMPLETE source Dirichlet series is holomorphic throughout Re(s)>1/2',
        proof='if B=sup Re(nontrivial zero)>1/2, choose Re(rho)>max(1/2,B-smallest_positive_shift); all positive shifts lie right ofB, so the unique leading inverse order gives an uncanceled pole',
        arbitrary_zero_multiplicity=True,initial_series_domain='Re(s)>1, followed by uniqueness of meromorphic continuation',
        conclusion='RH, conditional on the holomorphy premise; reflection symmetry handles the other half of the critical strip',
        implies_original_critical_moment_without_additional_growth_theorem=False,
        uniform_holomorphy_premise_established=False,whole_signed_bound_proved=False,RH_proved=False)


def analytic_recovery(row,bridge,meter):
    r=rational(row['mesh_power']);theta=rational(row['transport_program']['theta']);boundary=2*r-1
    admitted=bool(bridge['verified'] and boundary<Q(1,2) and theta<=Q(5,6))
    meter.charge(100)
    return dict(admitted=admitted,detail_holomorphy_boundary=str(boundary),source_bridge_verified=bridge['verified'],
        proof_dependencies=['cofinal bound for complete coarseS: OPEN','E_(PG)<=(1+a²/w)S',
            'Mellin integral of PG holomorphic Re>1/2','zero-cell-mean detail holomorphic Re>2r-1',
            'paid transport error Mellin integral holomorphic Re>1/2','complete source holomorphy forces RH'],
        original_critical_energy_recovery_claimed=False,coarse_bound_proved=False,RH_proved=False)


def obligation(row):
    cert=row['certificate'];a,w=rational(row['storage_program']['mix']),rational(row['storage_program']['reserve'])
    error=2*rational(row['transport_program']['theta'])-Q(5,3)
    return dict(schema='projected-core-increment-obligation-v1',parent_obligation=row['parent_obligation'],
        transport_program=row['transport_program'],storage_program=row['storage_program'],mesh_power=row['mesh_power'],
        projection='global fixed annular cells; full U,Q averaged, no prefix restart; all internal signed crosses retained',
        exact_storage_split='A=S+V, V>=0 with a checked derivative bound; energy payment depends on the selected recovery route',
        exact_increment_split='A(2X)-rho A(X)=S(2X)-rho S(X)+V(2X)-rho V(X)',
        detail_certificate=cert,source_majorant_binding_required=True,
        recovery_route=row.get('lane'),analytic_recovery=row.get('analytic_recovery'),
        open_target=dict(expression='S(2X)-rho*S(X)',required='<=C*(1+log2X)^k at EVERY dyadicX>=1',
            constant='one fixed finite C, not fitted by this stage',rho='1/2',log_power='2',uniform_premise_established=False),
        original_recovery=dict(storage_factor=str(2*(1+a*a/w)),transport_error_constant='50',transport_error_power=str(error),
            expression='E_F<=storage_factor*(S+paid_detail)+50X^transport_error_power',
            conditional_original_log_degree=max(2,cert['effective_detail_log_degree']) if cert['cofinal_recovery'] else None),
        old_fixed_C_claim_not_discharged=True,dependency_cycle=False,coarse_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False)
