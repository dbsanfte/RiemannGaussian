"""Invent periodic source preconditioners and search their uniform bound costs.

The mean-zero periodic coefficient is solved, as is the fractional hyperbola
cutoff. Removing every inverse-zeta factor cannot pass the RH relevance gate.
No observed source coefficients, fitted bound constants, or old search results
select a program.
"""
from collections import Counter
from copy import deepcopy
from fractions import Fraction as Q
from math import comb

import arithmetic_prefix_relations as SOURCE


def canonical(atoms):
    powers=Counter()
    for atom in atoms:
        powers[Q(atom['shift'])]+=1 if atom['kind']=='power' else -1
    return [dict(kind='power' if e>0 else 'mu',shift=str(s))
            for s,e in sorted(powers.items()) for _ in range(abs(e))]


def _key(atoms):return tuple((a['kind'],a['shift']) for a in canonical(atoms))


def family(source,meter=None):
    m=SOURCE.Meter() if meter is None else meter
    SOURCE.validate_source(source,m)
    channels=[]
    for i,c in enumerate(source['channels']):
        atoms=[dict(kind=a['kind'],shift=str(Q(a['shift'],source['lattice']))) for a in c['atoms']]
        channels.append(dict(index=i,atoms=canonical(atoms),weight=c['weight']))
    if len(channels)!=4:raise ValueError('four-mode normalized source family provider')
    r_values={Q(a['shift']) for c in channels for a in c['atoms'] if a['kind']=='power'}
    v_values={Q(a['shift']) for c in channels for a in c['atoms'] if a['kind']=='mu' and Q(a['shift'])>0}
    if len(r_values)!=1 or len(v_values)!=1:raise ValueError('one source power and shifted inverse')
    r,=r_values;v,=v_values;theta=1-r
    if not 0<r<Q(1,2) or not r<v<1:raise ValueError('provider domain0<r<1/2 and r<v<1')
    atom=lambda kind,shift:dict(kind=kind,shift=str(shift))
    wanted=[_key([atom('power',r),atom('mu',0),atom('mu',0)]),
            _key([atom('power',r),atom('mu',0),atom('mu',v)]),
            _key([atom('power',r),atom('mu',v)]),_key([atom('mu',0)])]
    roles=[]
    for key in wanted:
        found=[c for c in channels if _key(c['atoms'])==key]
        if len(found)!=1:raise ValueError('complete normalized source role match')
        roles.append(found[0])
    beta=Q(roles[0]['weight'][0])
    if beta<=0 or [c['weight'] for c in roles]!=[[str(beta),'0'],[str(-beta),'0'],['0','-1'],[str(-beta),'0']]:
        raise ValueError('exact source weights, scalar and unit')
    return dict(beta=str(beta),r=str(r),v=str(v),theta=str(theta),
                channel_roles=[c['index'] for c in roles])


def periodic(q):
    if type(q) is not int or not 2<=q<=4096:raise ValueError('bounded integer period')
    # For a(n)=1+c*1_(q divides n), mean1+c/q=0 determines c.
    coefficient=-Q(1)/Q(1,q)
    return dict(q=q,step_coefficients=[[1,'1'],[q,str(coefficient)]],
        solved_mean_equation=['1',str(Q(1,q))],periodic_mean='0',prefix_bound=str(q-1),
        prefix_exact='floor(x)-q*floor(x/q)',prefix_domain='every real x>=0',
        prefix_nonnegative=True,identity='mu*A_q=D_q',
        dirichlet_product='(1-q^(1-s))*zeta(s)',
        ordinary_moment_domain='Re(s)>0')


def hyperbola_search(theta,v):
    theta=Q(theta);v=Q(v)
    lines=[(Q(0),Q(1)),(theta,-theta)]
    candidates={theta}
    for i,(a,b) in enumerate(lines):
        for c,d in lines[i+1:]:
            if b!=d:
                x=(c-a)/(b-d)
                if 0<x<=theta:candidates.add(x)
    scored=[dict(alpha=str(x),power=str(max(a+b*x for a,b in lines))) for x in sorted(candidates)]
    selected=min(scored,key=lambda row:(Q(row['power']),Q(row['alpha'])))
    minimum=Q(selected['power'])
    # An absolutely convergent shifted contraction needs a STRICT exponent
    # margin. A slightly larger rational power can price a previously open
    # contraction. The subunit case is independently valid up to theta.
    exponents={minimum}
    boundary=1-v
    if v+minimum<=1 and boundary<Q(1,2):
        exponents.add((boundary+Q(1,2))/2)
    choices=[dict(power=str(s),admissible=s>=minimum and s<=theta and v+s>1)
             for s in sorted(exponents) if minimum<=s<=theta]
    admissible=[Q(row['power']) for row in choices if row['admissible']]
    sigma=min(admissible) if admissible else minimum
    return dict(lines=[dict(constant=str(a),slope=str(b)) for a,b in lines],
        domain='0<alpha<=theta',vertices=scored,
        selected_alpha=selected['alpha'],envelope_minimum=selected['power'],
        exponent_candidates=choices,selected_exponent=str(sigma),
        critical_shift_margin=str(v+sigma-1),
        subcritical=sigma<Q(1,2),absolute_shift_contraction=v+sigma>1,
        proof='minimum of convex piecewise-linear exponent envelope at a vertex',
        all_real_kernel_rule='hyperbola_with_complete_periodic_prefix_and_ordinary_tail',
        kernel_constant_per_prefix_bound=str(7/theta))


def transformed_channels(source,q,j):
    result=[]
    for i,c in enumerate(source['channels']):
        atoms=canonical([dict(kind=a['kind'],shift=str(Q(a['shift'],source['lattice']))) for a in c['atoms']])
        inverse_count=sum(a==dict(kind='mu',shift='0') for a in atoms)
        cancel=min(j,inverse_count)
        for _ in range(cancel):atoms.remove(dict(kind='mu',shift='0'))
        result.append(dict(source_channel=i,atoms=atoms,weight=c['weight'][:],
            periodic_copies=j-cancel,dilation_power=cancel,
            complete_prefix=True,unit_retained=True))
    return result


def dilation(q,power):
    return [[q**k,str(comb(power,k)*(-q)**k)] for k in range(power+1)]


def _step_bound(stencil):
    total=Q(0);ceiling=Q(0)
    for d,c in stencil:
        total+=Q(c);ceiling=max(ceiling,abs(total))
    return ceiling


def channel_price(channel,fam,q,hyperbola,scalar_bound):
    r,v,theta=map(Q,(fam['r'],fam['v'],fam['theta']))
    sigma=Q(hyperbola['selected_exponent']);R_bound=Q(scalar_bound)
    a,b=map(Q,channel['weight']);weight=abs(a)+R_bound*abs(b)
    atoms=channel['atoms'];periods=channel['periodic_copies'];degree=channel['dilation_power']
    power=lambda x:dict(kind='power',shift=str(x))
    mu=lambda x:dict(kind='mu',shift=str(x))
    common=dict(source_channel=channel['source_channel'],weight_ceiling=str(weight),
                full_dilation=dilation(q,degree),domain='every real x>0')
    if not atoms and periods==0:
        C=weight*_step_bound(dilation(q,degree));rho=Q(0);rule='complete_finite_step_prefix'
    elif not atoms and periods==1:
        C=weight*(q-1)*(1+q)**degree;rho=Q(0);rule='periodic_prefix'
    elif atoms==[power(r)] and periods==0:
        C=weight*(1+q)**degree/theta;rho=Q(0);rule='centered_power_kernel'
    elif atoms==canonical([power(r),mu(v)]) and periods==0:
        C0=(1/(1-v)+1+1/(v-r))/theta
        C=weight*(1+q)**degree*C0;rho=1-v;rule='centered_shifted_inverse_kernel'
    elif atoms==canonical([power(r),mu(v)]) and periods==1 and v+sigma>1:
        C0=Q(7)*(q-1)/theta*(1+1/(v+sigma-1))
        C=weight*(1+q)**degree*C0;rho=sigma;rule='periodic_center_then_absolute_shifted_convolution'
    else:
        return dict(**common,status='OPEN',reason='no admitted full centered-prefix provider',
                    atoms=deepcopy(atoms),periodic_copies=periods,
                    critical_inverse_count=sum(a==mu(0) for a in atoms))
    return dict(**common,status='PROVED',rule=rule,constant=str(C),power=str(rho),
                log_power=0,subcritical=rho<Q(1,2),
                centered_at_analytic_theta_main=any(a['kind']=='power' and a['shift']==str(r) for a in atoms),
                all_subunit_arguments_retained=True)


def pole_budget(source,j):
    orders=[]
    for c in source['channels']:
        orders.append(sum(1 if a['kind']=='mu' else -1 for a in c['atoms'] if a['shift']==0)-j)
    maximum=max(orders);leaders=[i for i,e in enumerate(orders) if e==maximum]
    preserved=maximum>0 and len(leaders)==1
    return dict(channel_orders=orders,maximum_remaining_order=maximum,leading_channels=leaders,
        RH_pole_bridge_available=preserved,
        reason='a reciprocal-zeta pole survives near the supremum of zero real parts' if preserved else
               'critical inverse pole erased; this registered RH bridge is unavailable',
        periodic_multiplier_zeros='Re(s)=1',positive_shift_factors='nonzero at a zero chosen near the rightmost supremum',
        inverse_periodic_operator_assumed_bounded=False,RH_proved=False)


def program(source,fam,q,j,hyperbola,scalar_bound):
    channels=transformed_channels(source,q,j)
    prices=[channel_price(c,fam,q,hyperbola,scalar_bound) for c in channels]
    pole=pole_budget(source,j)
    result=dict(q=q,power=j,periodic=periodic(q),channels=channels,prices=prices,pole_budget=pole,
        centering=dict(theta=fam['theta'],common_D_power=j,source_residue_zeta_multiplier=j,
                       analytic_only=True,source_normalization_required=True,
                       ordinary_mu_moment_assumed=False),
        open_source_channels=[p['source_channel'] for p in prices if p['status']=='OPEN'],
        uniform_complete_target_bound_proved=False,RH_proved=False)
    if j==1 and result['open_source_channels']==[fam['channel_roles'][0]]:
        paid=[p for p in prices if p['status']=='PROVED']
        sigma=max(Q(p['power']) for p in paid);constant=sum((Q(p['constant']) for p in paid),Q(0))
        beta=Q(fam['beta']);ceil_sigma=(sigma.numerator+sigma.denominator-1)//sigma.denominator
        energy_constant=constant**2*2**(2*ceil_sigma)
        result['reduction']=dict(
            identity='prefix(A_q*f)(x)=beta*J_q(x)+R_q(x)',
            open_source_channel=fam['channel_roles'][0],open_weight=str(beta),
            target='J_q(x)=J(x)-q*J(x/q), J(x)=prefix(K_r*mu)(x)-x^theta/(theta*zeta(theta))',
            target_domain='every real x>0; centered subunit J is retained',
            paid_remainder=dict(constant=str(constant),power=str(sigma),domain='every real x>=1',
                energy_constant=str(energy_constant),energy_power=str(2*sigma-1),
                energy_domain='every integer X>=1, X^-2 sum_(X<=n<2X)',
                all_signed_remainder_terms_retained=True),
            energy_implications=dict(
                preconditioned_source_from_new_target=dict(target_coefficient=str(2*beta**2),
                                                          remainder_coefficient='2'),
                new_target_from_preconditioned_source=dict(target_coefficient=str(2/beta**2),
                                                          remainder_coefficient=str(2/beta**2))),
            RH_implication_requires='new target energy O_epsilon(X^epsilon) for EVERY epsilon>0 uniformly over X',
            ordinary_mu_theta_series_convergence_used=False,
            inverse_A_q_bound_used=False,original_F_bound_proved=False,new_target_bound_proved=False)
    return result


def search(source,q_values=(2,3,5,7,11,17),powers=(0,1,2),scalar_bound='5',meter=None):
    m=SOURCE.Meter(cap=1_000_000,seconds=120) if meter is None else meter
    fam=family(source,m);bound=SOURCE._rational(scalar_bound,m)
    if bound<=0:raise ValueError('licensed positive absolute scalar bound')
    if type(q_values) not in (tuple,list) or not 1<=len(q_values)<=64 or list(q_values)!=sorted(set(q_values)):
        raise ValueError('distinct ordered finite period dictionary')
    if type(powers) not in (tuple,list) or any(type(j) is not int for j in powers) or list(powers)!=[0,1,2]:
        raise ValueError('declared inverse-degree audit0,1,2')
    hp=hyperbola_search(fam['theta'],fam['v'])
    programs=[]
    for q in q_values:
        periodic(q)
        for j in powers:
            m.charge(100+25*len(source['channels']))
            programs.append(program(source,fam,q,j,hp,scalar_bound))
    admissible=[p for p in programs if 'reduction' in p and p['pole_budget']['RH_pole_bridge_available']
                and Q(p['reduction']['paid_remainder']['energy_power'])<0]
    selected=min(admissible,key=lambda p:(len(p['open_source_channels']),
        Q(p['reduction']['paid_remainder']['energy_power']),p['q'])) if admissible else None
    return dict(schema='periodic-normalization-search-v1',source_binding=deepcopy(source),family=fam,
        q_values=list(q_values),powers=list(powers),scalar_abs_bound=scalar_bound,hyperbola_search=hp,
        programs=programs,selected=None if selected is None else dict(q=selected['q'],power=selected['power']),
        selection_rule='preserve RH pole, require independently subcritical complete remainder, minimize open modes then remainder power then period',
        complete_source_observations_used=False,normalization_premise_must_be_replayed=True,
        uniform_complete_target_bound_proved=False,RH_proved=False)
