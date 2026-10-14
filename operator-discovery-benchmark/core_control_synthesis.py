"""Generate complete storage constructions, recurrence conjectures and proof DAGs.

The grammar and elementary proof rules are supplied. Every expression, shape,
training constant, selection and obstruction is then produced without model
calls. A finite pass leaves the uniform increment as an OPEN lemma.
"""
from fractions import Fraction as Q
from itertools import product
import math
import numpy as np
from flint import arb

KINDS=('log_bank','half_delay','transport_error')
ALPHAS=('0','1/6','1/3')
MIXES=('-1','1')
RESERVES=('1/3','1','3')
RHOS=('1/2','1')
LOG_POWERS=('0','1/2','1','3/2','2','3','4','6')


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
    elif type(aux) is not dict or set(aux)!={'kind','alpha'} or aux['kind'] not in KINDS or rational(aux['alpha'])<0:
        raise ValueError('auxiliary kind and nonnegative fractional exponent')


def validate_shape(shape):
    if type(shape) is not dict or set(shape)!={'rho','log_power'}:raise ValueError('recurrence AST')
    if not 0<rational(shape['rho'])<=1 or rational(shape['log_power'])<0:raise ValueError('contractive or additive recurrence')


def catalogue(meter):
    programs=[dict(auxiliary=None,mix='0',reserve='1')]
    programs.extend(dict(auxiliary=dict(kind=k,alpha=a),mix=s,reserve=w)
                    for k,a,s,w in product(KINDS,ALPHAS,MIXES,RESERVES))
    rows=[]
    for p in programs:
        validate(p);aux=p['auxiliary']
        rows.append(dict(id=len(rows),program=p,lane='baseline' if aux is None else aux['kind'],
                         complexity=1 if aux is None else 4+int(aux['alpha']!='0')+int(p['reserve']!='1')))
        meter.charge(50)
    return rows


def shapes():return [dict(rho=r,log_power=k) for r,k in product(RHOS,LOG_POWERS)]


def certificate(program,shape,transport,pole_witness_verified=False):
    validate(program);validate_shape(shape)
    a,w=rational(program['mix']),rational(program['reserve'])
    rho,k=rational(shape['rho']),rational(shape['log_power'])
    c=1+a*a/w;degree=k+(rho==1);error=2*rational(transport['theta'])-Q(5,3)
    paid=error<=0;excluded=bool(pole_witness_verified and paid and degree<2)
    return dict(domination_constant=str(c),full_target_storage_constant=str(2*c),error_constant='50',
        error_power=str(error),conditional_log_degree=str(degree),cofinal_recovery=paid,pole_excluded=excluded,
        domination_identity='(1+a^2/w)*[(G+aQ)^2+wQ^2]-G^2=(aG+(a^2+w)Q)^2/w',
        conditional_constant='A(1)+C/(1-rho)' if rho<1 else 'A(1)+C',
        uniform_premise='A(2X)<=rho*A(X)+C*(1+log2X)^k for EVERY dyadic X>=1, SAME C',
        pole_gate_target='ORIGINAL f through paid energy recovery, including theta5/6; no pole of g is assumed',
        uniform_premise_established=False,all_scale_storage_bound_proved=False,all_scale_target_bound_proved=False,RH_proved=False)


def auxiliary_values(state,aux):
    H=state['H'];n=np.arange(1,H+1);G=np.asarray([float(v) for v in state['G']])
    if aux['kind']=='log_bank':q=np.asarray([float(v) for v in state['Bg'][1:]])/np.log(2*n)
    elif aux['kind']=='half_delay':q=G[n//2]
    else:q=np.asarray([float(v) for v in state['D'][1:]])
    return np.concatenate(([0.],q*n**(-float(rational(aux['alpha'])))))


def float_tables(state,scales,meter):
    H=state['H'];G=np.asarray([float(v) for v in state['G']]);tables={}
    for X in scales:
        if type(X) is not int or X<1 or X&(X-1) or 2*X-1>H:raise ValueError('whole dyadic block')
    base={X:float(np.dot(G[X:2*X],G[X:2*X])/X**2) for X in scales}
    for kind,alpha in product(KINDS,ALPHAS):
        q=auxiliary_values(state,dict(kind=kind,alpha=alpha));row={}
        for X in scales:
            v,z=G[X:2*X],q[X:2*X]
            row[X]=(base[X],float(np.dot(v,z)/X**2),float(np.dot(z,z)/X**2))
        tables[(kind,alpha)]=row;meter.charge(35*H)
    meter.live(16*(H+1)+len(scales)*40)
    return dict(base=base,auxiliaries=tables)


def float_storage(program,tables):
    validate(program);a,w=float(rational(program['mix'])),float(rational(program['reserve']))
    aux=program['auxiliary']
    if aux is None:return dict(tables['base'])
    return {X:gg+2*a*gq+(a*a+w)*qq for X,(gg,gq,qq) in tables['auxiliaries'][(aux['kind'],aux['alpha'])].items()}


def fit(storage,parents,shape,meter):
    validate_shape(shape);rho,k=float(rational(shape['rho'])),float(rational(shape['log_power']))
    ratios=[(storage[2*X]-rho*storage[X])/(1+X.bit_length()-1)**k for X in parents]
    if not ratios or any(not math.isfinite(x) for x in ratios):raise ArithmeticError('finite complete training')
    meter.charge(50*len(parents));return max(1,math.ceil(1.25*max(0.,*ratios)))


def float_test(storage,parents,shape,C,meter):
    rho,k=float(rational(shape['rho'])),float(rational(shape['log_power']))
    rows=[]
    for X in parents:
        delta=storage[2*X]-rho*storage[X];upper=C*(X.bit_length())**k
        rows.append(dict(X=X,drift=delta,upper_bound=upper,status='pass' if delta<=upper else 'fail'))
        meter.charge(50)
    return rows


def exact_measure(state,program,X,meter):
    validate(program);H=state['H']
    if type(X) is not int or X<1 or X&(X-1) or 2*X-1>H:raise ValueError('complete dyadic block')
    a,w=real(program['mix']),real(program['reserve']);aux=program['auxiliary'];total=arb(0)
    for n in range(X,2*X):
        g=state['G'][n]
        if aux is None:total+=g*g;meter.charge(8);continue
        if aux['kind']=='log_bank':q=state['Bg'][n]/arb(2*n).log()
        elif aux['kind']=='half_delay':q=state['G'][n//2]
        else:q=state['D'][n]
        alpha=rational(aux['alpha']);q/=arb(n).root(alpha.denominator)**alpha.numerator
        total+=(g+a*q)**2+w*q*q;meter.charge(200)
    return total/(X*X)


def exact_test(storage,parents,shape,C,meter):
    validate_shape(shape)
    if type(C) is not int or C<1:raise ValueError('frozen positive integer constant')
    k=rational(shape['log_power']);rho=real(shape['rho']);rows=[]
    for X in parents:
        delta=storage[2*X]-rho*storage[X]
        upper=C*arb(X.bit_length()).root(k.denominator)**k.numerator
        rows.append(dict(X=X,drift=delta,upper_bound=upper,status='pass' if delta<=upper else 'fail' if delta>upper else 'unresolved'))
        meter.charge(180)
    return rows


def proof_obligation(record):
    """A typed, acyclic obligation; an open leaf can never certify its parent."""
    cert=record['certificate'];key='control_'+str(record['transport_id'])+'_'+str(record['storage_id'])+'_'+record['shape']['rho']+'_'+record['shape']['log_power']
    nodes=[dict(id='uniform_increment',status='open',depends_on=[],
                expression=dict(op='subtract',left=['storage',record['storage_program'],'2X'],
                    right=['sum',['multiply',record['shape']['rho'],['storage',record['storage_program'],'X']],
                                 ['multiply',record['constant'],['power',['add',1,['log2','X']],record['shape']['log_power']]]]),
                required='<=0 at EVERY dyadic X>=1 with this SAME C',finite_tests_do_not_discharge=True),
           dict(id='storage_growth',status='conditional',depends_on=['uniform_increment'],rule='dyadic_induction',log_degree=cert['conditional_log_degree']),
           dict(id='core_growth',status='conditional',depends_on=['storage_growth'],
                rules=['positive_square_domination','paid_transport_recovery'],original_corrections_retained=True)]
    ids={r['id'] for r in nodes};done=set()
    for n in nodes:
        if not set(n['depends_on'])<=done:raise ValueError('cyclic or missing proof dependency')
        done.add(n['id'])
    return dict(id=key,schema='detector-generated-core-control-obligation-v1',transport_program=record['transport_program'],
        storage_program=record['storage_program'],shape=record['shape'],constant=record['constant'],
        target='complete original core energy; all units, prime powers, signed cross terms and old recovery retained',
        construction_origin='enumerated supplied arithmetic/auxiliary grammar, selected by frozen rule without model calls',
        proof_rule_origin='supplied elementary identities and reviewed analytic imports; composed automatically',
        dependency_graph=nodes,dependency_cycle=False,uniform_premise_established=False,
        next_search_target=nodes[0],whole_signed_bound_proved=False,RH_proved=False)
