"""Generate auxiliary expressions AND uniform-bound conjectures for an input core.

Candidate answers are enumerated without numerical responses. Data can reject
or select a conjecture, but only a scoped proof rule can discharge its premise.
"""
from fractions import Fraction as Q
from itertools import combinations, product
import gzip
import json
from pathlib import Path

from flint import arb, ctx
import prime_bank_candidates as S
import joint_preconditioned_source as P

NAMES = ('nu0', 'nu1', 'nu2', 'mu')
THETAS = ('0','1/6','1/3','1/2','2/3','5/6')
ALPHAS = ('0','1/6','1/3','1/2')
AUX_THETAS = (None,'1/3','1/2','2/3')
WEIGHTS = ('1/3','1','3')
RHOS = ('1/2','1')
GAMMAS = ('0','1/6')
LOG_POWERS = (0,1)
MAX_H = 262143


def real(value):
    q=Q(value)
    return arb(q.numerator)/q.denominator


def power(base, exponent):
    q=Q(exponent)
    return arb(base).root(q.denominator)**q.numerator


def filters():
    return ([dict(kind='delay',sign=0,theta='0')]+
            [dict(kind='delay',sign=s,theta=t) for t in THETAS for s in (1,-1)]+
            [dict(kind='log_abel',cutoff=64)])


def catalogue(meter):
    vectors=[]
    for i in range(4):
        v=[0]*4;v[i]=1
        vectors.append(('single_'+NAMES[i],v))
    for i,j in combinations(range(4),2):
        for sign in (1,-1):
            v=[0]*4;v[i]=1;v[j]=sign
            vectors.append(('pair_'+NAMES[i]+'_'+NAMES[j],v))
    auxiliaries=[(None,None)]
    for (lane,v),theta,alpha,w in product(vectors,AUX_THETAS,ALPHAS,WEIGHTS):
        auxiliaries.append((lane,dict(coefficients=list(map(str,v)),theta=theta,alpha=alpha,weight=w)))
    rows=[]
    for f in filters():
        for lane,aux in auxiliaries:
            if aux is None:
                lane='baseline_log' if f['kind']=='log_abel' else 'baseline_critical' if f['sign'] and f['theta']=='1/2' else 'baseline_delay'
            rows.append(dict(id=len(rows),lane=lane,
                             program=dict(target_filter=dict(f),auxiliary=aux),
                             complexity=1+(2 if f['kind']=='log_abel' else int(bool(f['sign'])))+
                               (0 if aux is None else 2+sum(Q(v)!=0 for v in aux['coefficients'])+int(aux['theta'] is not None)+int(Q(aux['alpha'])!=0)),
                             whole_signed_bound_proved=False,RH_proved=False))
            meter.charge(30)
    return rows


def recovery(program):
    f=program['target_filter']
    if f['kind']=='log_abel':
        return dict(cofinal=True,extra_log_degree=1,kind='Volterra_absorption_with_finite_head',
                    premise='G(n)=F(n) below64; G(n)=sum_(k<=n) f(k)log(k)/log(n) at n>=64',
                    cost='tail norm <=2*(norm G+finite_head_cost), sigma>=1/2; sum dyadic G energies for a conservative extra log in block recovery',
                    uniform_core_bound_proved=False)
    theta=Q(f['theta']) if f['sign'] else Q(0)
    if not f['sign']:
        return dict(cofinal=True,extra_log_degree=0,kind='identity',uniform_core_bound_proved=False)
    if theta<Q(1,2):
        return dict(cofinal=True,extra_log_degree=0,kind='bounded_causal_inverse',
                    cost='(1-2^(theta-1/2))^-1 in critical prefix norm',uniform_core_bound_proved=False)
    if theta==Q(1,2):
        return dict(cofinal=True,extra_log_degree=2,kind='critical_polylog_causal_inverse',
                    cost='at most1+floor(log2 H) in truncated critical norm',uniform_core_bound_proved=False)
    return dict(cofinal=False,extra_log_degree=None,kind='unpaid_inverse_power',
                energy_power_loss=str(2*theta-1),uniform_core_bound_proved=False)


def pole_gate(program,meter):
    aux=program['auxiliary']
    if aux is None or Q(aux['alpha'])>=Q(1,6) or aux['theta']=='2/3':
        return dict(cofinal_obstructed=False,reason='no retained supercritical pole certified by this gate')
    kappa=arb(2)/3;z=kappa.zeta();zv=(arb(4)/3).zeta()
    masses=[1/(kappa*z*z),1/(kappa*z*zv),1/(kappa*zv),arb(0)]
    residue=sum((real(c)*m for c,m in zip(aux['coefficients'],masses)),arb(0))
    meter.charge(550)
    if residue.is_zero():
        return dict(cofinal_obstructed=False,reason='exact zero source pole')
    if residue.contains(0):
        return dict(cofinal_obstructed=False,reason='residue comparison unresolved')
    return dict(cofinal_obstructed=True,
                reason='positive auxiliary square retains a pole above the critical line',
                source_prefix_pole='2/3',weighted_prefix_pole=str(Q(2,3)-Q(aux['alpha'])),
                nonzero_residue=residue.str(55),source_row=aux['coefficients'],
                annihilating_delay_exponent='2/3',whole_core_bound_disproved=False)


def assemble_state(prefixes,core,F,Ru,H,meter):
    if type(H) is not int or not 1<=H<=MAX_H:
        raise ValueError('bounded complete core horizon')
    if set(prefixes)!=set(NAMES) or any(len(v)!=H+1 for v in [*prefixes.values(),core,F]):
        raise ValueError('all source prefixes and coefficients including unit')
    B=[arb(0)]*(H+1);G=[arb(0)]*(H+1)
    for n in range(1,H+1):
        logn=arb(n).log()
        B[n]=B[n-1]+core[n]*logn
        G[n]=F[n] if n<64 else B[n]/logn
        meter.charge(70)
    return dict(H=H,precision=ctx.prec,prefixes=prefixes,core=core,F=F,R_u=Ru,
                c=[arb(9)/2,-arb(9)/2,-Ru,-arb(9)/2],log_prefix=B,log_abel=G)


def source(H,program,meter):
    if not 1<=H<=MAX_H:raise ValueError('declared source horizon')
    s=S.source_state(H,meter)
    Ru=2*s['m_u']/3
    s['R_u']=Ru;s['tilde_b']=[arb(0)]*(H+1)
    for n in range(1,H+1):
        s['tilde_b'][n]=s['a'][n]-Ru/arb(n).root(3)
        meter.charge(70)
    t=P.prepare(s,program,meter)
    prefixes={name:t['mode_prefixes'][key] for name,key in zip(NAMES,('B','U','power','V'))}
    result=assemble_state(prefixes,t['core'],t['core_prefix'],Ru,H,meter)
    result['modes']={name:t['modes'][key] for name,key in zip(NAMES,('B','U','power','V'))}
    meter.live(54*(H+1)+4096)
    return result


def archived_source(directory,role,H,meter):
    aliases={'mode_prefix:B':'nu0','mode_prefix:U':'nu1','mode_prefix:power':'nu2','mode_prefix:V':'mu',
             'core':'core','core_prefix':'F'}
    found={}
    with gzip.open(Path(directory)/(role+'_vectors.jsonl.gz'),'rt') as stream:
        for line in stream:
            row=json.loads(line);name=row['name']
            if name in aliases:
                if len(row['values'])<=H:raise ValueError('archive horizon')
                found[aliases[name]]=[arb(v) for v in row['values'][:H+1]]
                meter.charge(8*(H+1))
    if set(found)!=set(NAMES)|{'core','F'}:raise ValueError('complete independent parent vectors')
    constants=json.loads((Path(directory)/(role+'_cases.json')).read_text())['constants']
    return assemble_state({name:found[name] for name in NAMES},found['core'],found['F'],arb(constants['R_u']),H,meter)


def gram_tables(state,scales,meter):
    """Streaming full signed Gram; storage depends on scales, not H*dimension²."""
    scales=sorted(set(scales))
    if any(type(X) is not int or X<1 or 2*X-1>state['H'] for X in scales):
        raise ValueError('whole requested blocks, never clipped')
    boundaries=sorted({0}|{j for X in scales for j in (X-1,2*X-1)})
    sums={a:[[arb(0)]*9 for _ in range(9)] for a in ALPHAS}
    saved={0:{a:[row[:] for row in matrix] for a,matrix in sums.items()}}
    boundary_set=set(boundaries)
    for n in range(1,max(boundaries)+1):
        rows=[state['prefixes'][name][n] for name in NAMES]+[state['prefixes'][name][n//2] for name in NAMES]+[state['log_abel'][n]]
        root=arb(n).root(3)
        weights={'0':arb(1),'1/6':1/root,'1/3':1/(root*root),'1/2':arb(1)/n}
        for i in range(9):
            for j in range(i,9):
                value=rows[i]*rows[j]
                for alpha,matrix in sums.items():matrix[i][j]+=weights[alpha]*value
        meter.charge(70+9*10//2*13)
        if n in boundary_set:
            saved[n]={a:[row[:] for row in matrix] for a,matrix in sums.items()}
    result={}
    for X in scales:
        result[X]={}
        for alpha in ALPHAS:
            matrix=[[arb(0)]*9 for _ in range(9)]
            for i in range(9):
                for j in range(i,9):
                    matrix[i][j]=(saved[2*X-1][alpha][i][j]-saved[X-1][alpha][i][j])/(X*X)
                    matrix[j][i]=matrix[i][j]
                    meter.charge(4)
            result[X][alpha]=matrix
    meter.live(12*(state['H']+1)+400*len(boundaries)+4096)
    return result


def form(matrix,vector,meter):
    entries=[(i,v) for i,v in enumerate(vector) if not v.is_zero()]
    result=arb(0)
    for k,(i,a) in enumerate(entries):
        result+=a*a*matrix[i][i]
        for j,b in entries[k+1:]:result+=2*a*b*matrix[i][j]
    meter.charge(6*len(entries)**2+1)
    return result


def energies(program,tables,state,meter,cache=None):
    if cache is None:cache={}
    core=state['c']+[arb(0)]*5
    f=program['target_filter']
    if f['kind']=='log_abel':g=[arb(0)]*8+[arb(1)]
    else:
        a=f['sign']*power(2,f['theta'])
        g=state['c']+[-a*v for v in state['c']]+[arb(0)]
    aux=program['auxiliary'];h=None
    if aux is not None:
        v=list(map(real,aux['coefficients']));b=arb(0) if aux['theta'] is None else power(2,aux['theta'])
        h=v+[-b*q for q in v]+[arb(0)]
    target_key=('target',)
    filter_key=('filter',tuple(sorted(f.items())))
    aux_key=None if aux is None else ('aux',tuple(aux['coefficients']),aux['theta'],aux['alpha'])
    if target_key not in cache:cache[target_key]={X:form(t['0'],core,meter) for X,t in tables.items()}
    if filter_key not in cache:cache[filter_key]={X:form(t['0'],g,meter) for X,t in tables.items()}
    if aux_key is not None and aux_key not in cache:cache[aux_key]={X:form(t[aux['alpha']],h,meter) for X,t in tables.items()}
    rows={}
    for X,table in tables.items():
        target=cache[target_key][X];filtered=cache[filter_key][X]
        additional=arb(0) if h is None else cache[aux_key][X]
        majorant=filtered+(arb(0) if aux is None else real(aux['weight'])*additional)
        meter.charge(6)
        rows[X]=dict(X=X,energy_target=target,energy_filtered=filtered,energy_auxiliary=additional,majorant=majorant)
    return rows


def envelope(X,gamma,k):
    if X&(X-1)==0:log=arb(X.bit_length()-1)
    else:log=arb(X).log()/arb(2).log()
    return power(X,gamma)*(1+log)**k


def fit(rows,scales,rho,gamma,k,meter):
    maximum=arb(0)
    for X in scales:
        drift=rows[2*X]['majorant']-real(rho)*rows[X]['majorant']
        ratio=drift/envelope(X,gamma,k)
        if ratio.upper()>maximum:maximum=ratio.upper()
        meter.charge(100)
    return str(Q(max(0,int((maximum*arb(5)/4).ceil().unique_fmpz()))))


def score(rows,scales,rho,gamma,k,C,meter):
    decisions=[]
    for X in scales:
        drift=rows[2*X]['majorant']-real(rho)*rows[X]['majorant']
        bound=real(C)*envelope(X,gamma,k)
        status='passed' if drift.upper()<=bound.lower() else 'counterexample' if drift.lower()>bound.upper() else 'inconclusive'
        decisions.append(dict(X=X,status=status,drift=drift.str(55),upper_bound=bound.str(55)))
        meter.charge(100)
    return dict(decisions=decisions,failed=sum(r['status']!='passed' for r in decisions),
                uniform_premise_proved=False)


def implication(program,rho,gamma,k,C,base_bound):
    rho=Q(rho);gamma=Q(gamma);C=Q(C);B=Q(base_bound)
    if not 0<=rho<=1 or gamma<0 or type(k)is not int or k<0 or C<0 or B<0:
        raise ValueError('nonnegative forcing and bounded scale multiplier')
    inverse=recovery(program)
    degree=k+int(rho==1)
    return dict(rule='nonnegative_auxiliary_and_dyadic_recurrence',
        auxiliary='A=E_G+w*E_H >= E_G; complete squares retain every signed cross term',
        premise=f'for every dyadic X>=1: A(2X)<={rho}*A(X)+{C}*X^({gamma})*(1+log2 X)^{k}',
        base=f'A(1)<={B}',
        growth='A(2^j)<=2^(gamma*j)*(base+C*j*(1+j)^k); j>=0',
        sharpened_log_degree=degree,
        recovery=inverse,conditional_core_cofinal=bool(gamma==0 and inverse['cofinal']),
        conditional_core_log_degree=degree+inverse['extra_log_degree'] if gamma==0 and inverse['cofinal'] else None,
        uniform_premise_proved=False,whole_signed_bound_proved=False,RH_proved=False)


def coarse_certificate(program,Ru_ceiling=5):
    """Universal weak reference bound, independent of empirical calibration."""
    if type(Ru_ceiling)is not int or Ru_ceiling<1:raise ValueError('positive certified residue ceiling')
    K=Q(27,2)+Ru_ceiling
    ct=K if program['target_filter']['kind']=='log_abel' else 2*K
    aux=program['auxiliary'];ch=Q(0);weight=Q(0)
    if aux is not None:
        if not 0<=Q(aux['alpha'])<=1:raise ValueError('nonnegative fractional weight')
        ch=2*sum(abs(Q(v)) for v in aux['coefficients']);weight=Q(aux['weight'])
        if weight<=0:raise ValueError('positive storage weight')
    constant=72*(ct*ct+weight*ch*ch)
    return dict(rule='absolute_prefix_majorants',source='actual_mu_candidate10_four_mode_core',
        imports=['|nu0(n)|<=d2(n); |nu1(n)|,|nu2(n)|,|mu(n)|<=1',
                 'sum_(n<=x) d2(n)<=x*(1+log x)', '0<R_u<=residue_ceiling'],
        program=program,residue_ceiling=Ru_ceiling,constant=str(constant),gamma='1',log_power=2,
        statement='for every dyadic X>=1 and rho>=0: A(2X)-rho*A(X)<=constant*X*(1+log2 X)^2',
        independently_rh_sufficient=False,whole_signed_bound_proved=False,RH_proved=False)


def hypothesis_record(row,rho,gamma,k,C,base_bound,training,validation,pole):
    cert=implication(row['program'],rho,gamma,k,C,base_bound)
    return dict(program_id=row['id'],lane=row['lane'],rho=rho,gamma=gamma,log_power=k,constant=C,
                base_bound=base_bound,training=training,validation=validation,
                consequence=cert,analytic_gate=pole,
                cofinal_candidate=cert['conditional_core_cofinal'] and not pole['cofinal_obstructed'],
                status='analytic_obstruction' if pole['cofinal_obstructed'] and gamma=='0' else
                       'finite_counterexample' if validation['failed'] else 'finite_survivor_open_uniform_premise',
                complexity=row['complexity'],whole_signed_bound_proved=False,RH_proved=False)


def rank(record):
    degree=record['consequence']['conditional_core_log_degree']
    return (not record['cofinal_candidate'],record['validation']['failed'],
            degree if degree is not None else 100,record['complexity'],
            Q(record['gamma']),record['program_id'],Q(record['rho']),record['log_power'])


def obligation(record,row):
    return dict(id='core_auxiliary_increment_'+str(row['id'])+'_'+record['rho']+'_'+record['gamma']+'_'+str(record['log_power']),
        status=('counterexample_found' if record['status']=='finite_counterexample' else
                'analytic_obstruction' if record['status']=='analytic_obstruction' else 'open'),
        source='actual_mu_candidate10_four_mode_core',program=row['program'],
        expression=['subtract',['auxiliary_energy',row['id'],'2X'],['multiply',record['rho'],['auxiliary_energy',row['id'],'X']]],
        required_bound=dict(constant=record['constant'],power=record['gamma'],log_power=record['log_power']),
        uniformity='all dyadic X>=1; the displayed constant is independent of X',
        consequence=record['consequence'],finite_status=record['status'],
        dependency_class='candidate10_complete_prime_bank_covariance',
        is_equivalent_rewrite=False,is_stronger_sufficient_intermediate_lemma=record['cofinal_candidate'],
        next_search_input_is_this_expression=True,all_crosses_and_units_retained=True,
        proof_attempts=['nonnegative auxiliary domination: proved',
                        'conditional dyadic iteration and target recovery: proved',
                        'absolute-prefix backend: proves only the archived gamma=1 reference bound',
                        'required signed uniform step: OPEN'],
        whole_signed_bound_proved=False,RH_proved=False)
