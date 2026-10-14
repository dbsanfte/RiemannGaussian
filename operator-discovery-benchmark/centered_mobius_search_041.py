"""Search signed, dissipative covariance controls for the full centered prefix.

Only training Grams reach selection. All hypotheses remain OPEN; finite
evidence and the proved recurrence implication have separate statuses.
"""
from fractions import Fraction as Q
import math
import numpy as np


MULTIPLIERS=(2,3,5,7)
TRAIN_SCALES=tuple(2**k for k in range(5,11))
CHECK_SCALES=tuple(2**k for k in range(17))
HORIZON=2**20-1


def rational(value):
    if type(value) is not str or len(value)>2500:raise ValueError('canonical rational string')
    q=Q(value)
    if str(q)!=value:raise ValueError('canonical rational string')
    return q


def lambda_value(program,r_text):
    expr=program['lambda']
    if expr['kind']=='rational':return float(rational(expr['value']))
    if expr!=dict(kind='prime_power',prime=program['m'],exponent=str(-rational(r_text))):
        raise ValueError('source-generated prime-power parameter')
    return math.exp(-float(rational(r_text))*math.log(program['m']))


def canonical_key(program):
    delta=rational(program['delta']);lam=program['lambda']
    # At delta0 the innovation coordinate cancels exactly from the inequality.
    key=None if delta==0 else tuple(sorted(lam.items()))
    return (program['m'],key,program['rho'],program['delta'],program['C'])


def dictionary(r_text='1/3'):
    r=rational(r_text)
    if not 0<r<Q(1,2):raise ValueError('source exponent domain')
    programs=[];keys={};aliases=[];raw=0
    for m in MULTIPLIERS:
        lambdas=[dict(kind='rational',value=s) for s in ('1/2','1','3/2')]
        lambdas.append(dict(kind='prime_power',prime=m,exponent=str(-r)))
        for lam in lambdas:
            for rho in ('0','1/2','1'):
                for delta in ('0','1/4','1'):
                    for C in ('0','1'):
                        raw+=1
                        p=dict(id='pending',m=m,**{'lambda':lam.copy()},rho=rho,delta=delta,C=C)
                        key=canonical_key(p)
                        if key in keys:
                            aliases.append(dict(program_id=keys[key],discarded_lambda=lam.copy(),
                                                reason='delta0 innovation parameter cancels exactly'))
                            continue
                        p['id']='haar_%03d'%(len(programs)+1);keys[key]=p['id'];programs.append(p)
    return dict(programs=programs,raw_program_count=raw,canonical_program_count=len(programs),
                exact_aliases=aliases,parameters=dict(m=list(MULTIPLIERS),r=r_text,
                rho=['0','1/2','1'],delta=['0','1/4','1'],C=['0','1']),
                identity='Q=E_A-m*rho*E_J+delta*E_(A-lambda*J)-C*D',
                no_selected_formula_supplied=True,uniform_bound_proved=False)


def prefix_squares(a):
    if not isinstance(a,np.ndarray) or a.ndim!=1 or not np.isfinite(a).all() or a[0]!=0:
        raise ValueError('complete finite increment vector with zero at index0')
    return np.cumsum(a*a)


def block(state,m,X,d_prefix):
    if type(m) is not int or m<2 or type(X) is not int or X<1 or 2*m*X>len(state['J']):
        raise ValueError('complete child block and positive integer scale')
    J=state['J'][X:2*X]
    child=state['J'][m*X:2*m*X].reshape(X,m)
    A=np.mean(child,axis=1)
    normalization=float(X)*X
    G=np.array([[np.dot(J,J),np.dot(J,A)],[np.dot(J,A),np.dot(A,A)]])/normalization
    variance=float(np.sum((child-A[:,None])**2)/(m*m*normalization))
    child_energy=float(np.sum(child*child)/(m*m*normalization))
    values=[*G.flat,variance,child_energy,float(d_prefix[2*m*X-1]/X)]
    if not all(math.isfinite(v) for v in values):raise ValueError('finite complete Gram observation')
    return dict(m=m,X=X,gram=G.tolist(),D=float(d_prefix[2*m*X-1]/X),
                within_cell_variance=variance,child_energy=child_energy,
                identity_residual=child_energy-float(G[1,1])/m-variance)


def training_evidence(state):
    d=prefix_squares(state['a'])
    return dict(r=state['r'],q=state['q'],training_scales=list(TRAIN_SCALES),
                blocks=[block(state,m,X,d) for m in MULTIPLIERS for X in TRAIN_SCALES],
                scope='training only; validation and final blocks are not passed to selection')


def evaluate(program,observations,r_text):
    lam=lambda_value(program,r_text);rho=float(rational(program['rho']))
    delta=float(rational(program['delta']));C=float(rational(program['C']))
    results=[]
    for obs in observations:
        if obs['m']!=program['m']:raise ValueError('matching Haar multiplier')
        G=np.asarray(obs['gram'],dtype=float)
        if G.shape!=(2,2) or not np.isfinite(G).all():raise ValueError('finite2x2 signed Gram')
        # Keep the signed cross. Never clip it or pretend the diagonal pays it.
        terms=((1+delta)*G[1,1],-2*delta*lam*G[0,1],
               (delta*lam*lam-program['m']*rho)*G[0,0],-C*obs['D'])
        defect=math.fsum(float(t) for t in terms)
        tolerance=1e-10*(1+math.fsum(abs(float(t)) for t in terms))
        status='pass' if defect < -tolerance else 'fail' if defect > tolerance else 'unresolved'
        results.append(dict(X=obs['X'],defect=defect,tolerance=tolerance,status=status,
                            innovation_energy=float(G[1,1]-2*lam*G[0,1]+lam*lam*G[0,0])))
    return results


def growth(program):
    return 'bounded' if rational(program['rho'])<1 or rational(program['C'])==0 else 'logarithmic'


def _rank(program,observations):
    # Uniform conclusion, then algebraic strength and simple representation.
    # Finite margin is only a last tie-break; C is never fitted from data.
    return (growth(program)!='bounded',rational(program['rho']),-rational(program['delta']),
            rational(program['C']),program['m'],program['lambda']['kind']!='rational',
            max(row['defect'] for row in observations),program['id'])


def search(evidence,r_text='1/3',q=2):
    if evidence.get('r')!=r_text or evidence.get('q')!=q or evidence.get('training_scales')!=list(TRAIN_SCALES):
        raise ValueError('exact bound source and frozen training partition')
    lookup={}
    for row in evidence['blocks']:
        key=(row['m'],row['X'])
        if key in lookup:raise ValueError('distinct training blocks')
        lookup[key]=row
    if set(lookup)!={(m,X) for m in MULTIPLIERS for X in TRAIN_SCALES}:
        raise ValueError('only the complete declared training partition may enter selection')
    grammar=dictionary(r_text);assessments=[];programs={p['id']:p for p in grammar['programs']}
    by_id={}
    for p in grammar['programs']:
        obs=evaluate(p,[lookup[p['m'],X] for X in TRAIN_SCALES],r_text)
        row=dict(id=p['id'],observations=obs,failures=sum(x['status']=='fail' for x in obs),
                 unresolved=sum(x['status']=='unresolved' for x in obs),
                 uniform_consequence_if_proved=growth(p),uniform_bound_proved=False)
        assessments.append(row);by_id[p['id']]=row
    passing=[p for p in grammar['programs'] if not by_id[p['id']]['failures'] and not by_id[p['id']]['unresolved']]
    strata=dict(
        zero_forcing=lambda p:Q(p['C'])==0,
        dissipative_bounded=lambda p:Q(p['delta'])>0 and growth(p)=='bounded',
        arithmetic_innovation=lambda p:Q(p['delta'])>0 and p['lambda']['kind']=='prime_power',
        logarithmic=lambda p:Q(p['rho'])==1 and Q(p['C'])>0,
        direct_moment=lambda p:Q(p['delta'])==0 and Q(p['rho'])==0)
    chosen=[];selection=[]
    for name,condition in strata.items():
        eligible=[p for p in passing if condition(p)]
        if not eligible:
            selection.append(dict(stratum=name,eligible=0,selected=None));continue
        selected=min(eligible,key=lambda p:_rank(p,by_id[p['id']]['observations']))
        selection.append(dict(stratum=name,eligible=len(eligible),selected=selected['id']))
        if selected['id'] not in {p['id'] for p in chosen}:chosen.append(selected)
    # An unfitted zero-forcing endpoint is retained as a declared control,
    # even when refuted during training. It is not relabeled as a survivor.
    baseline=next(p for p in grammar['programs'] if p['m']==2 and p['rho']=='1' and p['delta']=='0' and p['C']=='0')
    if baseline['id'] not in {p['id'] for p in chosen}:chosen.append(baseline)
    return dict(schema='centered-mobius-haar-search-v1',r=r_text,q=q,
        grammar=grammar,training_assessments=assessments,selection=selection,candidates=chosen,
        coverage=dict(raw_programs=grammar['raw_program_count'],canonical_programs=len(programs),
                      aliases=len(grammar['exact_aliases']),training_passes=len(passing),
                      training_refuted=sum(row['failures']>0 for row in assessments),
                      training_unresolved=sum(row['failures']==0 and row['unresolved']>0 for row in assessments)),
        control=baseline['id'],training_scales=list(TRAIN_SCALES),
        selection_uses_other_scales=False,constants_fitted=False,
        signed_covariance_inequality='2*lambda*C_JI+(1+delta)*E_I <= (m*rho-lambda^2)*E_J+C*D',
        original_full_target_retained=True,uniform_covariance_bound_proved=False,RH_proved=False)
