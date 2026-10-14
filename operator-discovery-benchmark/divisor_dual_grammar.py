"""Index-generated full-defect dual matrices, exact arithmetic and finite LDL."""
from fractions import Fraction as Q
from math import gcd,lcm,floor
import flint
import numpy as np
from critical_defect_grammar import floor_power
from estimate_grammar import inverse_one_prefix
from rational_fractional_evaluator import ball
from mellin_kernel_grammar import real

VERSION='whole-signed-defect-divisor-zero-Gram-and-native-dual-certificate-v1'


def ceil_power(n,p):
    p=Q(p)
    if type(n)is not int or n<1 or p<0:raise ValueError('Positive integer and nonnegative rational power required')
    k=p.numerator//p.denominator;r=p-k
    if not r:return n**k
    f=floor_power(n,r)
    if f is None:return None
    if r.denominator>4096 and n.bit_length()>r.denominator:return None
    # For q beyond this bit threshold, f=1 and n>1 cannot be an exact power.
    exact=f==1 and n==1 or r.denominator<=4096 and f**r.denominator==n**r.numerator
    return n**k*(f if exact else f+1)


def mask_value(mask,n,N):
    k=mask['kind']
    if k=='constant':return int(mask['value'])
    if k=='above':return int(n>int(mask['threshold']))
    if k=='residue':return int(n%int(mask['modulus'])==int(mask['residue']))
    if k=='divisible_union':return int(any(n%int(b)==0 for b in mask['bases']))
    if k=='prefix':
        B=floor_power(N,Q(mask['power']));return None if B is None else int(n<=B)
    if k=='square':return int(__import__('math').isqrt(n)**2==n)
    raise ValueError('Unsupported row mask')


def mask_certificate(mask):
    k=mask.get('kind')
    try:
        if k=='constant':valid=mask['value'] in [0,1] and type(mask['value'])is int
        elif k=='above':valid=type(mask['threshold'])is int and mask['threshold']>=0
        elif k=='residue':valid=type(mask['modulus'])is int and mask['modulus']>=2 and type(mask['residue'])is int and 0<=mask['residue']<mask['modulus']
        elif k=='divisible_union':valid=bool(mask['bases']) and all(type(b)is int and b>=2 for b in mask['bases'])
        elif k=='prefix':valid=0<=Q(mask['power'])<=1
        elif k=='square':valid=True
        else:valid=False
    except (ValueError,KeyError,TypeError):valid=False
    return {'admitted':valid,'boolean_nonnegative_all_integer_indices':valid,'kernel_semantics_unchanged':True,'all_scale_inverse_forcing_identity_proved':valid,'global_critical_PSD_proved':False}


def gram(mask,N):
    if not mask_certificate(mask)['admitted']:raise ValueError('Admitted nonnegative mask required')
    tails=[0]*(N+1)
    for k in range(1,N+1):
        w=mask_value(mask,k,N)
        if w is None:return None
        if w:
            for d in range(1,k+1):
                if k%d==0:tails[d]+=1
    return [[tails[lcm(i,j)] if lcm(i,j)<=N else 0 for j in range(1,N+1)] for i in range(1,N+1)]


def Hmatrix(X):
    N=4*X
    def W(n):return max(0,4*X-max(2*X,n))-4*max(0,2*X-max(X,n))
    return [[W(max(i,j)) for j in range(1,N+1)] for i in range(1,N+1)]


def parameters(p,X,q):
    if p.get('arithmetic_model')!='inverse_one' or type(X)is not int or X<1 or type(q)is not int or q<1 or not mask_certificate(p['mask'])['admitted']:raise ValueError('Actual arithmetic, integer scales/levels and admitted mask required')
    c=Q(p['diagonal_coefficient']);r=Q(p['level_power']);cy=Q(p['Gram_coefficient']);gamma=Q(p['Gram_power'])
    if c<=0 or r<0 or cy<0 or gamma<0:raise ValueError('Positive diagonal and nonnegative profile powers required')
    cr=ceil_power(q,r);xr=ceil_power(X,Q(1,q));yr=ceil_power(X,gamma)
    if any(v is None for v in [cr,xr,yr]):return {'missing':True,'reason':'exact_rational_ceiling_resources_exhausted'}
    D=c*(1+cr)*X*xr;Y=cy*yr;unit=mask_value(p['mask'],1,4*X)
    return {'missing':False,'D':str(D),'Y':str(Y),'unit_forcing_weight':unit,'charged_defect_bound':str(4*X*D+Y*unit),
        'ordinary_energy_power':str(max(2+Q(1,q),gamma if unit else 0)),'level_constant_may_grow':r>0}


def family_certificate(p):
    if p.get('arithmetic_model')!='inverse_one' or not mask_certificate(p.get('mask',{}))['admitted']:return {'admitted':False,'reason':'actual_model_and_nonnegative_mask_required'}
    try:gamma=Q(p['Gram_power']);r=Q(p['level_power']);valid=Q(p['diagonal_coefficient'])>0 and Q(p['Gram_coefficient'])>=0 and gamma>=0 and r>=0
    except (ValueError,KeyError,TypeError):valid=False
    if not valid:return {'admitted':False,'reason':'nonnegative_profile_and_positive_diagonal_required'}
    unit=mask_value(p['mask'],1,4);admitted=unit==0 or gamma<=2;mask=p['mask'];barrier=None
    if mask['kind']=='constant' and not mask['value']:barrier='positive_vector_with_no_arithmetic_constraints'
    if mask['kind']=='prefix' and Q(mask['power'])<1:barrier='positive_tail_satisfies_complete_prefix_rows'
    if mask['kind']=='residue' and mask['residue']==0 and mask['modulus']in [2,3]:barrier='finite_prime_local_inverse_has_positive_linear_mean'
    if mask['kind']=='divisible_union' and set(mask['bases'])<=set([2,3]):barrier='finite_prime_local_inverse_has_positive_linear_mean'
    return {'admitted':admitted,'exact_ordinary_zeta_and_full_signed_defect_retained':True,'cofinal_positive_levels_and_every_dyadic_scale_required':True,
        'unit_Gram_forcing_cost_charged':True,'global_matrix_PSD_proved':False,'RH_if_global_matrix_PSD':admitted,
        'cofinal_critical_matrix_family_analytically_ruled_out':bool(barrier) and admitted,'global_PSD_obstruction':barrier if admitted else None,
        'bounded_level_constants_would_imply_stronger_fixed_critical_bound':r==0 and admitted,'global_RH_signed_premise_proved':False,'RH_proved':False}


def matrix(p,X,q):
    params=parameters(p,X,q)
    if params['missing']:return params,None
    G=gram(p['mask'],4*X)
    if G is None:return {'missing':True,'reason':'row_mask_resources_exhausted'},None
    D,Y=map(Q,(params['D'],params['Y']));H=Hmatrix(X);S=[[D*int(i==j)-H[i][j]+Y*G[i][j] for j in range(4*X)] for i in range(4*X)]
    return params,S


def negative_direction(S,L,k,bits=96):
    v=[flint.arb(0) for _ in range(k+1)];v[k]=flint.arb(1)
    for i in range(k-1,-1,-1):v[i]=-sum((L[j][i]*v[j] for j in range(i+1,k+1)),flint.arb(0))
    out=[Q(round(Q(z.mid().str(120,radius=False))*2**bits),2**bits) for z in v]+[Q(0)]*(len(S)-k-1);value=sum((out[i]*S[i][j]*out[j] for i in range(k+1) for j in range(k+1)),Q(0))
    return {'vector':list(map(str,out)),'exact_quadratic_value':str(value),'rejects_candidate_matrix_not_actual_RH_inequality':True} if value<0 else None


def certify(p,X,q,precision=512):
    params,S=matrix(p,X,q)
    if params['missing']:return params
    # Float eigenvectors only propose exact rational COUNTEREXAMPLES; they
    # never certify positivity. Native LDL handles every remaining matrix.
    screen=np.array([[float(z) for z in row] for row in S],dtype=np.float64)
    eig,vec=np.linalg.eigh(screen)
    if eig[0]<0:
        scale=2**40;z=[round(float(t)*scale) for t in vec[:,0]];den=lcm(*(v.denominator for row in S for v in row));integer=[[int(v*den) for v in row] for row in S]
        num=sum(z[i]*integer[i][j]*z[j] for i in range(len(S)) for j in range(len(S)))
        if num<0:
            counter={'vector':list(map(str,(Q(v,scale) for v in z))),'exact_quadratic_value':str(Q(num,den*scale**2)),'rejects_candidate_matrix_not_actual_RH_inequality':True}
            return {'missing':False,'status':'finite_rational_negative_direction','parameters':params,'counterexample':counter,'finite_matrix_PSD':False,'global_PSD_proved':False,'floating_screen_is_not_a_proof':True}
    flint.ctx.prec=precision;N=len(S);L=[[flint.arb(int(i==j)) for j in range(N)] for i in range(N)];pivots=[]
    for k in range(N):
        value=real(S[k][k])-sum((L[k][j]**2*pivots[j] for j in range(k)),flint.arb(0))
        if not value>0:
            counter=negative_direction(S,L,k) if value<0 else None
            return {'missing':counter is None,'status':'negative_matrix_direction' if counter else 'native_LDL_not_resolved','parameters':params,'precision':precision,'pivot_index':k+1,
                'pivot_ball':ball(value),'counterexample':counter,'finite_matrix_PSD':False,'global_PSD_proved':False,'missing_not_counterexample':counter is None}
        pivots.append(value)
        for i in range(k+1,N):L[i][k]=(real(S[i][k])-sum((L[i][j]*L[k][j]*pivots[j] for j in range(k)),flint.arb(0)))/value
    D=Q(params['D']);global_calibration=q==1 and D>=8*X**2
    return {'missing':False,'status':'finite_native_LDL_positive','parameters':params,'pivot_balls':list(map(ball,pivots)),'dimension':N,'precision':precision,
        'finite_matrix_PSD':True,'whole_signed_defect_at_this_scale_proved':True,'global_PSD_proved':global_calibration,
        'global_proof_scope':'q=1, every integer X, row-norm generic energy power 3' if global_calibration else None,
        'global_critical_PSD_proved':False,'RH_proved':False}


def forcing(f):
    N=len(f)-1;inv=[Q(0)]*(N+1);inv[1]=1
    for n in range(2,N+1):inv[n]=-sum((inv[d]*Q(f[n//d]) for d in range(1,n) if n%d==0),Q(0))
    response=[sum((inv[d]*Q(f[n//d]) for d in range(1,n+1) if n%d==0),Q(0)) for n in range(1,N+1)]
    return {'input':list(map(str,f)),'inverse':list(map(str,inv)),'anonymous_response':list(map(str,response)),'prime_or_factor_oracle_used':False}
