"""Source-free constant-predictor work canonicalization and scope guard."""
from fractions import Fraction as Q
from copy import deepcopy
import json
import time

SCHEMA='floor-residual-prime-work-guard-050-v1'


class Meter:
    def __init__(self,cap=1000000,seconds=60,max_bits=4096):
        self.cap,self.operations,self.max_bits=cap,0,max_bits
        self.deadline=time.monotonic()+seconds

    def charge(self,n=1):
        if type(n) is not int or n<0 or n>self.cap-self.operations:
            raise OverflowError('050 work cap')
        self.operations+=n
        if time.monotonic()>self.deadline:raise TimeoutError('050 deadline')

    def number(self,x):
        x=Q(x);bits=max(abs(x.numerator).bit_length(),x.denominator.bit_length())
        self.charge(1+bits)
        if bits>self.max_bits:raise OverflowError('050 rational bit cap')
        return x


def _json(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)


def _rat(x,m):
    if type(x) is not str or not 1<=len(x)<=2500:raise ValueError('canonical bounded rational string')
    try:y=Q(x)
    except (ValueError,ZeroDivisionError):raise ValueError('invalid rational') from None
    if str(y)!=x:raise ValueError('canonical rational required')
    return m.number(y)


def _matrix(x,m):
    if type(x) is not list or len(x)!=2 or any(type(row) is not list or len(row)!=2 for row in x):
        raise ValueError('exact two by two matrix')
    return [[_rat(v,m) for v in row] for row in x]


def _det(x,m):return m.number(m.number(x[0][0]*x[1][1])-m.number(x[0][1]*x[1][0]))


def _psd(x,m):
    return x[0][1]==x[1][0] and x[0][0]>=0 and x[1][1]>=0 and _det(x,m)>=0


def _parse(request,m):
    if type(request) is not dict or set(request)!={'Q','B','rho'}:raise ValueError('exact Q,B,rho request')
    size=len(_json(request))
    if size>32768:raise OverflowError('050 input byte cap')
    m.charge(1+size//64)
    gram,B=_matrix(request['Q'],m),_matrix(request['B'],m)
    rho=_rat(request['rho'],m)
    if not _psd(gram,m):raise ValueError('symmetric PSD Gram required')
    if rho<0:raise ValueError('nonnegative comparison coefficient required')
    return gram,B,rho


def _mat_string(x):return [[str(v) for v in row] for row in x]


def _result(request,gram,parent,rho,m):
    slack=[[m.number(rho*gram[i][j]-parent[i][j]) for j in range(2)] for i in range(2)]
    valid=_psd(slack,m)
    certificate={
        'schema':SCHEMA,'status':'ALIASED_PARENT_GRAM_RECURRENCE',
        'request':deepcopy(request),
        'canonical_observable':{'child_gram':_mat_string(gram),'parent_gram':_mat_string(parent)},
        'parent_slack':_mat_string(slack),'contraction_guard_paid':valid,
        'work_identity':'W_B = 2<Bz,Q(y-Bz)> + <y-Bz,Q(y-Bz)> = <y,Qy> - <z,Rz>, R=B^TQB',
        'slack_identity':'W_B=(P_child-rho*P_parent)+<z,(rho*Q-R)z>',
        'work_dominates_existing_increment':valid,
        'whole_work_bound_weakens_existing_obligation':False if valid else None,
        'contraction_status':'PAID_UNIVERSAL_ALGEBRA' if valid else 'FAILED_ALGEBRA_GUARD',
        'same_observable_rule':'same exact Q and R imply same complete work for every pair of Hilbert states',
        'parent_gram_dominance_rule':'R1<=R2 implies W_R1>=W_R2 at fixed child Q',
        'whole_work_change_alone_is_new_signed_arithmetic_mechanism':False,
        'distinct_downstream_source_proof_tactic_allowed':True,
        'Q_positive_definite':_det(gram,m)>0,
        'scope':'universal Hilbert-state algebra, any constant real predictor, PSD Q; exact rational admission here',
        'target_recovery_proved':False,'uniform_arithmetic_bound_proved':False,
        'source_values_evaluated':False,'norms_evaluated':False,'RH_status':'OPEN',
        'unpaid_source_leaves':['complete source identity for innovations','uniform innovation/correlation/flux estimate including all spatial tails'],
        'antirestatement_rule':'canonicalize whole-work observables by Q,R; retain B only as independently justified source-bound proof tactic',
    }
    m.charge(1+len(_json(certificate))//64)
    return certificate


def build_guard(request,meter=None):
    m=meter or Meter();gram,B,rho=_parse(request,m)
    # Matrix product computation of B^T Q B.
    qb=[[m.number(sum((m.number(gram[i][k]*B[k][j]) for k in range(2)),Q(0))) for j in range(2)] for i in range(2)]
    parent=[[m.number(sum((m.number(B[k][i]*qb[k][j]) for k in range(2)),Q(0))) for j in range(2)] for i in range(2)]
    return _result(request,gram,parent,rho,m)


def _equal(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(_equal(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_equal(x,y) for x,y in zip(a,b))
    return a==b


def verify_guard(request,certificate,meter=None):
    m=meter or Meter();gram,B,rho=_parse(request,m)
    # Separate column/polarization reconstruction, no builder call or matrix multiplication.
    def quadratic(v):
        return m.number(m.number(gram[0][0]*m.number(v[0]*v[0]))+
                        m.number(2*gram[0][1]*m.number(v[0]*v[1]))+
                        m.number(gram[1][1]*m.number(v[1]*v[1])))
    c0=[B[0][0],B[1][0]];c1=[B[0][1],B[1][1]]
    r00,r11=quadratic(c0),quadratic(c1)
    plus=quadratic([m.number(c0[i]+c1[i]) for i in range(2)])
    r01=m.number((plus-r00-r11)/2)
    expected=_result(request,gram,[[r00,r01],[r01,r11]],rho,m)
    if not _equal(certificate,expected):raise ValueError('changed canonical work, algebra, dependency or claim scope')
    return {'verified':True,'status':expected['status'],
            'canonical_observable':expected['canonical_observable'],
            'contraction_guard_paid':expected['contraction_guard_paid'],
            'uniform_arithmetic_bound_proved':False,'target_recovery_proved':False,'RH_status':'OPEN'}
