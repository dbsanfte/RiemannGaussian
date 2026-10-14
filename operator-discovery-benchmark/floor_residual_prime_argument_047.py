"""Exact conditional joint-potential proof schemas; no source/norm evaluation.

Arithmetic recurrence/base leaves are never admitted from numerical flags.
The paid objects here are universal rational majorization and induction rules.
"""
from copy import deepcopy
from fractions import Fraction as Q
import json
import time

SCHEMA = 'floor-residual-prime-argument-047-v1'
ROUNDING = {'kind':'dyadic_power_floor','bits_multiplier':4,
            'scale':'ceil_log2_N','drift':'round_each_exponential_before_signed_sum',
            'product':'multiply_rounded_children_exactly'}


class Unsupported(ValueError):
    pass


class Meter:
    def __init__(self, cap=1000000, seconds=60, max_bits=4096):
        self.cap, self.operations, self.max_bits = cap, 0, max_bits
        self.deadline = time.monotonic()+seconds

    def charge(self, n=1):
        if type(n) is not int or n<0 or n>self.cap-self.operations:
            raise OverflowError('047 algebra work cap')
        self.operations += n
        if time.monotonic()>self.deadline:
            raise TimeoutError('047 algebra deadline')

    def number(self, x):
        x=Q(x)
        bits=max(abs(x.numerator).bit_length(),x.denominator.bit_length())
        self.charge(1+bits)
        if bits>self.max_bits:
            raise OverflowError('047 rational bit cap')
        return x


def _json(x):
    return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)


def _keys(x, names):
    if type(x) is not dict or set(x)!=set(names):
        raise Unsupported('exact request/AST fields required')


def _rat(x,m):
    if type(x) is not str or not 1<=len(x)<=2500:
        raise Unsupported('canonical bounded rational string required')
    try:y=Q(x)
    except (ValueError,ZeroDivisionError):
        raise Unsupported('invalid rational') from None
    if str(y)!=x:
        raise Unsupported('canonical rational string required')
    return m.number(y)


def _pow(x,n,m):
    if type(n) is not int or n<0:
        raise Unsupported('nonnegative exact power')
    bits=max(abs(x.numerator).bit_length(),x.denominator.bit_length())
    if n*bits>m.max_bits:
        raise OverflowError('047 power result bit preflight')
    out=Q(1)
    while n:
        m.charge()
        if n&1:out=m.number(out*x)
        n//=2
        if n:x=m.number(x*x)
    return out


def _psd(a,c,d,m):
    det=m.number(m.number(a*d)-m.number(c*c))
    return a>=0 and d>=0 and det>=0, det


def completed_square_gram(tau,d,meter=None):
    """Gram of (H+A)^2+tau*(H+(1-d)*A)^2, exact rationals."""
    m=meter or Meter()
    tau,d=_rat(tau,m),_rat(d,m)
    if tau<0:raise ValueError('nonnegative storage weight required')
    v=m.number(1-d)
    return [[str(m.number(1+tau)),str(m.number(1+tau*v))],
            [str(m.number(1+tau*v)),str(m.number(1+tau*v*v))]]


def enumerate_potentials(tau_values,d_values,meter=None):
    m=meter or Meter()
    if type(tau_values) is not list or type(d_values) is not list or len(tau_values)*len(d_values)>4096:
        raise OverflowError('047 potential catalogue size cap')
    out=[]
    for tau in tau_values:
        for d in d_values:
            gram=completed_square_gram(tau,d,m)
            out.append({'tau':tau,'d':d,'gram':gram,
                        'target_only_control':Q(tau)==0 or Q(d)==0})
    return out


def _parse(request,m):
    _keys(request,('source_recipe','rounding','prime','original_forcing_b','target','argument'))
    try:size=len(_json(request))
    except (TypeError,ValueError):raise Unsupported('finite JSON input required') from None
    if size>65536:raise OverflowError('047 input size cap')
    m.charge(1+size//64)
    recipe=request['source_recipe']
    _keys(recipe,('id','base','auxiliary'))
    if type(recipe['id']) is not str or len(recipe['id'])>256 or recipe['auxiliary'] is not None:
        raise Unsupported('bounded source ordinal and null external auxiliary required')
    base=recipe['base'];_keys(base,('kind','a','theta','terms'))
    if base['kind']!='drift_mixture':raise Unsupported('bare moving-profile source required')
    a,theta=_rat(base['a'],m),_rat(base['theta'],m)
    if a<=0 or not 0<theta<1:raise Unsupported('a>0, 0<theta<1 required')
    terms=base['terms']
    if type(terms) is not list or not 1<=len(terms)<=8:raise Unsupported('one through eight fixed terms')
    prior=Q(0);total=Q(0);Cw=Q(0)
    for term in terms:
        _keys(term,('rate','weight'))
        r,w=_rat(term['rate'],m),_rat(term['weight'],m)
        if r<=prior or w==0:raise Unsupported('sorted distinct positive rates/nonzero weights required')
        prior=r;total=m.number(total+w);Cw=m.number(Cw+abs(w))
    if total!=1:raise Unsupported('unit profile sum required')
    if _json(request['rounding'])!=_json(ROUNDING):raise Unsupported('actual rounded source policy required')
    p=request['prime']
    if type(p) is not int or not 2<=p<=4096:raise Unsupported('bounded actual prime required')
    j=2
    while j*j<=p:
        m.charge()
        if p%j==0:raise Unsupported('prime adjunction cannot use composite dilation')
        j+=1
    if request['original_forcing_b']!='-1':raise Unsupported('whole plus-dilation forcing required')
    target=request['target'];_keys(target,('A','eta'))
    A,eta=_rat(target['A'],m),_rat(target['eta'],m)
    if A<=0 or eta<=0:raise Unsupported('positive finite target constant and exponent required')
    arg=request['argument'];_keys(arg,('state','gram','recurrence','base'))
    if arg['state']!='prime_split_H_A':raise Unsupported('exact full H+A state required')
    gram=arg['gram']
    if type(gram) is not list or len(gram)!=2 or any(type(row) is not list or len(row)!=2 for row in gram):
        raise Unsupported('two by two rational Gram required')
    q00,q01,q10,q11=[_rat(v,m) for row in gram for v in row]
    if q01!=q10:raise Unsupported('symmetric Gram required')
    rec=arg['recurrence'];_keys(rec,('rho','C','forcing','parities'))
    rho,C=_rat(rec['rho'],m),_rat(rec['C'],m)
    if not 0<=rho<1 or C<0:raise Unsupported('0<=rho<1, C>=0 required')
    if rec['forcing']!='L_parent^-eta' or not _equal(rec['parities'],[0,1]):
        raise Unsupported('both integer children and parent-level forcing required')
    _keys(arg['base'],('minimum',))
    M=arg['base']['minimum']
    if type(M) is not int or not 2<=M<=2**31 or M&(M-1):
        raise Unsupported('power-of-two minimum2..2^31 required')
    return p,theta,Cw,A,eta,q00,q01,q11,rho,C,M,M.bit_length()


def _equal(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(_equal(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_equal(x,y) for x,y in zip(a,b))
    return a==b


def evaluate_argument(request,meter=None):
    """Certify an implication; never promote empirical premises to a proof."""
    m=meter or Meter()
    try:values=_parse(request,m)
    except Unsupported as exc:
        return {'schema':SCHEMA,'status':'UNSUPPORTED','reason':str(exc),
                'target_status':'OPEN','RH_status':'OPEN'}
    p,theta,Cw,A,eta,q00,q01,q11,rho,C,M,L0=values
    majorant,detdiff=_psd(m.number(q00-1),m.number(q01-1),m.number(q11-1),m)
    if not majorant:
        return {'schema':SCHEMA,'status':'INVALID_ARGUMENT','reason':'Gram minus full target outer product is not PSD',
                'target_status':'OPEN','RH_status':'OPEN','request':deepcopy(request)}
    margin=m.number(1-rho-m.number(C/A))
    # rho+C/A <= (L0/(L0+1))^eta; exponentiation uses positive rationals only.
    left=m.number(rho+m.number(C/A))
    induction=_pow(left,eta.denominator,m)<=_pow(Q(L0,L0+1),eta.numerator,m)
    if not induction:
        return {'schema':SCHEMA,'status':'INVALID_ARGUMENT','reason':'exact initial-level induction budget fails',
                'target_status':'OPEN','RH_status':'OPEN','request':deepcopy(request)}
    _,detQ=_psd(q00,q01,q11,m)
    status='OPEN'
    rejection=None
    if theta>Q(1,2) and (eta>1-theta or C==0):
        status='REFUTED_ARGUMENT'
        rejection={'rule':'046 reviewed unconditional whole-forcing lower beta bound',
                   'bare_source_preserved':True,'reason':('eta>1-theta' if eta>1-theta else 'zero forcing gives geometric decay faster than beta'),
                   'finite_tests_unchanged':True}
    # Zero forcing refutes this geometric recurrence, not every slower
    # logarithmic upper bound for the unchanged target.
    target_refuted = theta>Q(1,2) and eta>1-theta
    cert={'schema':SCHEMA,'status':status,'target_status':('REFUTED' if target_refuted else 'OPEN'),
          'request':deepcopy(request),'RH_status':'OPEN','source_values_evaluated':False,'norms_evaluated':False,
          'implication_status':'PAID_UNIVERSAL_ALGEBRA',
          'source_identity':{
              'source':'actual ordinary Mobius mu; every N and prime-child profile recomputed with exact rounding',
              'target':'h_N=e_(pN)+D_p e_N=H_N+A_N',
              'split':'A_N=D_p[(1-V_(pN)(p))*chi+sum_(n=2)^N mu(n)*(U_N(n)-V_(pN)(pn))*f_n]; H_N=h_N-A_N',
              'U_N':'actual rounded parent profile, not a quotient or a fixed lambda assumption',
              'zero_lambda_allowed':True,'all_prime_powers_and_units_retained':True},
          'potential':{'definition':'P_N=sum_(k>=1) z_N(k)^T Q z_N(k)/(k*(k+1)), z=(H_N(1/k),A_N(1/k))',
              'full_target_domination':'||h_N||^2<=P_N','majorant_difference_determinant':str(detdiff),
              'gram_determinant':str(detQ),'joint_state_strictly_coercive':detQ>0,
              'target_only_control':detQ==0},
          'induction':{'initial_level':L0,'left':str(left),'right_base':str(Q(L0,L0+1)),
              'exponent':str(eta),'exact_comparison':'left^eta.denominator <= right_base^eta.numerator',
              'universal_conclusion_if_leaves_paid':'P_N<=A/L(N)^eta for every integer N>=M; hence whole target norm bound',
              'child_level':'L(2N+r)=L(N)+1 for r=0,1','whole_base_interval':[M,2*M-1],
              'no_empirical_flag_admission':True},
          'dependencies':[
              {'id':'SOURCE_SPLIT','status':'PAID_UNIVERSAL_ALGEBRA','scope':'all integers N>=M, actual rounded prime source',
               'claim':'A is the displayed direct finite expression and H=h-A by definition; exact all-scale identity; finite implementations still require their own replay'},
              {'id':'BASE','status':'OPEN','scope':{'N_interval':[M,2*M-1],'all_k':True},
               'claim':'P_N<=A/L(N)^eta, certified exact head plus paid infinite tail for every base N'},
              {'id':'RECURRENCE','status':'OPEN','scope':{'N_minimum':M,'parities':[0,1],'all_k':True},
               'claim':'P_(2N+r)<=rho*P_N+C/L(N)^eta with fixed Gram and constants, both parities'},
          ],
          'spatial_tail':{
              'required':'all k>K including k>N and k>pN; finite source does not imply zero tail',
              'source_envelope_Cw':str(Cw),'H_bound':'3+Cw*(p+3)*N','A_bound':'1+2*Cw*N',
              'paid_rule':'tail_(k>K) P <= (abs(Q00)*BH^2+2*abs(Q01)*BH*BA+abs(Q11)*BA^2)/(K+1)',
              'cost':'quadratic in N before division by K; no uniform log-rate follows without choosing and paying K'},
          'predictor_work':{
              'enumerable':'fixed rational two-by-two B with B^T Q B<=rho Q',
              'innovation':'xi_(N,r)(k)=z_(2N+r)(k)-B*z_N(k), all k>=1',
              'exact_identity':'P_child-rho*P_parent=<z_parent,(B^TQB-rho Q)z_parent>+2<B z_parent,Q xi>+<xi,Q xi>',
              'sufficient_source_leaf':'2<B z_parent,Q xi>+<xi,Q xi> <= C/L(N)^eta, both parities, full tail',
              'status':'OPEN; signed work is not a separately positive innovation bound',
              'zero_predictor_control':'B=0 leaves P_child itself and is an endpoint restatement'},
          'analytic_rejection':rejection,
          'uniform_arithmetic_bound_proved':False,'RH_proved':False,'RH_refuted':False}
    m.charge(1+len(_json(cert))//64)
    return cert


def verify_argument(request,certificate,meter=None):
    """Exact replay of this source-free implication, not an independent audit."""
    m=meter or Meter()
    expected=evaluate_argument(request,m)
    if not _equal(expected,certificate):raise ValueError('changed argument, scope, dependency or exact algebra')
    return {'verified':True,'status':expected['status'],'target_status':expected['target_status'],
            'implication_status':expected.get('implication_status','UNPAID'),
            'uniform_arithmetic_bound_proved':False,'RH_status':'OPEN'}
