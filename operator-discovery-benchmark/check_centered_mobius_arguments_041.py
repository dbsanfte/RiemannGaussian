"""Independent all-scale Haar/covariance implications; no source observations.

An admitted program has an OPEN arithmetic covariance premise. Verification
proves its conditional implication, never that premise or the target bound.
"""
from fractions import Fraction as F
from copy import deepcopy
from math import isqrt
from flint import arb, ctx

MAX_BITS = 4096

class Meter:
    def __init__(self): self.operations = 0
    def charge(self, n=1): self.operations += n

def _q(s, meter):
    if type(s) is not str or not 1 <= len(s) <= 2500:
        raise ValueError('canonical bounded rational text required')
    meter.charge(len(s)+1)
    try: v = F(s)
    except (ValueError, ZeroDivisionError): raise ValueError('invalid rational') from None
    if str(v) != s or max(abs(v.numerator).bit_length(),v.denominator.bit_length()) > MAX_BITS:
        raise ValueError('canonical rational/bit cap')
    return v

def _integer(n, lo, hi, name):
    if type(n) is not int or not lo <= n <= hi: raise ValueError(name)
    return n

def _eq(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(_eq(a[k],b[k]) for k in a)
    if type(a) is list: return len(a)==len(b) and all(_eq(x,y) for x,y in zip(a,b))
    return a==b

def _prime(p,meter):
    for d in range(2,isqrt(p)+1):
        meter.charge()
        if p%d==0: return False
    return p>=2

def _coefficient_certificate(r,q,K):
    return {
        'schema':'centered-mobius-bound-v1','r':str(r),'theta':str(1-r),'q':q,
        'source':{'convolution':[{'kind':'power','exponent':str(-r)},{'kind':'mu','exponent':'0'}]},
        'unit':'1',
        'local':{'variable':'t','parameter':'p^-r','numerator':['1','-1'],
          'denominator':['1','-p^-r'],'prime':'p^-r-1',
          'higher_prime_power_multiplier':'p^-r','higher_prime_power_domain':'e>=2',
          'divisible_multiplier':'p^-r','coprime_multiplier':'p^-r-1',
          'divisibility_domain':'p prime,n>=1; divisible iff p divides n','prime_power_abs_bound':'1'},
        'coefficient_abs_bound':'1',
        'periodic':{'definition':'c_q=b_r-q*(delta_q*b_r)','coefficient_abs_bound':str(q+1),
          'conditional_prime_laws':{
            'hypothesis':'q is prime; no primality claim is made by this certificate',
            'q_local_numerator':['1','-(q+1)','q'],'q_local_denominator':['1','-q^-r'],
            'q_divisibility':'c_q(q*n)=q^-r*c_q(n)-(q+1)*1_(q does not divide n)*b_r(n)+q*1_(valuation_q(n)=1)*b_r(n/q)',
            'other_prime':'c_q(p*n)=p^-r*c_q(n)-1_(p does not divide n)*c_q(n), p prime distinct from q',
            'higher_q_prime_power_multiplier':'q^-r, e>=3'}},
        'normalization':{'definition':'(1-q^r)/(theta*zeta(theta))',
          'interpretation':'analytic; no ordinary mu(theta) moment asserted','absolute_ceiling':str(K),
          'ceiling_requires_independent_verification':True},
        'increment':{'definition':'a(n)=c_q(n)-kappa*(n^theta-(n-1)^theta)',
          'domain':'every integer n>=1','unit':'1-kappa','power_increment_abs_bound':'1',
          'absolute_bound':str(q+1+K)},
        'prefix_energy_bound_proved':False,'RH_proved':False}

def verify_coefficient_certificate(r='1/3',q=2,kappa_ceiling='1',certificate=None,meter=None):
    meter=Meter() if meter is None else meter
    r=_q(r,meter); _integer(q,2,4096,'integer period2..4096')
    if not 0<r<F(1,2): raise ValueError('source r in (0,1/2)')
    K=_q(kappa_ceiling,meter)
    if K.denominator!=1 or K<0: raise ValueError('nonnegative integer ceiling')
    K=int(K)
    # The local GF gives v-1 at e1 and v^(e-1)(v-1) thereafter.
    # Multiplication by (1-q*t) changes numerator to 1-(q+1)t+q*t²;
    # its valuation-one crossing is mandatory, not a geometric e2 law.
    meter.charge(128)
    expected=_coefficient_certificate(r,q,K)
    if certificate is not None and not _eq(certificate,expected):
        raise ValueError('source/local/normalization certificate changed')
    with ctx.workprec(256):
        rr=arb(r.numerator)/r.denominator; theta=1-rr
        z=theta.zeta(); kappa=(1-arb(q)**rr)/(theta*z)
        meter.charge(8192)
        if not z.is_finite() or z.contains(0) or not kappa.is_finite() or not kappa>0 or not abs(kappa)<=K:
            raise ValueError('independent analytic normalization ceiling not certified')
    return expected

def _lambda(lam,r,m,meter):
    if type(lam) is not dict: raise ValueError('typed lambda')
    if lam.get('kind')=='rational':
        if set(lam)!= {'kind','value'}: raise ValueError('rational lambda fields')
        v=_q(lam['value'],meter)
        return {'kind':'rational','value':str(v)}
    if lam.get('kind')=='prime_power':
        if set(lam)!= {'kind','prime','exponent'}: raise ValueError('prime lambda fields')
        if type(lam['prime']) is not int or lam['prime']!=m or not _prime(m,meter):
            raise ValueError('lambda base must be actual prime branch')
        if _q(lam['exponent'],meter)!=-r: raise ValueError('prime lambda exact source exponent')
        return {'kind':'prime_power','prime':m,'exponent':str(-r)}
    raise ValueError('unknown lambda kind')

def _expanded(lam,m,rho,delta,C):
    if delta==0:
        jl=str(-m*rho);cross='0'
    elif lam['kind']=='rational':
        l=F(lam['value']); jl=str(delta*l*l-m*rho); cross=str(-2*delta*l)
    else:
        jl={'constant':str(-m*rho),'power_coefficient':str(delta),
            'prime':m,'exponent':str(2*F(lam['exponent']))}
        cross={'coefficient':str(-2*delta),'prime':m,'exponent':lam['exponent']}
    return {'E_child_average':str(1+delta),'C_parent_average':cross,
            'E_parent':jl,'D':str(-C),
            'domain':'EVERY integer X>=1; exact complete centered source',
            'relation':'(1+delta)E_A-2delta*lambda*C_JA+(delta*lambda^2-m*rho)E_J-C*D<=0'}

def verify_program(program,r='1/3',q=2,kappa_ceiling='1',coefficient_certificate=None,meter=None):
    meter=Meter() if meter is None else meter
    if type(program) is not dict or set(program)!= {'id','m','lambda','rho','delta','C'}:
        raise ValueError('exact program fields; proof claims/numeric fits not admitted')
    if type(program['id']) is not str or not 1<=len(program['id'])<=256:
        raise ValueError('program id')
    m=_integer(program['m'],2,4096,'branch integer2..4096')
    rr=_q(r,meter);rho=_q(program['rho'],meter);delta=_q(program['delta'],meter);C=_q(program['C'],meter)
    if not 0<=rho<=1 or delta<0 or C<0: raise ValueError('rho[0,1], damping and forcing nonnegative')
    lam=_lambda(program['lambda'],rr,m,meter)
    source=verify_coefficient_certificate(r,q,kappa_ceiling,coefficient_certificate,meter)
    K=int(kappa_ceiling);B=F(q+1+K)
    variance=B*B*F(m*m-1,12*m)
    seed=4*B*B*(m-1)
    forcing=2*C*B*B
    if rho<1:
        madic=seed+(forcing+variance)/(1-rho); log_power=0
        rule='geometric contraction with every seed1..m-1'
    elif C==0:
        madic=seed+variance*F(m,m-1);log_power=0
        rule='summable Haar error with every seed1..m-1'
    else:
        madic=seed+variance*F(m,m-1)+forcing*F(m,m-1);log_power=1
        rule='linear iteration; log(m)>=(m-1)/m'
    # Exact negative witness for only increment-norm+unit premises.
    # H(n)=n-kappa for n>=1; A=mH+(m-1)(kappa+1/2).
    threshold=max(F(1),F(2*K),8*C*B*B/(m-rho))
    integer_ceiling=(threshold.numerator+threshold.denominator-1)//threshold.denominator
    X=1<<integer_ceiling.bit_length()
    witness=m*(m-rho)*X/4-2*m*C*B*B
    if witness<=0: raise ArithmeticError('countermodel construction')
    meter.charge(512+X.bit_length())
    primal_q=_prime(q,meter)
    result={
      'schema':'centered-mobius-program-verification-v1','verified':True,'program':deepcopy(program),
      'source_binding':{'r':r,'theta':str(1-rr),'q':q,'unit':'1-kappa',
        'kappa':'(1-q^r)/(theta*zeta(theta))','kappa_absolute_ceiling':str(K),
        'ordinary_mu_theta_series_used':False,'coefficient_certificate':source},
      'definitions':{'energy':'E_Z(X)=X^-2*sum_(X<=n<2X)Z(n)^2',
        'average':'A(n)=m^-1*sum_(j=0..m-1)J_q(m*n+j)',
        'innovation':'I(n)=A(n)-lambda*J_q(n)',
        'forcing':'D(X)=X^-1*sum_(k=1..2*m*X-1)a(k)^2',
        'covariance':'C_JI(X)=X^-2*sum_(X<=n<2X)J_q(n)*I(n)'},
      'paid_increment':{'constant':str(B),'unit_retained':True,'all_valuations_retained':True},
      'paid_boundary':{'constant':str(variance),'power':'-1',
        'identity':'E_J(mX)=E_A(X)/m+V_m(X)',
        'variance':'V_m(X)=(m^2*X^2)^-1*sum_n sum_j(J_q(mn+j)-A(n))^2',
        'domain':'EVERY integer X>=1'},
      'paid_forcing':{'constant':str(2*m*B*B),'power':'0','includes_unit':True},
      'open_covariance':{'status':'OPEN','expanded':_expanded(lam,m,rho,delta,C),
        'inequality':'2lambda*C_JI+(1+delta)E_I<=(m*rho-lambda^2)E_J+C*D',
        'finite_samples_are_not_a_proof':True,
        'endpoint_equivalent':delta==0,'lambda_cancels_when_delta_zero':delta==0},
      'conditional_recurrence':{'status':'CONDITIONAL','rho':str(rho),
        'constant_forcing':str(forcing),'decaying_forcing':str(variance),
        'inequality':'E_J(mX)+(delta/m)E_I(X)<=rho*E_J(X)+(C/m)D(X)+V_m(X)'},
      'conditional_energy_bound':{'constant':str(5*madic),'log_power':log_power,
        'scope':'EVERY integer X>=1','requires_open_covariance':True,
        'seed_count':m-1,'seed_bound':str(seed),'madic_bound_constant':str(madic),
        'cover_factor':'5','rule':rule,
        'epsilon_conversion':'log_power0: C; log_power1: C*(1+1/epsilon), EVERY epsilon>0'},
      'arithmetic_innovation':{
        'status':'EXACT_IDENTITY_ONLY','q_is_prime':primal_q,
        'q_crossing_retained':True,
        'q_prime_formula':None if not primal_q else
          'P_c(q*x)=q^-r*P_c(x)+O_q(q*x)-(q+1)*O_q(x)+q*O_q(x/q)',
        'q_prime_O':'O_q(x)=sum_(n<=x,q does not divide n)b_r(n)',
        'no_prime_free_prefix_bound_proved':True},
      'proof_attempt':{'status':'GENERIC_INCREMENT_RULE_REJECTED',
        'scope':'bounded centered increments and retained unit ONLY; actual Euler/coefficient-source laws not imposed',
        'countermodel':{'H0':'0','H_positive_integer':'n-kappa','a1':'1-kappa','later_a':'1',
          'kappa_domain':[str(0),str(K)],'X':str(X),'strict_defect_lower':str(witness),
          'actual_source_laws_satisfied':False,'actual_target_refuted':False}},
      'dependency_graph':[
        {'id':'source','status':'PROVED','depends_on':[]},
        {'id':'increments','status':'PROVED','depends_on':['source']},
        {'id':'haar_variance','status':'PROVED','depends_on':['increments']},
        {'id':'forcing','status':'PROVED','depends_on':['increments']},
        {'id':'signed_covariance','status':'OPEN','depends_on':['source']},
        {'id':'conditional_implication','status':'CONDITIONAL','depends_on':['haar_variance','forcing','signed_covariance']},
        {'id':'uniform_target','status':'OPEN','depends_on':['conditional_implication','signed_covariance']}],
      'covariance_proved':False,'uniform_target_bound_proved':False,
      'whole_signed_bound_proved':False,'RH_proved':False}
    return result
