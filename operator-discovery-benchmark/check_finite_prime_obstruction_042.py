"""Independent finite-prime countermodel certificate; actual source not refuted.

No producer imports, source arrays, coefficient observations or old test runs.
"""
from fractions import Fraction as F
from math import isqrt
from flint import arb,ctx

MAX_INPUT_BITS=4096
MAX_PROOF_BITS=8192

class Meter:
    def __init__(self,cap=50000000):self.operations=0;self.cap=cap
    def charge(self,n=1):
        if type(n) is not int or n<0 or n>self.cap-self.operations:raise OverflowError('work cap')
        self.operations+=n

def _q(s,meter):
    if type(s) is not str or not 1<=len(s)<=2500:raise ValueError('bounded canonical rational text')
    meter.charge(len(s)+1)
    try:v=F(s)
    except (ValueError,ZeroDivisionError):raise ValueError('invalid rational') from None
    if str(v)!=s or max(abs(v.numerator).bit_length(),v.denominator.bit_length())>MAX_INPUT_BITS:
        raise ValueError('canonical rational bit cap')
    return v

def _int(n,minimum,bits,name):
    if type(n) is not int or n<minimum or n.bit_length()>bits:raise ValueError(name)
    return n

def _integer_text(s,meter):
    if type(s) is not str or not 1<=len(s)<=2500:raise ValueError('integer proof text')
    try:n=int(s)
    except ValueError:raise ValueError('integer proof text') from None
    if str(n)!=s or n<0 or n.bit_length()>MAX_PROOF_BITS:raise ValueError('canonical integer proof cap')
    meter.charge(n.bit_length()+1)
    return n

def _prime(n,meter):
    _int(n,2,MAX_INPUT_BITS,'prime input')
    if n==2:return True
    if n%2==0:return False
    bound=isqrt(n)
    # Meter before primality trial work, also preventing enormous trial loops.
    meter.charge(max(1,(bound-1)//2))
    return all(n%d for d in range(3,bound+1,2))

def _eq(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(_eq(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_eq(x,y) for x,y in zip(a,b))
    return a==b

def _power(n,e,meter):
    estimate=1 if n==1 else n.bit_length()*e
    if estimate>MAX_PROOF_BITS:raise ValueError('power certificate resource cap')
    meter.charge(estimate+e.bit_length()+1)
    return pow(n,e)

def _threshold(claim,theta,k,L,meter):
    if type(claim) is not dict or set(claim)!={'X','j','ratio','theta_numerator','theta_denominator',
       'powered_numerator','powered_denominator','lhs','rhs','comparison','minimal_dyadic'}:
        raise ValueError('complete threshold proof')
    j=_int(claim['j'],0,MAX_INPUT_BITS,'dyadic exponent')
    ratio=k/(2*L)
    num=_power(ratio.numerator,theta.denominator,meter)
    den=_power(ratio.denominator,theta.denominator,meter)
    if j>MAX_PROOF_BITS-1 or num.bit_length()+j*theta.numerator>MAX_PROOF_BITS:
        raise ValueError('dyadic shift proof size')
    lhs=num<<(j*theta.numerator);X=1<<j
    meter.charge(lhs.bit_length()+X.bit_length()+8)
    if lhs<den or (j and num<<((j-1)*theta.numerator)>=den):
        raise ValueError('threshold not valid/minimal')
    expected={'X':str(X),'j':j,'ratio':str(ratio),'theta_numerator':theta.numerator,
      'theta_denominator':theta.denominator,'powered_numerator':str(num),
      'powered_denominator':str(den),'lhs':str(lhs),'rhs':str(den),
      'comparison':'>=','minimal_dyadic':True}
    # Parse all claimed integer strings before equality so malformed huge values fail closed.
    for key in ('X','powered_numerator','powered_denominator','lhs','rhs'):_integer_text(claim[key],meter)
    if not _eq(claim,expected):raise ValueError('altered exact threshold witness')
    return expected

def verify(proposal,meter=None):
    meter=Meter() if meter is None else meter
    if type(proposal) is not dict:raise ValueError('certificate object')
    p=proposal.get('parameters')
    if type(p) is not dict or set(p)!={'primes','r','theta','q','k_lower','K_upper'}:
        raise ValueError('parameter binding')
    P=p['primes']
    if type(P) is not list or len(P)>1024 or any(type(x) is not int for x in P) or P!=sorted(set(P)):
        raise ValueError('sorted distinct registered integer primes')
    for prime in P:
        if not _prime(prime,meter):raise ValueError('registered value not prime')
    r=_q(p['r'],meter);k=_q(p['k_lower'],meter)
    q=_int(p['q'],2,MAX_INPUT_BITS,'period integer>=2')
    K=_int(p['K_upper'],1,MAX_INPUT_BITS,'strict positive integer ceiling')
    if not 0<r<F(1,2) or not 0<k<=K:raise ValueError('r and scalar intervals')
    theta=1-r
    if p['theta']!=str(theta):raise ValueError('wrong theta')
    h_bound=1<<(2*len(P));L=(q+1)*h_bound
    if L.bit_length()>MAX_PROOF_BITS:raise ValueError('l1 bound resource cap')
    meter.charge(L.bit_length()+len(P)*96)
    threshold=_threshold(proposal.get('threshold'),theta,k,L,meter)
    with ctx.workprec(256):
        rr=arb(r.numerator)/r.denominator;tt=1-rr
        kk=arb(k.numerator)/k.denominator
        z=tt.zeta();kap=(1-arb(q)**rr)/(tt*z)
        meter.charge(8192)
        if not z.is_finite() or z.contains(0) or not kap.is_finite() or not kap>0 or not kk<=kap or not kap<=K:
            raise ValueError('analytic scalar lower/upper independently uncertified')
    # Missing-prime witness is exact, and checked minimal to bind the claimed diagnostic.
    missing=2;registered=set(P)
    while missing in registered or not _prime(missing,meter):
        missing+=1;meter.charge()
    rows=[]
    for prime in P:
        rows.append({'prime':prime,'v':{'kind':'prime_power','prime':prime,'exponent':str(-r)},
          'v_domain':'0<v<1','u_numerator':['1','-1'],'u_denominator':['1','-v'],
          'h_numerator':['1','-2','1'],'h_denominator':['1','-v'],
          'u_e0':'1','u_e_ge1':'(v-1)*v^(e-1)','h_e0':'1','h_e1':'v-2',
          'h_e_ge2':'(1-v)^2*v^(e-2)','h_l1':'4-2*v','h_l1_upper':'4'})
    expected={
      'schema':'finite-prime-obstruction-v1','parameters':{'primes':P,'r':str(r),'theta':str(theta),
        'q':q,'k_lower':str(k),'K_upper':K},
      'quantifier':'for any fixed finite set P of distinct actual primes',
      'assumptions':{'analytic_scalar':'(1-q^r)/(theta*zeta(theta))','scalar_bounds':'0<k<=kappa<=K',
        'scalar_bounds_require_independent_verification':True,'ordinary_mu_theta_series_convergence_used':False},
      'definitions':{'u_unit':'1','u_registered':'(p^-r-1)*p^(-r*(e-1)), e>=1, p in P',
        'u_unregistered':'1, e>=1, p not in P','u_multiplicative':True,'u_coefficient_abs_bound':'1',
        'divisor_identity':'u=One*h_P','g':'(delta-q*delta_q)*h_P',
        'c':'(delta-q*delta_q)*u=One*g','J':'prefix(c)(x)-kappa*x^theta','J_zero':'0','c_unit':'1',
        'energy':'X^-2*sum_(X<=n<2X)J(n)^2'},
      'local_laws':{'registered':rows,'unregistered':{'u_e_ge0':'1','h_e0':'1','h_e_ge1':'0'}},
      'norms':{'h_l1_upper':str(h_bound),'g_l1_upper':str(L),
        'factorization':'sum|h_P|=product_(p in P)(4-2*p^-r)<=4^|P|',
        'g_triangle':'sum|g|<=(q+1)*sum|h_P|'},
      'periodic':{'q':q,'multiplier_coefficients':['1',str(-q)],'harmonic_multiplier':'0',
        'harmonic_identity':'sum g(d)/d=(1-q/q)*sum h_P(d)/d=0',
        'prefix_identity':'prefix(c)(x)=sum g(d)*(floor(x/d)-x/d)',
        'prefix_abs_bound':str(L),'prefix_domain':'every real x>=0',
        'absolute_series_justifies_interchange':True},
      'first_missing_prime':{'prime':missing,'u_value':'1','required_value':'p^-r-1',
        'required_value_range':'(-1,0)','signed_gap':'2-p^-r','signed_gap_strict_lower':'1',
        'registered_prime_laws_retained':True},
      'threshold':threshold,
      'energy_obstruction':{'lower_constant':str(k*k/4),'exponent':str(1-2*r),
        'domain':'every integer X>=threshold.X',
        'centered_abs_lower':'(k/2)*n^theta for every integer n>=threshold.X',
        'energy_lower':'(k^2/4)*X^(1-2*r)','energy_exponent_strictly_positive':True,
        'growth_disproves_uniform_subpower_for_fake':True,'upper_centered_bound':'K*x^theta+L'},
      'source_scope':{'fake_dirichlet_series':'zeta(s)*H_P(s)',
        'H_P':'product_(p in P)(1-p^-s)^2/(1-p^(-(s+r)))',
        'fake_periodic_dirichlet_series':'(1-q^(1-s))*zeta(s)*H_P(s)',
        'fake_periodic_has_theta_pole':False,'retains_actual_global_meromorphic_identity':False,
        'retains_actual_center_as_its_own_residue':False,'excluded_by_actual_all_prime_source_binding':True,
        'grammar_scope':'only finitely many registered prime laws plus unit and coefficient bound',
        'purpose':'negative calibration of insufficient proof grammars'},
      'source_counterexample':False,'covariance_bound_proved':False,'actual_all_prime_bound_proved':False,
      'RH_proved':False,'RH_refuted':False,'actual_source_values_generated':False,
      'actual_normalization_evaluated':False}
    # Producer work counters are descriptive, never proof premises or verifier accounting.
    counts=proposal.get('counts')
    if type(counts) is not dict or set(counts)!={'operations','peak_integer_bits'}:
        raise ValueError('descriptive work counter shape')
    _int(counts['operations'],0,MAX_INPUT_BITS,'operation counter')
    peak=_int(counts['peak_integer_bits'],0,MAX_INPUT_BITS,'peak integer counter')
    if peak>MAX_PROOF_BITS:raise ValueError('producer proof-size counter')
    expected['counts']=counts
    if not _eq(proposal,expected):raise ValueError('altered local/norm/floor/energy/source-scope certificate')
    meter.charge(1024)
    return {'verified':True,'schema':'finite-prime-obstruction-verification-v1',
      'registered_prime_count':len(P),'first_missing_prime':missing,
      'uniform_fake_prefix_bound':str(L),'threshold':threshold['X'],
      'fake_energy_lower':{'constant':str(k*k/4),'power':str(1-2*r),'log_power':0,
        'domain':'EVERY integer X>=threshold'},
      'subpower_counterexample_epsilon':str((1-2*r)/2),
      'finite_prime_only_rule_obstructed':True,
      'all_041_covariance_programs_fail_for_this_model':True,
      'covariance_failure_scope':'conditional Haar implications use retained increments/unit; actual-source laws not satisfied',
      'analytic_scalar_bounds_independently_verified':True,
      'retains_actual_source_global_residue_identity':False,
      'actual_source_refuted':False,'existing_041_source_binding_refuted':False,
      'RH_proved':False,'RH_refuted':False,'source_coefficient_observations':0}
