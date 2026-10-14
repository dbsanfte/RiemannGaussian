"""Independent admission of a reviewed all-scale moving-profile obstruction.

No new producer imports, empirical norms, source arrays or finite tail probes.
"""
from fractions import Fraction as Q
import json
import check_floor_residual_drift_045 as DRIFT

class Meter:
    def __init__(self,cap=50000000):self.operations=0;self.cap=cap
    def charge(self,n=1):
        if type(n) is not int or n<0 or n>self.cap-self.operations:raise OverflowError('global rate work cap')
        self.operations+=n

def _meter(m):return Meter() if m is None else m

def rational(text,meter):return DRIFT.rational(text,meter)

def _equal(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(_equal(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_equal(x,y) for x,y in zip(a,b))
    return a==b

ROUNDING={'kind':'dyadic_power_floor','bits_multiplier':4,'scale':'ceil_log2_N',
  'drift':'round_each_exponential_before_signed_sum','product':'multiply_rounded_children_exactly'}

def _request(request,meter):
    if type(request) is not dict or set(request)!={'recipe','q','b','domain','rounding','bound'}:
        raise ValueError('exact all-scale rate request')
    try:size=len(json.dumps(request,sort_keys=True,separators=(',',':'),allow_nan=False))
    except (TypeError,ValueError):raise ValueError('finite JSON request') from None
    if size>65536:raise OverflowError('guard input size cap')
    meter.charge(1+size//64)
    recipe=request['recipe']
    if type(recipe) is not dict or set(recipe)!={'id','base','auxiliary'} or type(recipe['id']) is not str or len(recipe['id'])>256:
        raise ValueError('typed source recipe')
    q=request['q']
    if type(q) is not int or not 2<=q<=4096:raise ValueError('fixed integer dilation2..4096')
    b=rational(request['b'],meter)
    domain=request['domain']
    if type(domain) is not dict or set(domain)!={'kind','minimum'} or domain['kind'] not in ('all_integer','geometric_chain') or type(domain['minimum']) is not int or not 2<=domain['minimum']<=2**31:
        raise ValueError('all integer or specified unbounded chain domain')
    if not _equal(request['rounding'],ROUNDING):raise ValueError('different exact rounding operator')
    bound=request['bound']
    if type(bound) is not dict or set(bound)!={'A','eta'}:raise ValueError('uniform rate bound schema')
    A=rational(bound['A'],meter);eta=rational(bound['eta'],meter)
    if A<=0 or eta<=0:raise ValueError('positive fixed rational bound and rate')
    bare=type(recipe['base']) is dict and recipe['base'].get('kind')=='drift_mixture' and recipe['auxiliary'] is None
    if bare:
        a,theta,terms=DRIFT.parse_spec(recipe['base'],meter)
        return recipe,q,b,A,eta,domain,a,theta,terms
    return recipe,q,b,A,eta,domain,None,None,None

# These descriptors state the independently reviewed analytic rule. Each
# source/unit/tail/domain field is mandatory; they are not inferred from data.
def _rule_fields():
    return {
      'source_binding':{
        'source':'actual ordinary Mobius mu; not an arbitrary sign source',
        'basis':'f_n(x)=floor(1/x)/n-floor(1/(n*x)) on 0<x<=1, zero beyond1',
        'coefficients':'c_n(N)=-mu(n)*sum_j w_j*floor_dyadic(n^(-r_j*beta_N)); 2<=n<=N',
        'external_taper_or_auxiliary':False},
      'whole_mellin':{
        'finite_source':'A_N(s)=sum_(1<=n<=N) mu(n)*V_N^rounded(n)*n^(-s)',
        'unit':'n=1 cancels identically in A_N(s)-A_N(1)',
        'target':'M e_N(s)=[1-zeta(s)*(A_N(s)-A_N(1))]/s',
        'forcing':'M h_N(s)=[1-b*q^(-s)-zeta(s)*(A_(qN)(s)-A_(qN)(1)-b*q^(-s)*(A_N(s)-A_N(1)))]/s',
        'indicator_and_signed_parent_child_terms_retained':True},
      'RH_false_branch':{
        'off_line_zero':'rho with Re(rho)>1/2 exists if RH is false, by zeta zero symmetry',
        'exact_response':'M h_N(rho)=(1-b*q^(-rho))/rho',
        'Cauchy_lower_bound':'||h_N||^2>=(2*Re(rho)-1)*|1-b*q^(-rho)|^2/|rho|^2>0 for every N',
        'reason_multiplier_nonzero':'|b|*q^(-Re(rho))<1','no_source_tail_or_RH_assumption':True},
      'RH_true_branch':{
        'imported_theorem':{
          'author':'K. Soundararajan','title':'Partial sums of the Mobius function',
          'primary_source':'https://arxiv.org/pdf/0705.0723','location':'Theorem1','hypothesis':'RH',
          'bound':'|M(x)|<=C*sqrt(x)*exp(sqrt(log x)*(loglog x)^14), eventually','imported_not_discovered':True},
        'tail':{
          'exact_formula':'sum_(n>K) mu(n)*n^(-z)=-M(K)*K^(-z)+z*integral_K^infinity M(x)*x^(-z-1)dx',
          'scope':'Re(z)=1/2+r*beta_K, K=N or qN, bounded imaginary part',
          'monotonicity':'y^(-1/2)*(log y)^14 decreases once log y>28',
          'eventual_condition':'rmin*beta_K>=2*(log K)^(-1/2)*(loglog K)^14',
          'why_condition_holds':'theta>1/2, beta_K*log K~constant*(log K)^theta',
          'bound':'O((1+|z|/beta_K)*exp(-rmin*beta_K*log K/2))=o(1)',
          'uniformity':'uniform on a bounded beta_N-scaled frequency window; NOT a global critical-line tail energy bound',
          'series_scope':'shifted source series convergence follows here from the imported RH bound, never assumed on Re(s)=1/2'},
        'paid_harmonic':{
          'bound':'|A_N(1)|<=beta_N*sum_j|w_j|r_j+sum_j|w_j|*N^(-r_j*beta_N)/(r_j*beta_N)+Cw*N^(-4)*(1+log N)=O(beta_N)',
          'reason':'zeta(1+kappa)>=1/kappa and absolute harmonic tails; no RH needed'},
        'rounding':{'coefficient_error':'<=Cw*N^(-4)',
          'local_Dirichlet_error':'<=2*Cw*N^(-7/2) on Re(s)=1/2',
          'harmonic_error':'<=Cw*N^(-4)*(1+log N)','child_rounding_recomputed':True},
        'critical_zero':'choose one known ordinary critical-line zero rho, with any finite multiplicity d>=1',
        'local_zero_expansion':'zeta(rho+z)=C*z^d*(1+O(z)), C!=0',
        'scaled_frequency':'s=rho+i*beta_N*v',
        'boundary_layer':'F_d(v)=1-(i*v)^d*sum_j w_j/(r_j+i*v)^d; F_d(0)=1',
        'full_uniform_limit':'M h_N(rho+i*beta_N*v)->(1-b*q^(-rho))*F_d(v)/rho uniformly for v in any fixed compact interval',
        'nonzero_scale_factor':'|1-b*q^(-rho)|>=1-|b|/sqrt(q)>0',
        'local_energy':'a nonzero fixed v-window and Mellin Plancherel give ||h_N||^2>=c*beta_N eventually, c>0',
        'all_crosses_retained':True,'zero_simplicity_assumed':False},
      'unconditional_lower_bound':{
        'statement':'there exist c>0 and N_star such that ||h_N||^2>=c*beta_N for every integer N>=N_star',
        'argument':'RH true: local boundary layer; RH false: uniform positive zero witness and beta_N->0',
        'constants':'symbolic/non-effective in this certificate; no computed c or N_star',
        'geometric_scope':'therefore the same lower rate holds on every specified unbounded geometric chain'},
      'stable_recurrence':{
        'identity':'e_(qN)=b*D_q e_N+h_N, ||D_q||=q^(-1/2)',
        'hypothetical_vanishing_forcing':'would imply e_N->0 on the specified q-chain; all_integer domains contain such chains',
        'role':'valid implication, but not needed for the stronger direct RH-false/true case split'},
      'proof_guards':{
        'bare_profile_only':True,'finite_cutoff_paid_locally':True,'global_truncation_energy_paid':False,
        'moment_cancellation_required_for_lower_rate':False,'known_zero_and_RH_Mertens_facts_imported':True,
        'RH_not_used_to_prove_an_upper_bound':True,'finite_certified_norms_unchanged':True,
        'theta_at_most_half_or_eta_equality_not_refuted':True}}


def verify_guard(request,certificate,meter=None):
    m=_meter(meter)
    try:parsed=_request(request,m)
    except ValueError:parsed=None
    supported=False
    if parsed is not None:
        recipe,q,b,A,eta,domain,a,theta,terms=parsed
        supported=terms is not None and theta>Q(1,2) and b*b<q and eta>1-theta
    if not supported:
        keys={'schema','status','reason','advertised_uniform_rate_refuted','unpaid_rate_status','norm_convergence_status','RH_status'}
        if type(certificate) is not dict or set(certificate)!=keys:
            raise ValueError('unsupported guard schema')
        expected={'schema':'floor-residual-global-rate-guard-046-v1','status':'UNSUPPORTED',
          'advertised_uniform_rate_refuted':False,'unpaid_rate_status':'OPEN','norm_convergence_status':'OPEN','RH_status':'OPEN'}
        if not _equal({k:certificate[k] for k in expected},expected) or type(certificate['reason']) is not str or not 1<=len(certificate['reason'])<=1000:
            raise ValueError('unsupported scope cannot refute a rate or prove convergence')
        m.charge(30)
        return {'verified':True,'status':'UNSUPPORTED','advertised_uniform_rate_refuted':False,
          'norm_convergence_status':'OPEN','RH_proved':False,'RH_refuted':False}
    Cw=sum((abs(w) for _,w in terms),Q(0));weighted=sum((abs(w)*r for r,w in terms),Q(0))
    dynamic=(a,theta,1-theta,theta-Q(1,2),eta-(1-theta),q-b*b,b*b/q,Cw,weighted,A/a)
    for v in dynamic:
        # Match the bounded exact coefficient scope, without meter.number().
        rational(str(v),m)
    expected={'schema':'floor-residual-global-rate-guard-046-v1','status':'REFUTED_UNIFORM_LOG_RATE','request':request,
      'advertised_uniform_rate_refuted':True,'norm_convergence_status':'OPEN','RH_status':'OPEN',
      'RH_proved':False,'RH_refuted':False,'source_values_evaluated':False,'norms_evaluated':False,
      'numerical_lower_constant_claimed':False,'explicit_failing_support_claimed':False,
      'exact_conditions':{
        'a':str(a),'theta':str(theta),'beta_power':str(1-theta),
        'tail_dominance_gap_theta_minus_half':str(theta-Q(1,2)),
        'rate_gap_eta_minus_beta_power':str(eta-(1-theta)),
        'contraction_margin_q_minus_b_squared':str(q-b*b),'squared_recurrence_ratio':str(b*b/q),
        'sum_weights':'1','sum_abs_weights':str(Cw),'sum_abs_weighted_rates':str(weighted),
        'rmin':str(terms[0][0]),'rmax':str(terms[-1][0])},
      'beta_transfer':{
        'level':'L(N)=1+floor(log2 N)','definition':'ceil(a*L(N)^theta)/L(N)',
        'asymptotic':'beta_N~a*L(N)^(-(1-theta))','child_level_gap_upper_bound':(q-1).bit_length(),
        'child_recomputed':True,'child_beta_ratio':'beta_(qN)/beta_N->1',
        'precision':'4*ceil(log2 N), recomputed at qN',
        'ceiling_relative_error':'O(L^(-theta)); no beta monotonicity assumed'},
      'rate_contradiction':{
        'advertised_bound':'||h_N||^2<=A*L(N)^(-eta)',
        'comparison':'A*L^(-eta)/beta_N<=(A/a)*L^(-(eta-(1-theta)))->0',
        'constant_A_over_a':str(A/a),'uniform_domain_refuted':domain,
        'equality_or_slower_rate':'OPEN; this guard proves no attainability or uniform upper bound'}}
    expected.update(_rule_fields())
    if not _equal(certificate,expected):raise ValueError('changed source, proof premise, exact gate or scope')
    m.charge(1+len(json.dumps(expected,separators=(',',':')))//64)
    # Positivity on this symbolic v-window follows uniformly for every d>=1:
    # |1-F_d(v)|<=Cw*(|v|/rmin)^d<=1/2 when |v|<=rmin/(2Cw).
    # This is not a computed lower c or effective failing support threshold.
    window=terms[0][0]/(2*Cw)
    return {'verified':True,'status':'REFUTED_UNIFORM_LOG_RATE','advertised_uniform_rate_refuted':True,
      'refuted_eta_strictly_above':str(1-theta),'formal_boundary_layer_halfwidth':str(window),
      'actual_lower_constant_and_threshold_computed':False,
      'source_scope':'bare actual ordinary Mobius drift profile, separate exact dyadic rounding',
      'imported_conditional_theorem':'Soundararajan Theorem1, https://arxiv.org/pdf/0705.0723',
      'global_tail_energy_bound_claimed':False,'norm_convergence_status':'OPEN',
      'whole_signed_bound_proved':False,'RH_proved':False,'RH_refuted':False}
