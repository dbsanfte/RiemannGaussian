"""Independent source admission of a finite factored quadratic short repair.

Rebuilds thresholds, ordinary mu and every Pf/PG entry. The immutable063
forward repair checker is reused; no discovery producer or source data is.
"""
from fractions import Fraction as Q
import check_mobius_mass_conservation_060 as MASS
import check_mobius_prefix_repair_063 as REPAIR

Meter=MASS.Meter
MAX_N=65536
EXPRESSION='c_j=sum_(m<=H/j)u_m*[Pf-PG*u]_(j*m)-sum_(m<=H/(j+1))u_m*[Pf-PG*u]_((j+1)*m)'


def _integer(n,minimum,maximum):
    if type(n) is not int or not minimum<=n<=maximum:raise ValueError('bounded strict source integer')
    return n


def _ordinary_mu(radius,m):
    """Smallest-factor sieve followed by separate valuation factorization."""
    factors=list(range(radius+1));factors[1]=1
    for p in range(2,radius+1):
        m.charge(4)
        if factors[p]!=p:continue
        for n in range(p*p,radius+1,p):
            if factors[n]==n:factors[n]=p
            m.charge(4)
    mu=[0]*(radius+1);mu[1]=1
    for n in range(2,radius+1):
        remainder=n;sign=1
        while remainder>1:
            p=factors[remainder];remainder//=p;sign=-sign;m.charge(8)
            if remainder%p==0:sign=0;break
        mu[n]=sign
    return mu


def _weight(N,base,d,m):
    m.charge(20)
    return (4*N)//(base*d)-3*((2*N)//(base*d))+2*(N//(base*d))


def _shape(obj,outer,inner):
    if type(obj) is not list or len(obj)!=outer or any(type(row) is not list or len(row)!=inner for row in obj):
        raise ValueError('complete source matrix dimensions')


def verify_quadratic(lift,repair,meter=None):
    m=Meter() if meter is None else meter
    MASS._fields(lift,('schema','parameters','N','y','H','rule','K','arithmetic_radius',
        'ordinary_mu_through_radius','linear_terms','long_kernels_after_fill','expression',
        'same_u_sequence_in_both_factors','arithmetic_degree_at_most',
        'formal_source_only_factorization_reviewed','producer_exact_replay',
        'independent_quadratic_schema_admission','independent_whole_completion_admission_still_required',
        'uniform_quadratic_variation_bound_proved','RH_proved'))
    MASS._expect(lift['schema'],'mobius-factored-quadratic-repair-v1')
    alpha,gamma,tau,ps,p,q,period=MASS._parameters(lift['parameters'],m)
    N=_integer(lift['N'],2,MAX_N);D=(4*N)//p
    H=_integer(lift['H'],1,min(4096,D));y=_integer(lift['y'],1,D)
    rule=lift['rule']
    if type(rule) is not str or rule not in REPAIR.RULES:raise ValueError('licensed linear fill')
    K=y//(H+1);radius=max(H,K)
    if type(lift['K']) is not int or lift['K']!=K or type(lift['arithmetic_radius']) is not int or lift['arithmetic_radius']!=radius:
        raise ValueError('complete inverse-index and arithmetic radius')
    MASS._expect(lift['expression'],EXPRESSION)
    for key,value in (('same_u_sequence_in_both_factors',True),('arithmetic_degree_at_most',2),
            ('formal_source_only_factorization_reviewed',True),('producer_exact_replay',True),
            ('independent_quadratic_schema_admission',False),('independent_whole_completion_admission_still_required',True),
            ('uniform_quadratic_variation_bound_proved',False),('RH_proved',False)):
        MASS._expect(lift[key],value)
    if type(repair) is not dict:raise ValueError('typed linked repair')
    for key,value in (('primes',ps),('H',H),('rule',rule)):MASS._expect(repair.get(key),value)
    repair_proof=REPAIR.verify_repair(repair,m)
    _shape(lift['linear_terms'],2,H)
    kernels=lift['long_kernels_after_fill']
    if type(kernels) is not list or len(kernels)!=2:raise ValueError('two endpoint source kernels')
    for matrix in kernels:_shape(matrix,H,K)
    supplied_mu=lift['ordinary_mu_through_radius']
    if type(supplied_mu) is not list or len(supplied_mu)!=radius or any(type(x) is not int or x not in (-1,0,1) for x in supplied_mu):
        raise ValueError('complete signed ordinary-mu table')
    mu=_ordinary_mu(radius,m)
    if supplied_mu!=mu[1:]:raise ValueError('ordinary-mu factorization mismatch')
    # H*K <=D: matrices are prospectively bounded by the fixed N source cap.
    if H*K>2*N:raise OverflowError('prospective kernel dimension')
    m.charge(4*H*max(1,K)+radius+100)
    raw=[[[0]*K for _ in range(H)] for _ in range(2)];threshold_count=0
    for channel,base in enumerate((p,q)):
        for factor,sign in ((4,1),(2,-3),(1,2)):
            Z=(factor*N)//base
            for index in range(1,Z//(H+1)+1):
                T=min(y,Z//index);threshold_count+=1;m.charge(20)
                for ell in range(1,T//(H+1)+1):
                    X=T//ell
                    for d in range(1,H+1):
                        raw[channel][d-1][ell-1]+=sign*(X//d);m.charge(12)
    ratios=[Q(p,q),Q(1)]
    source=[[Q(_weight(N,p,d,m))-r*_weight(N,q,d,m) if d<=y else Q(0)
        for d in range(1,H+1)] for r in ratios]
    pf,_=REPAIR._fills(source,H,ps,rule,m)
    for e in range(2):
        for d in range(H):
            if MASS._rational(lift['linear_terms'][e][d],m)!=pf[e][d]:raise ValueError('source linear fill entry')
    reconstructed=[row.copy() for row in pf];raw_residual=[row.copy() for row in source]
    for ell in range(K):
        columns=[[MASS._bounded(Q(raw[0][d][ell])-r*raw[1][d][ell],m) for d in range(H)] for r in ratios]
        pg,_=REPAIR._fills(columns,H,ps,rule,m)
        for e in range(2):
            for d in range(H):
                if MASS._rational(kernels[e][d][ell],m)!=pg[e][d]:raise ValueError('source long kernel fill entry')
                reconstructed[e][d]=MASS._bounded(reconstructed[e][d]-pg[e][d]*mu[ell+1],m)
                raw_residual[e][d]=MASS._bounded(raw_residual[e][d]-columns[e][d]*mu[ell+1],m)
    MASS._expect(repair['residuals'],[[str(x) for x in row] for row in raw_residual])
    MASS._expect(repair['filled'],[[str(x) for x in row] for row in reconstructed])
    m.charge(200)
    return {'verified':True,'schema':'verified-mobius-quadratic-source-v1','parameters':lift['parameters'],
        'N':N,'y':y,'H':H,'rule':rule,'K':K,'arithmetic_radius':radius,
        'ordinary_mu_independently_verified':True,'same_u_sequence_in_both_factors_proved':True,
        'raw_residual_source_binding_proved':True,'every_Pf_and_PG_entry_verified':True,
        'quadratic_source_factorization_proved':True,'arithmetic_degree_at_most':2,
        'generic_long_source_definition':'all signed truncated-floor indicator thresholds with complete inner ordinary-mu inverse',
        'threshold_terms_rebuilt':threshold_count,'kernel_entries_verified':2*H*K,
        'source_generic_completion_identity_proved':True,
        'linked_repair_identity_proved':repair_proof['repair_identity_proved'],
        'coefficient_l1':repair_proof['coefficient_l1'],
        'saved_whole_completion_bytes_verified':False,'whole_saved_candidate_requires_062_admission':True,
        'uniform_quadratic_variation_bound_proved':False,'whole_signed_target_bound_proved':False,'RH_proved':False,
        'scientific_source_tables_or_LP_evaluated':False}
