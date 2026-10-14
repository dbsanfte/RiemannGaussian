"""New056 source-rule replays; no scientific arrays or old suite calls."""
import copy
from fractions import Fraction as Q
from itertools import combinations
from math import gcd
import unittest

import check_prime_insertion_core_056 as C
import prime_insertion_core_search_056 as P
from prime_bank_candidates import Meter as PipelineMeter

M=C.Meter(cap=100_000_000,seconds=180)
PM=P.Meter(cap=100_000_000,seconds=180)
PIPE=PipelineMeter(cap=100_000_000,seconds=180)


def tail(tau='1/2',primes=None,alpha='1/5'):
    request={'alpha':alpha,'primes':[] if primes is None else primes,'tau':tau}
    return request,P.tail_certificate(request,PM)


def jet(features=None,coefficients=None):
    request={'features':[[],[2],[3],[2,3]] if features is None else features,
        'coefficients':['1','-1','-1','1'] if coefficients is None else coefficients}
    return request,P.jet_certificate(request,PM)


def recovery(tau='1/2',primes=None,eta='0',low='1'):
    request={'tail_request':{'alpha':'1/5','primes':[] if primes is None else primes,'tau':tau},
        'low_core':{'constant':low,'log_power':eta,'status':'OPEN'}}
    return request,P.recovery_certificate(request,PM)


def recovery_schema(tau='1/2',primes=None,eta='0'):
    request={'tail_request':{'alpha':'1/5','primes':[] if primes is None else primes,'tau':tau},'log_power':eta}
    # Hand-written generic implication fixture; no producer oracle.
    T=Q(tau);s=0 if primes is None else len(primes);count=2**s
    if T<1:ctail=16*count/(T*T*(1-T))
    elif T==1:ctail=Q(20*count)
    else:ctail=4*count*T/(T-1)
    compatible=T>=Q(1,2)
    certificate={'schema':'prime-insertion-low-core-recovery-schema-v1','request':copy.deepcopy(request),
        'source_split':'t_S(N)=low_core_(0,tau)(N)+tail_(tau,infinity)(N)',
        'log_weight':'(1+log(N))^log_power','tail_square_root_compatible':compatible,
        'tail_square_root_constant':str(ctail) if compatible else None,
        'full_constant':{'C_low_coefficient':'1','offset':str(ctail)} if compatible else None,
        'log_power':eta,'minimum':2,
        'status':'PAID_CONDITIONAL_IMPLICATION_WITH_OPEN_PREMISE' if compatible else 'TAIL_PROVIDER_INSUFFICIENT',
        'conditional_original_target_implication':not request['tail_request']['primes'] and compatible,
        'low_core_constant_quantifier':'FOR EVERY finite C_low>=0',
        'open_premise':'|low_core_(0,tau)(N)|<=C_low*sqrt(N)*(1+log(N))^log_power for EVERY integer N>=2',
        'low_core_bound_proved':False,'complete_target_bound_proved':False,'RH_proved':False}
    return request,certificate


def microscopic(alpha='1/5',primes=None,gamma='1/2'):
    primes=[2,3] if primes is None else primes
    R=1
    for p in primes:R*=p
    r={'alpha':alpha,'primes':primes,'gamma':gamma}
    k=len(primes)
    c={'schema':'prime-insertion-microscopic-bound-v1','request':copy.deepcopy(r),
        'product':R,'prime_count':k,'integer_N_minimum':2,
        'operator':'E_R K(n)=K(R*n), n>=2',
        'filter':{'q':2,'coefficients':[2,-3,1],'normalization':'divide_by_alpha'},
        'integrand':'sum_(2<=n<=4N)w_P(n,N)*prod_(p|R*n)(1-p^-t)',
        'filter_absolute_mass':'4*N','cutoff':'epsilon_N=min(1/2,N^-gamma)',
        'upper_bound':{'constant':str(Q(12*R)/(k-Q(alpha))),
            'N_power':str(1-Q(gamma)*(k-Q(alpha)))},
        'unpaid_middle':'epsilon_N<t<1/2','near_zero_bound_proved':True,
        'complete_target_bound_proved':False,'RH_proved':False}
    return r,c


def factors(n):
    rows=[];p=2
    while p*p<=n:
        exponent=0
        while n%p==0:n//=p;exponent+=1;M.charge()
        if exponent:rows.append((p,exponent))
        p+=1;M.charge()
    if n>1:rows.append((n,1))
    return rows


def mu(n):
    f=factors(n)
    return 0 if any(e>1 for _,e in f) else (-1)**len(f)


def floor_weight(N,d):return (4*N)//d-3*((2*N)//d)+2*(N//d)


def add(out,p,value):
    out[p]=out.get(p,Q(0))+value
    if out[p]==0:out.pop(p)


def hjet(N,S):
    R=1
    for p in S:R*=p
    divisors=[]
    for k in range(len(S)+1):
        for U in combinations(S,k):
            e=1
            for p in U:e*=p
            divisors.append((e,(-1)**k))
    out={};zeroth=0
    for d in range(1,4*N+1):
        if gcd(d,R)>1:continue
        coeff=mu(d)*sum(sign*floor_weight(N,d*e) for e,sign in divisors)
        zeroth+=coeff
        for p,exponent in factors(R*d):add(out,p,-coeff*exponent)
        M.charge(10+len(divisors))
    return out,zeroth


def prime_shell(N,p):
    def count(X):
        value=p;result=0
        while value<=X:result+=1;value*=p;M.charge()
        return result
    return count(4*N)-3*count(2*N)+2*count(N)


def expected_jet(N,S):
    # Independently form the full von-Mangoldt prime-power prefix.
    out={}
    for n in range(2,4*N+1):
        f=factors(n)
        if len(f)==1:
            coeff=int(n<=4*N)-3*int(n<=2*N)+2*int(n<=N)
            add(out,f[0][0],coeff)
    for p in S:add(out,p,-prime_shell(N,p))
    return out


def rational_h(N,S):
    R=1
    for p in S:R*=p
    divisors=[]
    for k in range(len(S)+1):
        for U in combinations(S,k):
            e=1
            for p in U:e*=p
            divisors.append((e,(-1)**k))
    return sum((Q(mu(d),R*d)*sum(sign*floor_weight(N,d*e) for e,sign in divisors)
                for d in range(1,4*N+1) if gcd(d,R)==1),Q(0))


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_prime_insertion_core_056 operations='+str(sum(m.operations for m in (M,PM,PIPE))))


class CoreRulesTests(unittest.TestCase):
    def test_three_tail_regimes_and_critical_log(self):
        for tau,shape in [('1/2',{'N_power':'1/2','constant':'128','log_coefficient':'0','logarithm_base':'e'}),
                ('1',{'N_power':'0','constant':'12','log_coefficient':'4','logarithm_base':'e'}),
                ('257/256',{'N_power':'0','constant':'1028','log_coefficient':'0','logarithm_base':'e'})]:
            r,c=tail(tau)
            self.assertEqual(C.verify_tail_bound(r,c,M)['upper_bound'],shape)
        r,c=tail('1/257',[2,3],alpha='123/257')
        out=C.verify_tail_bound(r,c,M)
        self.assertEqual(Q(out['upper_bound']['constant']),Q(257**3,4))

    def test_actual_primes_and_products_beyond_old_array_cap(self):
        r,c=tail('2',[2,3,5,7,11,13,17,19,23])
        out=C.verify_tail_bound(r,c,M)
        self.assertEqual(out['upper_bound']['constant'],str(8*2**9))
        self.assertGreater(c['product'],2_000_000)
        for primes in ([4],[2,2],[3,2],[True],[1]):
            bad=copy.deepcopy(r);bad['primes']=primes
            with self.assertRaises(ValueError):C.verify_tail_bound(bad,c,M)

    def test_tail_domain_normalization_and_signed_source_binding(self):
        r,c=tail('1/2',[2,3])
        for field,value in [('integer_N_minimum',1),('product',2),
                ('normalizer','1/I_alpha'),('integrand','sum_(d prime)d^-t*W(N/d)'),
                ('unpaid_core','none'),('complete_target_bound_proved',True),('RH_proved',True)]:
            bad=copy.deepcopy(c);bad[field]=value
            with self.assertRaises(ValueError):C.verify_tail_bound(r,bad,M)
        bad=copy.deepcopy(c);bad['filter']['coefficients']=[-2,1]
        with self.assertRaises(ValueError):C.verify_tail_bound(r,bad,M)

    def test_tau_one_cannot_use_bounded_or_subcritical_provider(self):
        r,c=tail('1')
        for key,value in [('N_power','1/2'),('constant','4'),('log_coefficient','0'),('logarithm_base',2)]:
            bad=copy.deepcopy(c);bad['upper_bound'][key]=value
            with self.assertRaises(ValueError):C.verify_tail_bound(r,bad,M)
        r,c=tail('1/3')
        bad=copy.deepcopy(c);bad['upper_bound']['N_power']='1/2'
        with self.assertRaises(ValueError):C.verify_tail_bound(r,bad,M)

    def test_rational_types_and_cutoff_resource_guards(self):
        r,c=tail()
        for key,values in [('alpha',('0','1','2/4',0.2,True)),('tau',('0','-1','2/4',0.5,True,'257'))]:
            for value in values:
                bad=copy.deepcopy(r);bad[key]=value
                with self.assertRaises(ValueError):C.verify_tail_bound(bad,c,M)
        with self.assertRaises(OverflowError):C.verify_tail_bound(r,c,C.Meter(cap=0))

    def test_integer_unit_gate_and_full_cofactor_weight(self):
        def W(x):return (4*x).__floor__()-3*(2*x).__floor__()+2*x.__floor__()
        for i in range(1,100):self.assertEqual(W(Q(i)),0)
        self.assertNotEqual(W(Q(3,8)),0)
        self.assertNotEqual(W(Q(2,3)),0)
        # d1 for R3 has the e3 exception even though W(N)=0.
        self.assertNotEqual(W(Q(2))-W(Q(2,3)),0)

    def test_full_formal_first_jet_and_zero_jet_source_identity(self):
        for N in range(1,9):
            for S in ([],[2],[3],[2,3],[2,3,5]):
                actual,zeroth=hjet(N,S)
                self.assertEqual(zeroth,0)
                self.assertEqual(actual,expected_jet(N,S))

    def test_first_jet_bounds_and_exact_prime_two_identity(self):
        for N in range(1,257):
            self.assertEqual(prime_shell(N,2),-1)
            for p in (3,5,7,11,17):self.assertLessEqual(abs(prime_shell(N,p)),2)
        r,c=jet([[],[2]],['1','-1'])
        out=C.verify_first_jet(r,c,M)
        self.assertEqual(out['status'],'UNIFORM_FIRST_JET_BOUND')
        self.assertEqual(out['uniform_absolute_upper'],'1')
        self.assertEqual(out['exception_rows'],[{'prime':2,'coefficient':'1','rational_abs_bound':'1'}])

    def test_generic_rational_signed_jet_mixture(self):
        r,c=jet([[],[2],[3]],['1/257','-2/257','1/257'])
        out=C.verify_first_jet(r,c,M)
        self.assertEqual(out['uniform_absolute_upper'],'8/257')
        self.assertEqual(out['common_coefficient'],'0')
        for N in range(2,9):
            result={}
            for S,coefficient in zip(r['features'],r['coefficients']):
                row,_=hjet(N,S)
                for p,value in row.items():add(result,p,Q(coefficient)*value)
            expected={}
            for row in out['exception_rows']:add(expected,row['prime'],Q(row['coefficient'])*prime_shell(N,row['prime']))
            self.assertEqual(result,expected)

    def test_exact_zero_first_jet_keeps_zero_exception_rows(self):
        r,c=jet()
        out=C.verify_first_jet(r,c,M)
        self.assertEqual(out['status'],'EXACT_FIRST_JET_ZERO')
        self.assertEqual(out['uniform_absolute_upper'],'0')
        self.assertEqual(len(out['exception_rows']),2)
        self.assertTrue(out['first_jet_exact_zero_proved'])
        bad=copy.deepcopy(c);bad['exception_rows'].pop()
        with self.assertRaises(ValueError):C.verify_first_jet(r,bad,M)

    def test_first_jet_zero_does_not_cancel_full_kernel(self):
        r,c=jet()
        out=C.verify_first_jet(r,c,M)
        self.assertFalse(out['full_kernel_cancellation_proved'])
        self.assertFalse(out['low_core_bound_proved'])
        values=[sum((Q(a)*rational_h(N,S) for S,a in zip(r['features'],r['coefficients'])),Q(0)) for N in (2,3,4)]
        self.assertTrue(any(values))
        for flag in ('full_kernel_cancellation_proved','low_core_bound_proved','RH_proved'):
            bad=copy.deepcopy(c);bad[flag]=True
            with self.assertRaises(ValueError):C.verify_first_jet(r,bad,M)

    def test_common_prime_term_nonzero_is_retained_not_priced(self):
        r,c=jet([[],[2]],['1','1'])
        out=C.verify_first_jet(r,c,M)
        self.assertEqual(out['status'],'COMMON_PRIME_TERM_OPEN')
        self.assertEqual(out['common_coefficient'],'2')
        self.assertIsNone(out['uniform_absolute_upper'])
        bad=copy.deepcopy(c);bad['uniform_absolute_upper']='1'
        with self.assertRaises(ValueError):C.verify_first_jet(r,bad,M)
        bad=copy.deepcopy(c);bad['common_coefficient']='0'
        with self.assertRaises(ValueError):C.verify_first_jet(r,bad,M)

    def test_exception_sign_bound_and_full_rows_cannot_change(self):
        r,c=jet([[],[2],[3]],['1/257','-2/257','1/257'])
        for field,value in [('coefficient','-2/257'),('rational_abs_bound','0'),('prime',5)]:
            bad=copy.deepcopy(c);bad['exception_rows'][0][field]=value
            with self.assertRaises(ValueError):C.verify_first_jet(r,bad,M)
        bad=copy.deepcopy(c);bad['common_prime_term']='Psi_P includes only generator primes'
        with self.assertRaises(ValueError):C.verify_first_jet(r,bad,M)

    def test_jet_features_and_coefficient_schema_guards(self):
        r,c=jet()
        for features in ([],[[],[]],[[4]],[[3,2]]):
            bad=copy.deepcopy(r);bad['features']=features
            with self.assertRaises(ValueError):C.verify_first_jet(bad,c,M)
        for values in (['0']*4,[1,-1,-1,1],['2/4','-1','-1','1'],[True,'-1','-1','1'],['1']):
            bad=copy.deepcopy(r);bad['coefficients']=values
            with self.assertRaises(ValueError):C.verify_first_jet(bad,c,M)

    def test_numeric_recovery_strict_boundary_and_log_weight(self):
        for tau,compatible,constant in [('127/257',False,None),('1/2',True,'129'),('1',True,'21'),('2',True,'9')]:
            r,c=recovery(tau,eta='1/257')
            out=C.verify_low_core_recovery(r,c,M)
            self.assertEqual(out['full_constant'],constant)
            self.assertEqual(out['conditional_original_target_implication'],compatible)
            self.assertFalse(out['low_core_bound_proved'])
            self.assertFalse(out['complete_target_bound_proved'])

    def test_auxiliary_recovery_is_not_original_target_recovery(self):
        r,c=recovery('1/2',[2,3])
        out=C.verify_low_core_recovery(r,c,M)
        self.assertEqual(out['tail_square_root_constant'],'512')
        self.assertFalse(out['conditional_original_target_implication'])
        bad=copy.deepcopy(c);bad['conditional_original_target_implication']=True
        with self.assertRaises(ValueError):C.verify_low_core_recovery(r,bad,M)

    def test_numeric_open_core_never_promoted_by_tail_or_first_jet(self):
        r,c=recovery()
        bad=copy.deepcopy(r);bad['low_core']['status']='PAID'
        with self.assertRaises(ValueError):C.verify_low_core_recovery(bad,c,M)
        for flag in ('low_core_bound_proved','complete_target_bound_proved','RH_proved'):
            bad=copy.deepcopy(c);bad[flag]=True
            with self.assertRaises(ValueError):C.verify_low_core_recovery(r,bad,M)
        bad=copy.deepcopy(c);bad['source_split']='t_S=low_core'
        with self.assertRaises(ValueError):C.verify_low_core_recovery(r,bad,M)

    def test_recovery_underprice_and_plain_log_at_small_N_rejected(self):
        r,c=recovery('1',eta='1/2')
        bad=copy.deepcopy(c);bad['full_constant']='13'
        with self.assertRaises(ValueError):C.verify_low_core_recovery(r,bad,M)
        bad=copy.deepcopy(c);bad['log_weight']='log(N)^log_power'
        with self.assertRaises(ValueError):C.verify_low_core_recovery(r,bad,M)
        for key,value in [('constant','-1'),('constant',1),('log_power','-1/2')]:
            bad=copy.deepcopy(r);bad['low_core'][key]=value
            with self.assertRaises(ValueError):C.verify_low_core_recovery(bad,c,M)

    def test_generic_recovery_constant_quantifier(self):
        for tau,offset in [('1/2','128'),('1','20'),('2','8')]:
            r,c=recovery_schema(tau,eta='1/257')
            out=C.verify_low_core_recovery_schema(r,c,M)
            self.assertEqual(out['full_constant'],{'C_low_coefficient':'1','offset':offset})
            self.assertEqual(out['low_core_constant_quantifier'],'FOR EVERY finite C_low>=0')
            self.assertTrue(out['conditional_original_target_implication'])
            self.assertFalse(out['complete_target_bound_proved'])

    def test_generic_recovery_missing_tail_or_numeric_fit_rejected(self):
        r,c=recovery_schema()
        for field,value in [('full_constant',{'C_low_coefficient':'1','offset':'0'}),
                ('low_core_constant_quantifier','C_low is fitted from finite probes'),
                ('open_premise','only the training N'),('complete_target_bound_proved',True)]:
            bad=copy.deepcopy(c);bad[field]=value
            with self.assertRaises(ValueError):C.verify_low_core_recovery_schema(r,bad,M)

    def test_generic_recovery_provider_insufficient_not_arithmetic_refutation(self):
        r,c=recovery_schema('1/3')
        out=C.verify_low_core_recovery_schema(r,c,M)
        self.assertEqual(out['status'],'TAIL_PROVIDER_INSUFFICIENT')
        self.assertIsNone(out['full_constant'])
        self.assertFalse(out['conditional_original_target_implication'])
        self.assertFalse(out['RH_refuted'])
        bad=copy.deepcopy(c);bad['tail_square_root_compatible']=True
        with self.assertRaises(ValueError):C.verify_low_core_recovery_schema(r,bad,M)

    def test_generic_recovery_source_and_eta_binding(self):
        r,c=recovery_schema('1',[2],eta='1/257')
        self.assertFalse(C.verify_low_core_recovery_schema(r,c,M)['conditional_original_target_implication'])
        for key,value in [('log_power','-1'),('log_power',True)]:
            bad=copy.deepcopy(r);bad[key]=value
            with self.assertRaises(ValueError):C.verify_low_core_recovery_schema(bad,c,M)
        bad=copy.deepcopy(c);bad['request']['tail_request']['primes']=[]
        with self.assertRaises(ValueError):C.verify_low_core_recovery_schema(r,bad,M)

    def test_charge_only_meter_and_strict_boolean_flags(self):
        for request,certificate,function in [(*tail(),C.verify_tail_bound),(*jet(),C.verify_first_jet),
                (*recovery(),C.verify_low_core_recovery),(*recovery_schema(),C.verify_low_core_recovery_schema)]:
            self.assertTrue(function(request,certificate,PIPE)['verified'])
            bad=copy.deepcopy(certificate);bad['RH_proved']=0
            with self.assertRaises(ValueError):function(request,bad,M)
        self.assertFalse(hasattr(PIPE,'number'))

    def test_microscopic_full_E_R_source_and_arbitrary_denominators(self):
        r,c=microscopic()
        out=C.verify_microscopic_bound(r,c,M)
        self.assertEqual(out['upper_bound'],{'constant':'40','N_power':'1/10'})
        self.assertTrue(out['near_zero_bound_proved'])
        self.assertFalse(out['complete_target_bound_proved'])
        self.assertTrue(out['recovery_requires_middle_control'])
        r,c=microscopic(alpha='123/257',primes=[2],gamma='257/193')
        out=C.verify_microscopic_bound(r,c,PIPE)
        self.assertEqual(Q(out['upper_bound']['N_power']),1-Q(134,193))
        self.assertEqual(Q(out['upper_bound']['constant']),Q(24*257,134))

    def test_microscopic_signed_mass_and_unit_filter(self):
        for N in range(2,65):
            weights=[2*int(n<=N)-3*int(n<=2*N)+int(n<=4*N) for n in range(2,4*N+1)]
            self.assertEqual(sum(abs(w) for w in weights),4*N)
            self.assertEqual(2-3+1,0)
        r,c=microscopic()
        for key,value in [('filter_absolute_mass','2*N'),('operator','D_S K(n)'),
                ('integrand','t^k only'),('unpaid_middle','empty'),
                ('cutoff','epsilon_N=N^gamma'),('complete_target_bound_proved',True)]:
            bad=copy.deepcopy(c);bad[key]=value
            with self.assertRaises(ValueError):C.verify_microscopic_bound(r,bad,M)
        bad=copy.deepcopy(c);bad['filter']['coefficients']=[-2,1]
        with self.assertRaises(ValueError):C.verify_microscopic_bound(r,bad,M)

    def test_microscopic_constant_power_and_nonempty_gate(self):
        r,c=microscopic()
        for key,value in [('constant','4'),('N_power','-1/2')]:
            bad=copy.deepcopy(c);bad['upper_bound'][key]=value
            with self.assertRaises(ValueError):C.verify_microscopic_bound(r,bad,M)
        bad=copy.deepcopy(r);bad['primes']=[]
        with self.assertRaises(ValueError):C.verify_microscopic_bound(bad,c,M)
        for gamma in ('0','-1','2/4',0.5,True,'257'):
            bad=copy.deepcopy(r);bad['gamma']=gamma
            with self.assertRaises(ValueError):C.verify_microscopic_bound(bad,c,M)
        bad=copy.deepcopy(c);bad['RH_proved']=True
        with self.assertRaises(ValueError):C.verify_microscopic_bound(r,bad,M)


if __name__=='__main__':unittest.main()
