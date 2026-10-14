"""Independent059 admission tests on tiny synthetic finite sources only."""
import copy
import unittest
from fractions import Fraction as Q
from math import factorial,gcd,prod
from unittest.mock import patch
from flint import arb,ctx
import check_mobius_transport_059 as C
from prime_bank_candidates import Meter as PipelineMeter

METERS=[]

def meter():
    m=C.Meter(cap=1_000_000_000,seconds=180);METERS.append(m);return m

def request(N=5,alpha='1/2',gamma='1',tau='1/2',primes=(2,3),p=2,q=3):
    return {'N':N,'alpha':alpha,'gamma':gamma,'tau':tau,'primes':list(primes),'p':p,'q':q}

def mu_direct(n):
    # Distinct divisor-factorization rule, including explicit square rejection.
    sign=1
    for p in range(2,n+1):
        if n%p:continue
        if any(p%d==0 for d in range(2,p)):continue
        if n%(p*p)==0:return 0
        sign=-sign
    return sign

def tokens_for(r,m):
    data=C._request(r,m);context=C.prepare_context(m)
    tokens,_=C._tokens(data,C._state(context),m)
    return C._public_tokens(tokens)

def baseline(r,m):
    return {'pairs':[],'unmatched':[t['d'] for t in tokens_for(r,m)]}

def mixed(r,m):
    ts=tokens_for(r,m);plus=[t['d'] for t in ts if t['sign']==1];minus=[t['d'] for t in ts if t['sign']==-1]
    count=min(len(plus),len(minus))
    return {'pairs':[[plus[i],minus[i]] for i in range(count)],'unmatched':plus[count:]+minus[count:]}

def profile_plan(r,m):
    ts=tokens_for(r,m);pairs=[];unmatched=[]
    for profile in ('P','Q','D','S'):
        waiting=[]
        for t in ts:
            if t['profile']!=profile:continue
            if waiting and waiting[-1]['sign']!=t['sign']:
                pairs.append([waiting.pop()['d'],t['d']])
            else:waiting.append(t)
        unmatched.extend(t['d'] for t in waiting)
    return {'pairs':pairs,'unmatched':unmatched}

def dominance(policy):
    return {'schema':'mobius-profile-dominance-v1','policy':policy,
        'reference':{'steps':[{'kind':'scan','group':'profile','order':'asc','method':'stack'}]},
        'bound':'B_reference<=B_policy','uniform_growth_bound_proved':False,'RH_proved':False}

def Taylor_phi(a,r,m,degree=100):
    alpha=Q(r['alpha']);gamma=Q(r['gamma']);tau=Q(r['tau'])
    with ctx.workprec(384):
        epsilon=(-C._aq(gamma)*arb(r['N']).log()).exp()
        upper=C._aq(tau);rows={1:1}
        for p in r['primes']:
            rows.update({d*p:-v for d,v in list(rows.items())})
        total=arb(0);error=arb(0)
        for d,coefficient in rows.items():
            lam=arb(a*d).log();power=arb(1)
            # k0 cancels EXACTLY acrossG_M, so do not numerically integrate it.
            for k in range(1,degree+1):
                power*=lam
                beta=C._aq(Q(k)-alpha)
                integral=(upper**beta-epsilon**beta)/beta
                total+=coefficient*((-1)**k)*power*integral/factorial(k)
            beta=C._aq(Q(degree+1)-alpha)
            error+=abs(coefficient)*power*lam*(upper**beta-epsilon**beta)/(beta*factorial(degree+1))
        norm=C._aq(1-alpha).rgamma();total*=norm;error*=norm
        lo=C._dyadic((total-error.abs_upper()).lower(),m)
        hi=C._dyadic((total+error.abs_upper()).upper(),m,True)
    m.charge(10000*len(rows));return lo,hi


class TransportCheckerTests(unittest.TestCase):
    def test_ordinary_mu_tokens_all_weights_and_profiles(self):
        m=meter();seen=set()
        for N in range(2,32):
            r=request(N);tokens=tokens_for(r,m)
            actual={t['d']:t for t in tokens}
            for d in range(1,4*N//r['p']+1):
                a=C._W(N,r['p']*d);b=C._W(N,r['q']*d);mu=mu_direct(d)
                active=bool(gcd(d,6)==1 and mu and (a or b))
                self.assertEqual(d in actual,active)
                if not active:continue
                t=actual[d];seen.add(t['profile'])
                profile='P' if b==0 else 'Q' if a==0 else 'D' if a==b else 'S'
                sigma=a if a else -b
                self.assertEqual(t,{'d':d,'profile':profile,'sign':mu*sigma,'kernel_sign':sigma,'mu':mu})
                m.charge(200)
        self.assertEqual(seen,{'P','Q','D','S'})

    def test_unit_and_q_range_exit_remain(self):
        m=meter();r=request(5);ts=tokens_for(r,m)
        self.assertEqual(ts[0],{'d':1,'profile':'D','sign':-1,'kernel_sign':-1,'mu':1})
        self.assertEqual(ts[-1]['profile'],'P');self.assertEqual(ts[-1]['d'],7)
        self.assertEqual(C._W(5,3*7),0)
        self.assertTrue(C.verify_plan(r,baseline(r,m),m)['all_range_exits_retained'])

    def test_plan_cross_profile_pairs_and_reversal(self):
        m=meter();r=request(5);plan={'pairs':[[5,1]],'unmatched':[7]}
        out=C.verify_plan(r,plan,m)
        self.assertTrue(out['finite_triangle_bound_proved'])
        self.assertTrue(out['cross_profile_pairs_allowed'])
        self.assertFalse(out['uniform_growth_bound_proved']);self.assertFalse(out['RH_proved'])
        reversed_plan={'pairs':[[1,5]],'unmatched':[7]}
        self.assertTrue(C.verify_plan(r,reversed_plan,m)['verified'])

    def test_missing_duplicate_wrong_sign_and_foreign_tokens(self):
        m=meter();r=request(5)
        for plan in ({'pairs':[[5,1]],'unmatched':[]},
                {'pairs':[[5,1]],'unmatched':[1]},
                {'pairs':[[1,7]],'unmatched':[5]},
                {'pairs':[[5,1]],'unmatched':[25]},
                {'pairs':[[5,True]],'unmatched':[7]},
                {'pairs':[[5,1,7]],'unmatched':[]}):
            with self.assertRaises(ValueError):C.verify_plan(r,plan,m)
        bad=baseline(r,m);bad['verified']=True
        with self.assertRaises(ValueError):C.verify_plan(r,bad,m)

    def test_prime_parameters_types_and_canonical_aliases(self):
        m=meter();r=request();plan=baseline(r,m)
        for key,value in [('N',True),('N',1),('N',32769),('alpha','1'),('alpha','2/4'),
                ('gamma','0'),('tau','1'),('tau','0'),('primes',[2,4]),('primes',[3,2]),
                ('primes',[2,2,3]),('primes',[True,3]),('p',3),('p',True),('q',5)]:
            bad=copy.deepcopy(r);bad[key]=value
            with self.assertRaises(ValueError):C.verify_plan(bad,plan,m)
        with self.assertRaises(ValueError):C.verify_plan(dict(r,uniform=True),plan,m)

    def test_exact_powered_zero_band_general_tau(self):
        m=meter();context=C.prepare_context(m)
        for r in (request(2),request(4,gamma='1/2'),
                request(3,gamma='1/257'),request(3,gamma='1',tau='1/3')):
            with patch.object(C,'_phi',side_effect=AssertionError('gamma in zero band')):
                out=C.evaluate(r,baseline(r,m),meter=m,context=context)
            self.assertTrue(out['exact_zero_band'])
            self.assertEqual(out['bound'],{'lower':'0','upper':'0'})
            self.assertEqual(out['signed_sum'],{'lower':'0','upper':'0'})
        r=request(4,tau='1/3');out=C.evaluate(r,baseline(r,m),meter=m,context=context)
        self.assertFalse(out['exact_zero_band'])

    def test_phi_independent_integrated_taylor_calibration(self):
        m=meter();r=request(5,alpha='1/3');data=C._request(r,m);context=C.prepare_context(m);state=C._state(context)
        with ctx.workprec(256):
            epsilon,tau,empty=C._band(data,state,m,256)
            for a in (2,3,10,15):
                interval,hit=C._phi(a,data,epsilon,tau,256,state,m)
                lo,hi=Taylor_phi(a,r,m)
                # Both independent methods are rigorous; finerGamma interval
                # must overlap the explicitTaylor+remainder enclosure.
                self.assertLessEqual(Q(interval['lower']),hi)
                self.assertLessEqual(lo,Q(interval['upper']))
                self.assertGreaterEqual(Q(interval['lower']),0)

    def test_half_alpha_erfc_integral_and_monotone_difference(self):
        m=meter();r=request(5);context=C.prepare_context(m);data=C._request(r,m);state=C._state(context)
        with ctx.workprec(256):
            a,b=arb(1)/5,arb(1)/2
            values=[]
            for base in (2,3):
                total=arb(0)
                for e,mu in ((1,1),(2,-1),(3,-1),(6,1)):
                    lam=arb(base*e).log()
                    def endpoint(t):return 2*(-lam*t).exp()/t.sqrt()-2*(arb.pi()*lam).sqrt()*(lam*t).sqrt().erfc()
                    total+=mu*(endpoint(a)-endpoint(b))
                total/=arb.pi().sqrt();values.append(total)
                interval,_=C._phi(base,data,a,b,256,state,m)
                self.assertTrue(C._aq(Q(interval['lower']))<=total.lower())
                self.assertTrue(total.upper()<=C._aq(Q(interval['upper'])))
                m.charge(10000)
            self.assertTrue(values[0]>values[1])

    def test_evaluate_many_one_table_signed_bounds_and_triangle(self):
        m=meter();r=request(5);plans=[baseline(r,m),mixed(r,m)]
        context=C.prepare_context(m)
        out=C.evaluate_many(r,plans,meter=m,context=context)
        self.assertGreater(out['counts']['new_Phi_kernels'],0)
        self.assertEqual(out['rows'][0]['bound'],out['absolute_sum'])
        signed_lo,signed_hi=map(Q,(out['signed_sum']['lower'],out['signed_sum']['upper']))
        for row in out['rows']:
            self.assertTrue(row['verification']['complete_coverage'])
            self.assertGreaterEqual(Q(row['bound']['upper']),max(abs(signed_lo),abs(signed_hi)))
            self.assertFalse(row['verification']['uniform_growth_bound_proved'])
        self.assertLessEqual(Q(out['rows'][1]['bound']['upper']),Q(out['absolute_sum']['upper']))
        again=C.evaluate_many(r,plans,meter=m,context=context)
        self.assertEqual(again['rows'],out['rows']);self.assertEqual(again['counts']['new_Phi_kernels'],0)
        self.assertTrue(again['counts']['token_cache_hit'])

    def test_direct_joined_W_formula_no_token_sign_swap(self):
        m=meter();r=request(5);out=C.evaluate(r,mixed(r,m),meter=m)
        data=C._request(r,m);context=C.prepare_context(m);state=C._state(context)
        with ctx.workprec(256):
            a,b,empty=C._band(data,state,m,256);lo=Q(0);hi=Q(0)
            for d in (1,5,7):
                mu=mu_direct(d)
                for prime,orientation in ((2,1),(3,-1)):
                    weight=mu*orientation*C._W(5,prime*d)
                    if not weight:continue
                    phi,_=C._phi(prime*d,data,a,b,256,state,m)
                    v0,v1=Q(phi['lower']),Q(phi['upper'])
                    lo+=weight*(v0 if weight>0 else v1)
                    hi+=weight*(v1 if weight>0 else v0)
            self.assertLessEqual(lo,Q(out['signed_sum']['upper']))
            self.assertLessEqual(Q(out['signed_sum']['lower']),hi)

    def test_generic_fractional_parameters_and_functional_cache(self):
        m=meter();context=C.prepare_context(m)
        for alpha in ('1/257','123/257','256/257'):
            r=request(3,alpha=alpha,gamma='257/193',tau='123/257')
            out=C.evaluate(r,baseline(r,m),meter=m,context=context)
            self.assertTrue(out['verified']);self.assertFalse(out['RH_proved'])
        r=request(3,alpha='123/257',gamma='257/193',tau='123/257')
        out=C.evaluate(r,baseline(r,m),meter=m,context=context)
        self.assertEqual(out['counts']['new_Phi_kernels'],0)
        changed=C.evaluate(dict(r,alpha='1/2'),baseline(r,m),meter=m,context=context)
        self.assertGreater(changed['counts']['new_Phi_kernels'],0)

    def test_exact_rational_pair_interval_and_absolute_values(self):
        self.assertEqual(C._absolute_difference((Q(2),Q(3)),(Q(4),Q(5))),(Q(1),Q(3)))
        self.assertEqual(C._absolute_difference((Q(2),Q(5)),(Q(4),Q(8))),(Q(0),Q(6)))
        self.assertEqual(C._absolute_difference((Q(9),Q(10)),(Q(1),Q(2))),(Q(7),Q(9)))
        m=meter();plan={'pairs':[[1,3]],'unmatched':[5]}
        result=C._pair_result(plan,{1:(Q(1),Q(1)),3:(Q(4),Q(4)),5:(Q(2),Q(2))},m)
        self.assertEqual(result,{'lower':'5','upper':'5'})

    def test_assess_claim_pass_refuted_unresolved_and_general_beta(self):
        m=meter();r=request()
        out=C.assess_bound(r,{'lower':'1','upper':'2'},{'C':'1','beta':'1'},m)
        self.assertEqual(out['status'],'PASS');self.assertFalse(out['uniform_growth_bound_proved'])
        out=C.assess_bound(r,{'lower':'6','upper':'7'},{'C':'1','beta':'1'},m)
        self.assertEqual(out['status'],'REFUTED');self.assertFalse(out['RH_refuted'])
        out=C.assess_bound(r,{'lower':'4','upper':'6'},{'C':'1','beta':'1'},m)
        self.assertEqual(out['status'],'UNRESOLVED')
        self.assertEqual(C.assess_bound(r,{'lower':'0','upper':'0'},{'C':'0','beta':'123/257'},m)['status'],'PASS')
        self.assertEqual(C.assess_bound(r,{'lower':'1','upper':'1'},{'C':'1','beta':'0'},m)['status'],'PASS')
        out=C.assess_bound(r,{'lower':'0','upper':'1'},{'C':'2','beta':'1/257'},m)
        self.assertEqual(out['status'],'PASS')

    def test_claim_and_context_forgery_gates(self):
        m=meter();r=request()
        for claim in ({'C':'-1','beta':'1'},{'C':'1','beta':'3'},{'C':'1','beta':'-1'},
                {'C':True,'beta':'1'},{'C':'2/2','beta':'1'},{'C':'1','beta':'1','uniform':True}):
            with self.assertRaises(ValueError):C.assess_bound(r,{'lower':'0','upper':'1'},claim,m)
        for interval in ({'lower':'2','upper':'1'},{'lower':'-1','upper':'1'},
                {'lower':'0','upper':'1','verified':True}):
            with self.assertRaises(ValueError):C.assess_bound(r,interval,{'C':'1','beta':'1'},m)
        with self.assertRaises(ValueError):C.evaluate(r,baseline(r,m),meter=m,context={'phi':'forged'})

    def test_work_memory_power_and_precision_guards(self):
        m=meter();r=request();plan=baseline(r,m)
        with self.assertRaises(OverflowError):C.verify_plan(r,plan,C.Meter(cap=1))
        with self.assertRaises(ValueError):C.evaluate(r,plan,precision=True,meter=m)
        with self.assertRaises(ValueError):C.evaluate(r,plan,precision=1024,meter=m)
        with self.assertRaises(ValueError):C.evaluate_many(r,[],meter=m)
        with patch.object(C,'MAX_CACHE_BYTES',0):
            with self.assertRaises(MemoryError):C.evaluate(r,plan,meter=m,context=C.prepare_context(m))
        with patch.object(C,'MAX_PLAN_ENTRIES',1):
            with self.assertRaises(MemoryError):C.evaluate(r,plan,meter=m)
        with self.assertRaises(OverflowError):C.evaluate(request(3,gamma='200001'),baseline(request(3,gamma='200001'),m),meter=m)

    def test_charge_only_meter_and_precision_restore(self):
        m=PipelineMeter(cap=100000000,seconds=180);METERS.append(m);r=request();old=ctx.prec
        result=C.evaluate(r,baseline(r,m),meter=m)
        self.assertTrue(result['verified']);self.assertEqual(ctx.prec,old)
        with patch.object(C,'_phi',side_effect=ArithmeticError('syntheticGammafailure')):
            with self.assertRaises(ArithmeticError):C.evaluate(request(7),baseline(request(7),m),meter=m)
        self.assertEqual(ctx.prec,old)

    def test_profile_dominance_exact_policy_scope_and_mutations(self):
        m=meter()
        policies=[{'steps':[]},{'steps':[{'kind':'scan','group':'profile','order':'asc','method':'stack'}]},
            {'steps':[{'kind':'scan','group':'sector','order':'desc','method':'fifo'}]},
            {'steps':[{'kind':'scan','group':'profile_residue','modulus':257,'order':'asc','method':'fifo'}]},
            {'steps':[{'kind':'scan','group':'profile_block','theta':'123/257','order':'desc','method':'stack'},
                {'kind':'prime_ratio','group':'profile','order':'desc'}]},
            {'steps':[{'kind':'scan','group':'profile_quotient','order':'asc','method':'stack'}]}]
        for policy in policies:
            out=C.verify_profile_dominance(policy,dominance(policy),m)
            self.assertTrue(out['finite_profile_transport_dominance_proved'])
            self.assertFalse(out['uniform_growth_bound_proved'])
            self.assertFalse(out['cross_profile_policy_dominated'])
        for policy in ({'steps':[{'kind':'scan','group':'all','order':'asc','method':'stack'}]},
                {'steps':[{'kind':'prime_ratio','group':'all','order':'asc'}]},
                {'steps':[{'kind':'scan','group':'profile_residue','modulus':True,'order':'asc','method':'fifo'}]},
                {'steps':[{'kind':'scan','group':'profile_block','theta':'2/4','order':'asc','method':'stack'}]},
                {'steps':[{'kind':'scan','group':'profile','order':'asc','method':'greedy'}]},
                {'steps':policies[1]['steps']*3}):
            with self.assertRaises(ValueError):C.verify_profile_dominance(policy,dominance(policy),m)
        policy=policies[1];bad=dominance(policy);bad['uniform_growth_bound_proved']=True
        with self.assertRaises(ValueError):C.verify_profile_dominance(policy,bad,m)
        bad=dominance(policy);bad['reference']['steps'][0]['order']='desc'
        with self.assertRaises(ValueError):C.verify_profile_dominance(policy,bad,m)

    def test_monotone_profile_optimum_flux_and_zero_dummy(self):
        m=meter()
        # A reverse traversal can leave the wrongmass for the zero dummy.
        tokens=((1,'P',1,1,1),(2,'P',-1,1,-1),(3,'P',1,1,1))
        magnitudes={1:(Q(4),Q(4)),2:(Q(3),Q(3)),3:(Q(2),Q(2))}
        self.assertEqual(C._profile_optimum(tokens,magnitudes,m),{'lower':'3','upper':'3'})
        self.assertEqual(C._pair_result({'pairs':[[2,3]],'unmatched':[1]},magnitudes,m),{'lower':'5','upper':'5'})
        for N in (5,7,13):
            r=request(N);reference=profile_plan(r,m)
            out=C.evaluate(r,reference,meter=m)
            self.assertLessEqual(Q(out['profile_optimum']['lower']),Q(out['bound']['upper']))
            self.assertLessEqual(Q(out['bound']['lower']),Q(out['profile_optimum']['upper']))
            self.assertIn('notcrossprofileplans',out['profile_optimum_scope'])


if __name__=='__main__':
    try:unittest.main()
    finally:print('SYNTHETIC_WORK module=check_mobius_transport_059 operations='+str(sum(m.operations for m in METERS)))
