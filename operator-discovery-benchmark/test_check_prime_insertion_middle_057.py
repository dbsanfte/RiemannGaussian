"""Small independent source, integration and conditional transport tests.

No saved source arrays, scientific candidate scores or previous suites.
"""
import copy
import unittest
from fractions import Fraction as Q
from math import gcd,prod
from unittest.mock import patch
from flint import arb,ctx
import check_prime_insertion_middle_057 as C
import prime_insertion_middle_source_057 as S
from prime_bank_candidates import Meter as PipelineMeter

METERS=[]

def meter():
    m=C.Meter(cap=1_000_000_000,seconds=180);METERS.append(m);return m

def request(N=3,primes=(2,),alpha='1/2',gamma='1',lo='0',hi='1'):
    return dict(alpha=alpha,primes=list(primes),N=N,gamma=gamma,
        lower_fraction=lo,upper_fraction=hi)

def fixture(r,m):
    fixture_meter=S.Meter(cap=1_000_000_000,seconds=180);METERS.append(fixture_meter)
    value=S.evaluate(r,precision=192,meter=fixture_meter)
    return {k:value[k] for k in ('lower','upper')}

def mu(n):
    rest=n;result=1;p=2
    while p*p<=rest:
        if rest%p==0:
            rest//=p;result=-result
            if rest%p==0:return 0
        p+=1
    return -result if rest>1 else result

def cofactor_rows(N,primes):
    """Independent divisor-conductor compiler, unlike checker radical loop."""
    R=prod(primes);out={}
    divisors=[d for d in range(1,R+1) if R%d==0]
    for d in range(1,4*N+1):
        if gcd(d,R)!=1:continue
        w=mu(d)*(4*N//d-3*(2*N//d)+2*(N//d))
        for e in divisors:out[d*e]=out.get(d*e,0)+w*mu(e)
    return tuple(sorted((n,c) for n,c in out.items() if c))

def recovery(delta='1/3',Cvalue='2',weights=('0','0','1')):
    features=[dict(primes=[2],gamma='5/8',lower_fraction='0',upper_fraction='1'),
        dict(primes=[2,3],gamma='5/18',lower_fraction='0',upper_fraction='1/2')]
    r=dict(alpha='1/5',features=features,coefficients=[1,-2],
        **{'lambda':'3/7'},weights=list(weights),delta=delta,C=Cvalue)
    env=[Q(30),Q(40)]
    base=5*(env[0]**2+Q(3,7)*(env[0]+2*env[1])**2)
    c={'schema':'prime-insertion-middle-parent-recovery-v1','request':r,
        'matrix_terms':[{'i':0,'j':0,'coefficient':'10/7'},
            {'i':0,'j':1,'coefficient':'-12/7'},
            {'i':1,'j':1,'coefficient':'12/7'}],
        'source_envelopes':['30','40'],'base_upper':str(base),
        'recurrence':{'minimum':3,'children':[0,1],'offsets':[-1,0,1],
            'formula':'F(2N+r)<=sum_s w_s*F(N+s)+C/N^delta','status':'OPEN'},
        'recovery':{'kind':'bounded' if Q(delta)>0 else 'logarithmic',
            'constant':str(base+2*Q(Cvalue)/Q(delta) if Q(delta)>0 else base),
            'log_coefficient':'0' if Q(delta)>0 else Cvalue,
            'logarithm_base':2,'argument_shift':2,'base_maximum':5},
        'uniform_recurrence_proved':False,'uniform_middle_bound_proved':False,'RH_proved':False}
    return r,c


class MiddleCheckerTests(unittest.TestCase):
    def test_complete_radicals_match_cofactor_identity_and_valuations(self):
        m=meter();context=C.prepare_context(m);state=C._state(context)
        for N in (2,3,5,7):
            for primes in ((),(2,),(3,),(2,3),(3,5)):
                (rows,generated),hit=C._source(primes,N,state,m)
                self.assertEqual(rows,cofactor_rows(N,primes))
                self.assertEqual(sum(c for _,c in rows),0)
                self.assertFalse(hit);self.assertGreater(generated,0)
                m.charge(100*4*N*max(1,prod(primes)))

    def test_independent_taylor_admits_small_producer_integrals(self):
        m=meter();context=C.prepare_context(m)
        for r in (request(),request(5,(3,)),request(7,(2,3)),request(3,())):
            result=C.verify_middle_interval(r,fixture(r,m),m,context)
            self.assertTrue(result['verified']);self.assertFalse(result['all_scale'])
            self.assertTrue(result['source_chain_replayed_here'])
            self.assertFalse(result['producer_imported'])
            self.assertGreater(Q(result['rebuild']['integrated_remainder_upper']),0)

    def test_half_alpha_elementary_erfc_calibration(self):
        m=meter();context=C.prepare_context(m);r=request(3,(2,3))
        lo,hi,info=C._finite(r,m,context)
        with ctx.workprec(256):
            a,b=arb(1)/3,arb(1)/2;total=arb(0)
            for n,c in cofactor_rows(3,(2,3)):
                lam=arb(n).log()
                def F(t):return 2*(-lam*t).exp()/t.sqrt()-2*(arb.pi()*lam).sqrt()*(lam*t).sqrt().erfc()
                total+=c*(F(a)-F(b))
            total/=arb.pi().sqrt()
            self.assertTrue(C._aq(lo)<=total.lower())
            self.assertTrue(total.upper()<=C._aq(hi))
            m.charge(200*len(cofactor_rows(3,(2,3))))

    def test_arbitrary_fractional_parameters_normalizer_and_signed_source(self):
        m=meter();context=C.prepare_context(m)
        for alpha in ('1/257','123/257','256/257'):
            r=request(3,(3,5),alpha=alpha,gamma='257/193',lo='1/3',hi='2/3')
            result=C.verify_middle_interval(r,fixture(r,m),m,context)
            self.assertTrue(result['verified'])
            self.assertEqual(result['rebuild']['prime_product'],15)
        bad=fixture(r,m)
        # Multiplying a positive/nonzero interval by a wrong Gamma normalizer
        # cannot be admitted merely because its source metadata would agree.
        bad={k:str(2*Q(v)) for k,v in bad.items()}
        with self.assertRaises(ValueError):C.verify_middle_interval(r,bad,m,context)

    def test_exact_half_and_equal_bands_skip_source(self):
        m=meter();context=C.prepare_context(m)
        with patch.object(C,'_source',side_effect=AssertionError('source in zero band')):
            for r in (request(2),request(4,gamma='1/2'),request(3,gamma='1/257'),
                    request(3,lo='2/7',hi='2/7')):
                out=C.verify_middle_interval(r,{'lower':'0','upper':'0'},m,context)
                self.assertEqual(out['status'],'EXACT_ZERO_BAND')
                self.assertFalse(out['source_chain_replayed_here'])
        self.assertFalse(C._epsilon(5,Q(1,2),C._state(context),m))

    def test_band_partition_and_same_source_cache(self):
        m=meter();context=C.prepare_context(m)
        whole=request(5,(2,3),gamma='3/2')
        a=C.verify_middle_interval(whole,fixture(whole,m),m,context)
        pieces=[]
        for low,high in (('0','1/3'),('1/3','2/3'),('2/3','1')):
            r=request(5,(2,3),gamma='3/2',lo=low,hi=high)
            out=C.verify_middle_interval(r,fixture(r,m),m,context);pieces.append(out)
            self.assertTrue(out['rebuild']['source_cache_hit'])
            self.assertTrue(out['rebuild']['moments_cache_hit'])
        self.assertLessEqual(sum(Q(v['lower']) for v in pieces),Q(a['upper']))
        self.assertGreaterEqual(sum(Q(v['upper']) for v in pieces),Q(a['lower']))
        r=request(5,(2,3),alpha='1/3',gamma='2')
        out=C.verify_middle_interval(r,fixture(r,m),m,context)
        self.assertTrue(out['rebuild']['moments_cache_hit'])

    def test_functional_context_and_narrow_or_forged_interval(self):
        m=meter();context=C.prepare_context(m);r=request()
        out=C.verify_middle_interval(r,fixture(r,m),m,context)
        center=(Q(out['lower'])+Q(out['upper']))/2
        with self.assertRaises(ValueError):C.verify_middle_interval(r,{'lower':str(center),'upper':str(center)},m,context)
        with self.assertRaises(ValueError):C.verify_middle_interval(r,fixture(r,m),m,{'sources':'forged'})
        with self.assertRaises(ValueError):C.verify_middle_interval(r,dict(fixture(r,m),verified=True),m,context)
        with self.assertRaises(ValueError):C.verify_middle_interval(r,{'lower':'1','upper':'0'},m,context)

    def test_primes_parameters_canonical_types_and_capacity(self):
        m=meter();context=C.prepare_context(m)
        for key,value in [('N',True),('N',32769),('alpha','1'),('alpha','2/4'),
                ('alpha',0.5),('gamma','0'),('gamma','-1'),('primes',[4]),
                ('primes',[3,2]),('primes',[2,2]),('lower_fraction','2'),
                ('upper_fraction','-1')]:
            r=request();r[key]=value
            with self.assertRaises(ValueError):C.verify_middle_interval(r,{'lower':'-1','upper':'1'},m,context)
        with self.assertRaises(OverflowError):C.verify_middle_interval(request(gamma='200001'),{'lower':'-1','upper':'1'},m,context)
        with patch.object(C,'MAX_SOURCE_TERMS',1):
            with self.assertRaises(MemoryError):C._finite(request(11,(2,3)),m,C.prepare_context(m))
        with patch.object(C,'MAX_CACHE_BYTES',0):
            with self.assertRaises(MemoryError):C._finite(request(13),m,C.prepare_context(m))

    def test_charge_only_meter_and_precision_restoration(self):
        m=PipelineMeter(cap=100_000_000,seconds=180);METERS.append(m)
        r=request();old=ctx.prec
        result=C.verify_middle_interval(r,fixture(r,m),m,C.prepare_context(m))
        self.assertTrue(result['verified']);self.assertEqual(ctx.prec,old)
        with patch.object(C,'_integral_power',side_effect=ArithmeticError('synthetic')):
            with self.assertRaises(ArithmeticError):C._finite(request(3,(5,)),m,C.prepare_context(m))
        self.assertEqual(ctx.prec,old)
        with self.assertRaises(OverflowError):C.verify_middle_interval(r,{'lower':'-1','upper':'1'},C.Meter(cap=1))

    def test_dyadic_signed_rounding_and_taylor_remainder(self):
        m=meter()
        with ctx.workprec(256):
            for value in (Q(0),Q(1,3),Q(-1,3),Q(1,2**200),Q(-1,2**200)):
                a=C._aq(value)
                self.assertLessEqual(C._dyadic(a.lower(),m),value)
                self.assertGreaterEqual(C._dyadic(a.upper(),m,True),value)
            a,b=arb(1)/4,arb(1)/2;alpha=Q(1,3);lam=arb(7).log();degree=12
            # e^-lambda*t minus1 has a known signed Taylor expansion.
            total=arb(0)
            for k in range(1,degree+1):
                total+=(-lam)**k*C._integral_power(a,b,C._aq(k-alpha),m,256)/__import__('math').factorial(k)
            rem=lam**(degree+1)*C._integral_power(a,b,C._aq(degree+1-alpha),m,256)/__import__('math').factorial(degree+1)
            exact=lam**C._aq(alpha)*((lam*a).gamma_upper(-C._aq(alpha))-(lam*b).gamma_upper(-C._aq(alpha)))
            exact-=(a**(-C._aq(alpha))-b**(-C._aq(alpha)))/C._aq(alpha)
            self.assertTrue((exact-total).abs_upper()<=rem.upper())
            m.charge(50000)

    def test_recovery_exact_signed_crosses_and_source_base(self):
        m=meter();r,c=recovery()
        out=C.verify_parent_recovery(r,c,m)
        self.assertTrue(out['target_domination_proved']);self.assertEqual(out['recurrence_status'],'OPEN')
        self.assertEqual(out['recovery']['argument_shift'],2)
        self.assertFalse(out['uniform_middle_bound_proved']);self.assertFalse(out['RH_proved'])
        self.assertIn('not original K',out['target_scope'])
        for x,y in ((1,2),(-3,4),(7,-5)):
            energy=Q(10,7)*x*x-Q(12,7)*x*y+Q(12,7)*y*y
            self.assertEqual(energy,x*x+Q(3,7)*(x-2*y)**2)
            self.assertGreaterEqual(energy,x*x)

    def test_logarithmic_and_arbitrary_delta_recovery(self):
        m=meter()
        for delta in ('0','1/257','7/3'):
            r,c=recovery(delta=delta,weights=('1/3','1/3','1/3'))
            out=C.verify_recovery(r,c,m)
            self.assertEqual(out['recovery']['logarithm_base'],2)
            self.assertEqual(out['recovery']['kind'],'logarithmic' if delta=='0' else 'bounded')
        # Exact worst-parent recursive control validates the shifted log count.
        r,c=recovery(delta='0');B=Q(c['base_upper']);forcing=Q(r['C'])
        values={n:B for n in range(2,6)}
        for child in range(6,1025):
            N=child//2
            values[child]=max(values[N+s] for s in (-1,0,1))+forcing
            count=max(0,(child-2).bit_length()-2)
            self.assertLessEqual(values[child],B+forcing*count)
        m.charge(10000)

    def test_recovery_omitted_parity_neighbor_seeds_and_prices_rejected(self):
        m=meter();r,c=recovery()
        mutations=[('matrix_terms',c['matrix_terms'][:1]),('source_envelopes',['1','40']),
            ('base_upper','1'),('uniform_recurrence_proved',True),('RH_proved',True)]
        for key,value in mutations:
            bad=copy.deepcopy(c);bad[key]=value
            with self.assertRaises(ValueError):C.verify_parent_recovery(r,bad,m)
        for key,value in [('children',[0]),('offsets',[0]),('minimum',2),('status','PROVED')]:
            bad=copy.deepcopy(c);bad['recurrence'][key]=value
            with self.assertRaises(ValueError):C.verify_parent_recovery(r,bad,m)
        for key,value in [('argument_shift',0),('base_maximum',3),('constant',c['base_upper']),('logarithm_base',2.0)]:
            bad=copy.deepcopy(c);bad['recovery'][key]=value
            with self.assertRaises(ValueError):C.verify_parent_recovery(r,bad,m)

    def test_recovery_invalid_source_convexity_or_unpriced_cost(self):
        m=meter();r,c=recovery()
        for key,value in [('weights',['1','1','0']),('weights',['-1','1','1']),
                ('coefficients',[True,-2]),('coefficients',[1]),('lambda','-1'),
                ('delta','-1'),('C','-1'),('alpha','1')]:
            bad=copy.deepcopy(r);bad[key]=value
            with self.assertRaises(ValueError):C.verify_parent_recovery(bad,c,m)
        bad=copy.deepcopy(r);bad['features'][0]['primes']=[]
        with self.assertRaises(ValueError):C.verify_parent_recovery(bad,c,m)
        bad=copy.deepcopy(r);bad['features'][1]=copy.deepcopy(bad['features'][0])
        with self.assertRaises(ValueError):C.verify_parent_recovery(bad,c,m)


if __name__=='__main__':
    try:unittest.main()
    finally:print('SYNTHETIC_WORK module=check_prime_insertion_middle_057 operations='+str(sum(m.operations for m in METERS)))
