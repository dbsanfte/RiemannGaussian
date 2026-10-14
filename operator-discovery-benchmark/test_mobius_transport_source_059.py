"""Tiny custom-band source fixtures only; no scientific source N>=64."""
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import time
import unittest
from unittest.mock import patch
import numpy as np
import mobius_transport_source_059 as S

METERS=[]


def meter(**kwargs):
    value=S.Meter(**kwargs);METERS.append(value);return value


def request(N=7,primes=(2,3),p=2,q=3,alpha='1/3',gamma='2',tau='2/5'):
    return {'N':N,'alpha':alpha,'gamma':gamma,'tau':tau,'primes':list(primes),'p':p,'q':q}


def factors(n):
    rest,primes=n,[]
    for p in range(2,math.isqrt(n)+1):
        if rest%p==0:
            primes.append(p)
            while rest%p==0:rest//=p
    if rest>1:primes.append(rest)
    return primes


def mu(n):
    primes=factors(n)
    return 0 if any(n%(p*p)==0 for p in primes) else (-1)**len(primes)


def W(N,k,d):
    return 4*N//(k*d)-3*(2*N//(k*d))+2*(N//(k*d))


def G(primes,t):
    return math.prod(-math.expm1(-math.log(p)*t) for p in set(primes))


def scalar_nodes(req,degree):
    eps=min(float(Q(req['tau'])),math.exp(-float(Q(req['gamma']))*math.log(req['N'])))
    tau=float(Q(req['tau']))
    nodes,weights=np.polynomial.legendre.leggauss(degree)
    ts=(tau+eps)/2+(tau-eps)*nodes/2
    weights=weights*(tau-eps)/2/math.gamma(float(1-Q(req['alpha'])))
    return ts,weights


class TransportTests(unittest.TestCase):
    def test_all_quotient_weight_cases_and_exact_profile_signs(self):
        work=meter()
        for a in (-1,0,1):
            for b in (-1,0,1):
                if (a,b)==(0,0):continue
                profile,sign=S.classify_pair(a,b)
                mag={'P':Q(5),'Q':Q(3),'D':Q(2),'S':Q(8)}[profile]
                self.assertEqual(a*5-b*3,sign*mag)
                for mobius in (-1,1):self.assertEqual(mobius*(a*5-b*3),mobius*sign*mag)
                work.charge(20)
        with self.assertRaises(ValueError):S.classify_pair(0,0)
        with self.assertRaises(ValueError):S.classify_pair(True,1)
        for N in range(2,32):
            for d in range(1,4*N+1):
                self.assertIn(W(N,2,d),(-1,0,1));self.assertIn(W(N,3,d),(-1,0,1))
                work.charge(8)

    def test_integer_source_tokens_mu_coprimality_unit_and_range_exit(self):
        work=meter();context=S.prepare_context(work)
        exits=units=0
        for N in (2,3,5,7,11,17):
            req=request(N,primes=(2,3,5),p=3,q=5)
            result=S.evaluate(req,degree=16,meter=work,context=context)
            expected=[]
            for d in range(1,4*N//3+1):
                a,b=W(N,3,d),W(N,5,d)
                if mu(d) and math.gcd(d,30)==1 and (a,b)!=(0,0):
                    profile,sigma=S.classify_pair(a,b)
                    expected.append((d,profile,sigma,mu(d)*sigma,mu(d)))
                    exits+=d>4*N//5;units+=d==1
                work.charge(20)
            self.assertEqual([(t['d'],t['profile'],t['kernel_sign'],t['sign'],t['mu']) for t in result['tokens']],expected)
            self.assertTrue(all(math.isfinite(t['magnitude']) and t['magnitude']>0 for t in result['tokens']))
        self.assertGreater(exits,0);self.assertGreater(units,0)

    def test_joined_sum_equals_independent_direct_prime_product_integrand(self):
        work=meter()
        for req in (request(5),request(7,(2,3,5),3,5),request(9,(3,7),3,7)):
            degree=64
            result=S.evaluate(req,degree,meter=work)
            ts,weights=scalar_nodes(req,degree)
            total=0.0
            for t,weight in zip(ts,weights):
                def H(subset):
                    value=0.0
                    for n in range(1,4*req['N']+1):
                        c=int(2*req['N']<n<=4*req['N'])-2*int(req['N']<n<=2*req['N'])
                        value+=c*G(set(subset)|set(factors(n)),float(t))
                    return value
                M=req['primes'];p=req['p'];q=req['q']
                signed=(-math.expm1(-math.log(q)*t))*H([r for r in M if r!=q])-(-math.expm1(-math.log(p)*t))*H([r for r in M if r!=p])
                total+=float(weight)*signed*float(t)**(-1-float(Q(req['alpha'])))
                work.charge(200*4*req['N'])
            self.assertAlmostEqual(result['signed_sum'],total,delta=2e-12*(1+abs(total)))
            self.assertGreaterEqual(result['absolute_sum']+1e-14,abs(result['signed_sum']))
            self.assertFalse(result['numeric']['quadrature_error_certified'])
            self.assertFalse(result['numeric']['rigorous_source_interval_admitted'])

    def test_stable_difference_and_independent_scalar_phi_profiles(self):
        work=meter();req=request(13,(2,5),2,5)
        result=S.evaluate(req,degree=96,meter=work)
        ts,weights=scalar_nodes(req,96)
        for token in result['tokens']:
            d=token['d']
            phi=lambda k:math.fsum(float(w)*G(req['primes'],float(t))*math.exp(-math.log(k*d)*t)*t**(-1-float(Q(req['alpha']))) for t,w in zip(ts,weights))
            P,Qvalue=phi(req['p']),phi(req['q'])
            expected={'P':P,'Q':Qvalue,'D':P-Qvalue,'S':P+Qvalue}[token['profile']]
            self.assertAlmostEqual(token['magnitude'],expected,delta=2e-13*(1+abs(expected)))
            work.charge(100*len(ts))
        values=[token for token in result['tokens'] if token['profile']=='D']
        self.assertTrue(values)
        self.assertTrue(all(t['magnitude']>0 for t in values))

    def test_arbitrary_rationals_exact_empty_gate_and_zero_source_range(self):
        work=meter();context=S.prepare_context(work)
        with patch.object(S,'_quadrature',side_effect=AssertionError('quadrature in exact empty band')):
            with patch.object(S,'_log_arrays',side_effect=AssertionError('logs in exact empty band')):
                for req in (request(2,gamma='1',tau='2/5'),request(4,gamma='1',tau='1/4'),
                            request(2,alpha='1/257',gamma='1/257',tau='1/2')):
                    result=S.evaluate(req,meter=work,context=context)
                    self.assertTrue(result['numeric']['empty_band_exact'])
                    self.assertEqual(result['signed_sum'],0)
                    self.assertEqual(result['absolute_sum'],0)
                    self.assertTrue(all(t['magnitude']==0 for t in result['tokens']))
        nonempty=S.evaluate(request(3,alpha='1/257',gamma='257/128',tau='2/5'),meter=work)
        self.assertFalse(nonempty['numeric']['empty_band_exact'])
        zero_range=S.evaluate(request(2,(11,13),11,13),meter=work)
        self.assertEqual(zero_range['tokens'],[]);self.assertEqual(zero_range['signed_sum'],0)

    def test_caches_are_literal_and_optional(self):
        work=meter();context=S.prepare_context(work)
        req=request(7)
        first=S.evaluate(req,degree=32,meter=work,context=context)
        second=S.evaluate(req,degree=32,meter=work,context=context)
        self.assertEqual(first['tokens'],second['tokens'])
        for key in ('mu_sieve_entries','integer_weight_entries','log_atoms','quadrature_nodes'):
            self.assertEqual(second['counts']['total_primitive_counts'][key],0)
        changed=S.evaluate(dict(req,gamma='3'),degree=32,meter=work,context=context)
        self.assertEqual(changed['counts']['total_primitive_counts']['log_atoms'],0)
        self.assertEqual(changed['counts']['total_primitive_counts']['quadrature_nodes'],0)
        optional=S.prepare_context(work,max_bytes=0)
        S.evaluate(req,degree=16,meter=work,context=optional)
        self.assertEqual(optional.bytes_estimate,0)
        self.assertTrue(first['numeric']['numerical_screening_only'])
        self.assertFalse(first['numeric']['uniform_bound_proved'])
        self.assertFalse(first['numeric']['rh_proved'])

    def test_float_unresolved_endpoint_does_not_promote_zero(self):
        work=meter()
        tau=str(Q(1,2)+Q(1,2**101))
        self.assertFalse(S._band_empty(2,Q(1),Q(tau),work))
        with self.assertRaises(ArithmeticError):S.evaluate(request(2,gamma='1',tau=tau),meter=work)

    def test_adversarial_domains_and_resource_preflight(self):
        work=meter()
        for key,value in (('N',True),('N',S.MAX_N+1),('alpha','1'),('alpha','2/4'),
                          ('gamma','0'),('tau','1'),('primes',[2,2,3]),('primes',[3,2]),
                          ('primes',[2,4]),('p',3),('q',5)):
            bad=request();bad[key]=value
            with self.assertRaises(ValueError):S.evaluate(bad,meter=work)
        bad=request();bad['extra']=0
        with self.assertRaises(ValueError):S.evaluate(bad,meter=work)
        with self.assertRaises(ValueError):S.evaluate(request(),degree=7,meter=work)
        with self.assertRaises(OverflowError):S.evaluate(request(2,gamma='400000'),meter=work)
        with self.assertRaises(OverflowError):S.evaluate(request(),meter=meter(cap=0))
        expired=meter();expired.deadline=time.monotonic()-1
        with self.assertRaises(TimeoutError):S.evaluate(request(),meter=expired)
        with patch.object(S,'MAX_WORKING_BYTES',1024**2):
            with patch.object(S,'_mu',side_effect=AssertionError('allocation before preflight')):
                with self.assertRaises(MemoryError):S.evaluate(request(31),meter=work)
        with self.assertRaises(MemoryError):work.reserve(S.MAX_WORKING_BYTES+1)


if __name__=='__main__':
    path=Path(__file__).with_name('mobius_transport_source_059_development.json')
    if path.exists():raise SystemExit('retain prior focused receipt')
    started=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(TransportTests))
    counts=[m.counts() for m in METERS]
    receipt={'schema':'mobius-transport-source-059-development-v1','invocations':[{
        'returncode':0 if result.wasSuccessful() else 1,'tests':result.testsRun,
        'failures':len(result.failures),'errors':len(result.errors),
        'elapsed_seconds':time.monotonic()-started,'operations':sum(c['operations'] for c in counts)}],
        'total_primitive_counts':{k:sum(c['total_primitive_counts'][k] for c in counts)
                                 for k in S.Meter().primitives},
        'peak_bytes_estimate':max((c['peak_bytes_estimate'] for c in counts),default=0),
        'scope':'tiny N<=17 numerical custom-band fixtures and exact/cap tests N<64 only; no scientific source tables',
        'scientific_pilot_applied':False,'old_suites_or_studies_replayed':False,
        'checker_imported':False,'numerical_screening_only':True,'uniform_bound_or_rh_claimed':False}
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
