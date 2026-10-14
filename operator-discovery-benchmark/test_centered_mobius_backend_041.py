"""Synthetic coefficients, plus an isolated analytic-normalization regression."""
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
import time
import unittest
from unittest.mock import patch
import numpy as np
import centered_mobius_backend_041 as P

METERS=[]
def meter(cap=2_000_000):
    m=P.Meter(cap,120); METERS.append(m); return m


def toy_mu(n):
    sign=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;sign=-sign
            if n%p==0:return 0
        p+=1
    return -sign if n>1 else sign


def toy_power(n):
    # Multiplicative toy K(p)=1/2 for EVERY prime; no p^-r observations.
    count=0;p=2
    while p*p<=n:
        while n%p==0:n//=p;count+=1
        p+=1
    if n>1:count+=1
    return Q(1,2)**count


class CenteredMobius(unittest.TestCase):
    def test_normalization_integer_ceiling_and_serialization(self):
        # Scalar-only integration: no arithmetic coefficients or search observations.
        m=meter();norm=P.normalization_certificate('1/3',2,meter=m)
        json.dumps(norm)
        K=int(norm['absolute_ceiling'])
        with P.ctx.workprec(256):
            r=P.arb(1)/3;theta=1-r
            kappa=(1-P.arb(2)**r)/(theta*theta.zeta())
            self.assertGreater(kappa,0)
            self.assertLessEqual(abs(kappa),K)
            self.assertGreater(abs(kappa),K-1)
        self.assertEqual(norm['certificate']['increment']['absolute_bound'],str(3+K))
        self.assertFalse(norm['ordinary_mu_theta_series_convergence_used'])

    def test_exact_local_convolution_repeated_primes_and_units(self):
        m=meter();H=63;spf=P.smallest_prime_factors(H,m)
        b=P.multiplicative_coefficients(spf,lambda p:0.5,m)
        self.assertEqual(b[0],0);self.assertEqual(b[1],1)
        for n in range(1,H+1):
            m.charge(128*(n+1))
            expected=sum((Q(toy_mu(d))*toy_power(n//d) for d in range(1,n+1) if n%d==0),Q(0))
            self.assertEqual(b[n],float(expected));self.assertLessEqual(abs(b[n]),1)
        for p in (2,3,5,7):
            for n in range(1,H//p+1):
                m.charge(16)
                self.assertEqual(b[p*n],b[n]*(0.5 if n%p==0 else -0.5))
        for p in (2,3):
            c=P.center_coefficients(b,p,'1/2',0,m)['c']
            for n in range(1,H//p+1):
                m.charge(32)
                crossing=p*b[n//p] if n%p==0 and (n//p)%p else 0
                expected=.5*c[n]-(p+1)*b[n]*(n%p!=0)+crossing
                self.assertEqual(c[p*n],expected)

    def test_complete_periodic_center_unit_and_composite_period(self):
        m=meter();b=np.array([0,1,-.5,-.25,.125,-.125,.25,.125,-.0625])
        for q in (2,4,13):
            centered=P.center_coefficients(b,q,'2/3',.75,m)
            expected_c=[0]+[b[n]-(q*b[n//q] if n%q==0 else 0) for n in range(1,len(b))]
            self.assertEqual(list(centered['c']),expected_c)
            for n in range(1,len(b)):
                expected=sum(expected_c[1:n+1])-.75*n**(2/3)
                self.assertAlmostEqual(centered['J'][n],expected,places=13)
                self.assertAlmostEqual(centered['J'][n]-centered['J'][n-1],centered['a'][n],places=13)
            self.assertEqual(centered['a'][1],.25)
            for array in centered.values():self.assertEqual(array[0],0)

    def test_periodic_dilation_identity_including_subunit_main(self):
        m=meter();b=np.array([0,1,-.5,-.25,.125,-.125,.25,.125,-.0625]);q=3
        theta=.6;ordinary_kappa=-1.25
        centered=P.center_coefficients(b,q,'3/5',ordinary_kappa*(1-q**(1-theta)),m)
        prefix=np.cumsum(b)
        for n in range(1,len(b)):
            J=prefix[n]-ordinary_kappa*n**theta
            half=prefix[n//q]-ordinary_kappa*(n/q)**theta
            self.assertAlmostEqual(centered['J'][n],J-q*half,places=13)
        # Discarding the centered subunit term would change the n1 result.
        self.assertNotEqual(centered['J'][1],prefix[1]-ordinary_kappa)

    def test_symbolic_arbitrary_denominator_and_bounds(self):
        m=meter();cert=P.symbolic_certificate('1/257',5,'7',m)
        self.assertEqual(cert['theta'],'256/257')
        self.assertEqual(cert['increment']['absolute_bound'],'13')
        self.assertEqual(cert['local']['numerator'],['1','-1'])
        self.assertEqual(cert['local']['denominator'],['1','-p^-r'])
        self.assertFalse(cert['prefix_energy_bound_proved']);self.assertFalse(cert['RH_proved'])
        uncentered=P.symbolic_certificate('2/7',4,meter=m)
        self.assertIsNone(uncentered['increment']['absolute_bound'])
        b=P.multiplicative_coefficients(P.smallest_prime_factors(63,m),lambda p:.5,m)
        values=P.center_coefficients(b,5,'5/7',-7,m)
        self.assertLessEqual(np.max(np.abs(values['a'])),13)
        for n in range(1,64):self.assertLessEqual(n**(5/7)-(n-1)**(5/7),1)

    def test_invalid_domains_failures_and_caps(self):
        m=meter()
        for r,q in ((.25,2),('1/1',2),('0',2),('1/2',2),('-1/4',2),('2/8',2),('1/4',True),('1/4',1)):
            with self.assertRaises(ValueError):P.symbolic_certificate(r,q,meter=m)
        for ceiling in ('1/1','-1','01',True):
            with self.assertRaises(ValueError):P.symbolic_certificate('1/4',2,ceiling,m)
        for v in (0,1,float('nan')):
            with self.assertRaises(ArithmeticError):P.multiplicative_coefficients(P.smallest_prime_factors(3,m),lambda p:v,m)
        with self.assertRaises(ValueError):P.center_coefficients(np.array([1.,1.]),2,'2/3',0,m)
        with self.assertRaises(ArithmeticError):P.center_coefficients(np.array([0.,1.]),2,'2/3',float('inf'),m)
        with self.assertRaises(ValueError):P.multiplicative_coefficients(np.array([0,0,3]),lambda p:.5,m)
        low=meter(3)
        with self.assertRaises(OverflowError):P.smallest_prime_factors(9,low)
        with self.assertRaises(MemoryError):P.smallest_prime_factors(P.MAX_CELLS,m)
        with patch.object(P,'normalization_certificate',side_effect=AssertionError('must not evaluate invalid horizon')):
            with self.assertRaises(ValueError):P.build_state(0,meter=m)

    def test_production_api_with_injected_synthetic_normalization_and_coefficients(self):
        m=meter();cert=P.symbolic_certificate('1/4',3,'1',m)
        norm=dict(schema='centered-mobius-normalization-v1',r='1/4',q=3,theta='3/4',precision=192,
                  kappa='0.5',absolute_ceiling='1',certificate=cert,
                  ordinary_mu_theta_series_convergence_used=False)
        b=np.array([0.,1.,-.5,.25,-.125])
        with patch.object(P,'normalization_certificate',return_value=norm),patch.object(P,'multiplicative_coefficients',return_value=b):
            result=P.build_state(4,'1/4',3,normalization=norm,meter=m)
        self.assertEqual(result['H'],4);self.assertEqual(result['J'][1],.5)
        self.assertFalse(result['metadata']['float_roundoff_is_interval_certified'])
        self.assertFalse(result['metadata']['prefix_energy_bound_proved'])
        self.assertEqual(result['metadata']['operations'],m.operations)
        self.assertTrue(all(result[k][0]==0 for k in ('b','c','prefix','main','J','a')))


if __name__=='__main__':
    start=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(CenteredMobius))
    operations=sum(m.operations for m in METERS)
    receipt_path=Path(__file__).with_name('centered_mobius_backend_041_development.json')
    previous=json.loads(receipt_path.read_text()) if receipt_path.exists() else {'schema':'centered-mobius-development-v1','invocations':[]}
    code=0 if result.wasSuccessful() else 1
    invocation={'returncode':code,'operations':operations,'tests':result.testsRun,
                'failures':len(result.failures),'errors':len(result.errors),'elapsed_seconds':time.monotonic()-start,
                'source_exposure':'synthetic local p-parameter1/2 and injected rational centers only; no selected-source coefficient/normalization or archive reads'}
    previous['invocations'].append(invocation)
    previous['cumulative_operations']=sum(i['operations'] for i in previous['invocations'])
    receipt_path.write_text(json.dumps(previous,indent=2)+'\n')
    print('SYNTHETIC_WORK module=test_centered_mobius_backend_041 operations='+str(operations))
    sys.exit(code)
