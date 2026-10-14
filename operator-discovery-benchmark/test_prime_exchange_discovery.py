"""Exact joint-factor and full-support calibration; no new source study."""
from fractions import Fraction as Q
import unittest

import prime_slide_discovery as S
import prime_exchange_discovery as P
import check_prime_exchange_discovery as C

METERS=[]
def meter():
    m=S.Meter();METERS.append(m);return m
def tearDownModule():
    print('SYNTHETIC_WORK module=test_prime_exchange_discovery operations='+str(sum(m.operations for m in METERS)))


class ExchangeTests(unittest.TestCase):
    def test_generic_primitive_linear_dictionary_and_fractional_division(self):
        m=meter();self.assertEqual(len(P.linear_forms()),48);self.assertEqual(P.linear_forms(),C.linear_forms())
        poly={(0,1):Q(-1),(0,2):Q(-1),(1,0):Q(1),(1,1):Q(-1),(2,0):Q(2)}
        self.assertEqual(P.divide(poly,[2,1,1],m),{(1,0):Q(1),(0,1):Q(-1)})
        self.assertIsNone(P.divide(poly,[1,1,0],m))
        self.assertEqual(P.divide({(0,1):Q(1),(0,0):Q(1,2)},[0,2,1],m),{(0,0):Q(1,2)})
        self.assertEqual(P.divide({},[1,0,0],m),{})

    def test_diagonal_vanishing_is_detected_without_coordinatewise_vanishing(self):
        m=meter();engine=S.Engine(m)
        program=dict(binding='distinct_primes',terms=[
            dict(coefficient=1,left=[1,0],right=[0,1]),
            dict(coefficient=-1,left=[0,1],right=[1,0])])
        facts=engine.facts(program)
        self.assertEqual(facts['common_valuations'],[0,0])
        row=P.record(dict(id=1,program=program,multipliers=facts['multipliers']),m)
        self.assertEqual(row['factors'],[
            dict(coefficients=[0,1,-1],multiplicity=1),dict(coefficients=[1,-1,0],multiplicity=1),
            dict(coefficients=[1,0,-1],multiplicity=1)])
        C.verify(row['original'],row['factors'],row['quotients'],m)
        self.assertEqual(row['envelope']['prime_weight'],'1/3')
        self.assertTrue(row['full_kernel_correction_admissible'])
        self.assertEqual(len(row['edge_constructions']),3)
        self.assertTrue(all(edge['bound']['cofinal'] for edge in row['edge_constructions']))
        self.assertEqual(row['symmetric_core'],'OPEN');self.assertFalse(row['whole_signed_bound_proved'])

    def test_nonexchange_and_unit_factors_do_not_receive_edge_credit(self):
        m=meter();engine=S.Engine(m)
        program=dict(binding='distinct_primes',terms=[dict(coefficient=1,left=[1,1],right=[0,0])])
        facts=engine.facts(program);row=P.record(dict(id=2,program=program,multipliers=facts['multipliers']),m)
        C.verify(row['original'],row['factors'],row['quotients'],m)
        self.assertEqual(row['envelope']['prime_weight'],'0')
        self.assertFalse(row['full_kernel_correction_admissible']);self.assertEqual(row['edge_constructions'],[])

    def test_cutoff_and_both_orientation_kernels_match_literal_integer_domains(self):
        m=meter()
        for X in (16,32,64,128):
            for r,q in ((17,19),(29,31),(43,47)):
                for H,K in ((2,2),(2,3),(3,2),(3,4)):
                    A,B=P.kernels(X,q,r,H,K,'3/4',m);literal_A=literal_B=0
                    for n in range(X,2*X):
                        m.charge(12)
                        literal_A+=int(n**3<r**4 and q*H<=n and r*K<=n)
                        literal_B+=int(n**3<r**4 and r*H<=n and q*K<=n)
                    self.assertEqual((A,B),(literal_A,literal_B))
        A,B=P.kernels(64,31,29,2,3,'3/4',m)
        self.assertGreater(A,0);self.assertEqual(B,0)  # the complement cannot be clipped away

    def test_symmetric_core_and_exchange_correction_recompose_complete_pair(self):
        m=meter()
        for x,y in ((Q(1,4),Q(2,5)),(Q(2,7),Q(3,5))):
            zuH,zvH,zuK,zvK=Q(2),Q(-3),Q(-1),Q(4)
            PA=((x-1)*zuH+(x*x-1)*zvH)*((y-1)*zuK+(y*y-1)*zvK)
            PB=((y-1)*zuH+(y*y-1)*zvH)*((x-1)*zuK+(x*x-1)*zvK)
            D=(1-x)*(1-y)*(y-x);m.charge(80)
            self.assertEqual(PA-PB,D*(zuH*zvK-zvH*zuK))
            for A,B in ((3,0),(0,2),(5,7)):
                m.charge(20)
                self.assertEqual((PA*A+PB*B)/2,(PA+PB)*(A+B)/4+(PA-PB)*(A-B)/4)

    def test_edge_geometry_and_log_cost_match_independent_bound(self):
        m=meter()
        for theta,weight,degree in (('3/4','1/3','1'),('4/5','1/3','4'),('1/2','1/3','2')):
            row=P.edge_bound(theta,weight,degree,m);other=C.edge_bound(theta,weight,degree,m)
            for key in row:self.assertEqual(row[key],other[key])
        self.assertFalse(P.edge_bound('1/2','1/3','1',m)['cofinal'])
        with self.assertRaises(ValueError):P.edge_bound('3/4','0','1',m)
        with self.assertRaises(ValueError):P.kernels(1,3,5,2,2,'3/4',m)


if __name__=='__main__':unittest.main()
