import unittest
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import mobius_square_witness_084 as P
import check_mobius_square_witness_084 as C
import check_mobius_coupled_square_084 as SQ
from test_mobius_coupled_square_084 import program


class WitnessTests(unittest.TestCase):
    def test_literal_witness_bounds_every_tested_square(self):
        A=[[Q(-2),Q(3,2),Q(-1)],[Q(3,2),Q(0),Q(2)],[Q(-1),Q(2),Q(1)]]
        factors=[([[],[],[]],1),([[1],[2],[-1]],2),([[1,0],[0,1],[1,-1]],4)]
        for signs in product([-1,1],repeat=3):
            v=C.quadratic_value(A,list(signs))
            for L,den in factors:self.assertLessEqual(v,SQ.square_price(A,L,den)['price'])

    def test_independent_complete_integration_and_mutations(self):
        p=program();outer=P.S.O.synthesize(p)['certificate'];proposal=P.propose(p,131)
        cert=proposal['certificate'];admission=C.verify(p,131,outer,cert)
        self.assertEqual(admission['status'],'VERIFIED_FINITE_FIXED_OPERATOR_SQUARE_LOWER_BOUND')
        self.assertFalse(admission['actual_signed_drift_lower_bound_proved'])
        for key,value in [('lower_bound',str(Q(cert['lower_bound'])+1)),('squarefree_count',cert['squarefree_count']+1),('signs',cert['signs'][:-1])]:
            bad=deepcopy(cert);bad[key]=value
            self.assertNotEqual(C.verify(p,131,outer,bad)['status'],admission['status'])

    def test_prospective_shape_and_strict_signs(self):
        with self.assertRaises(C.ResourceLimit):C.quadratic_value([], [1]*513)
        with self.assertRaises(C.AdmissionError):C.quadratic_value([[Q(1)]],[True])
        with self.assertRaises(C.AdmissionError):C.quadratic_value([[Q(1)]],[0])
        with self.assertRaises(C.AdmissionError):C.quadratic_value([[Q(1)]],[1,-1])


if __name__=='__main__':unittest.main()
