"""Calibration fixtures only; no research instances or scores."""
import time
import unittest
from fractions import Fraction as F
from unittest.mock import patch
from types import SimpleNamespace
import primitive_state_numerical_proposals as P

class CompressionTests(unittest.TestCase):
    def compress(self,rows,rhs,**limits):
        return P.compress_rows(rows,rhs,2,deadline=time.monotonic()+10,**limits)
    def test_signed_proportional_and_zero(self):
        rows=[{0:F(2),1:F(4)},{0:F(-3),1:F(-6)},{}, {0:F(2),1:F(4)}]
        reduced,b,r=self.compress(rows,[F(6),F(-9),F(0),F(7)])
        self.assertEqual(r['retained_indices'],[0,3])
        self.assertEqual(r['row_representative'],[0,0,None,1])
        self.assertEqual(r['row_multiplier'],['1','-3/2','0','1'])
        self.assertEqual(r['row_scales'],['6','7'])
        self.assertEqual(reduced,[rows[0],rows[3]])
        self.assertEqual(b,[F(6),F(7)])
    def test_inconsistent_zero(self):
        reduced,b,r=self.compress([{},{}],[F(1),F(-2)])
        self.assertEqual(r['inconsistent_zero_rows'],[0,1])
        self.assertEqual(r['row_multiplier'],['1','-2'])
    def test_bounds_and_exact_input(self):
        with self.assertRaises(OverflowError):self.compress([{0:F(1)}],[F(0)],max_operations=1)
        with self.assertRaises(ValueError):self.compress([{0:0.1}],[F(0)])
        with self.assertRaises(TimeoutError):P.compress_rows([{}],[F(0)],1,deadline=0)
    def test_float_underflow_rejected(self):
        with self.assertRaises(OverflowError):P._matrix([{0:F(1,2**2000)}],[F(1)],1,{'row_scales':['1']})

class SolverTests(unittest.TestCase):
    def dual(self):
        return P.support_proposal([{('x',):F(1)},{('x',):F(-1)}],{('y',):F(1)},[('x',),('y',)],[],[0,1],deadline=time.monotonic()+10,max_rows=10,max_variables=10,max_work=1000)
    def test_dual_missing_values(self):
        with patch('scipy.optimize.linprog',return_value=SimpleNamespace(status=0,message='missing',success=True,x=None)):
            support,d=self.dual()
        self.assertIsNone(support);self.assertEqual(len(d['attempts']),1)
        self.assertEqual(d['transformation_receipt']['retained_indices'],[0,2])
    def test_dual_failure_retained(self):
        with patch('scipy.optimize.linprog',return_value=SimpleNamespace(status=4,message='unknown',success=False,x=None)):
            support,d=self.dual()
        self.assertIsNone(support);self.assertEqual(d['solver_status'],4);self.assertEqual(d['attempts'][0]['message'],'unknown')
    def test_dual_nonfinite(self):
        with patch('scipy.optimize.linprog',return_value=SimpleNamespace(status=0,message='bad',success=True,x=[float('nan')]*4)):
            support,d=self.dual()
        self.assertIsNone(support);self.assertTrue(d['invalid_values'])
    def test_primal_psd_and_scalar_identity(self):
        # x + G00=2, G01=1/2, G11=1: all original coordinates returned.
        columns=[{('a',):F(1)},{('a',):F(1)},{('b',):F(1)},{('c',):F(1)}]
        vector,d=P.primal_proposal(columns,{('a',):F(2),('b',):F(1,2),('c',):F(1)},[('a',),('b',),('c',)],(1,0),1,{'G':2},deadline=time.monotonic()+10)
        self.assertIsNotNone(vector)
        self.assertAlmostEqual(vector[0]+vector[1],2,places=6)
        self.assertAlmostEqual(vector[2],.5,places=6)
        self.assertGreaterEqual(vector[1]*vector[3]-vector[2]**2,-1e-6)
        self.assertEqual(d['transformation_receipt']['variable_mapping'],'identity')
        self.assertEqual(d['support'][-3:],[1,2,3])
    def test_primal_failure_no_values(self):
        import cvxpy as cp
        with patch.object(cp.Problem,'solve',side_effect=cp.error.SolverError('calibration failure')):
            vector,d=P.primal_proposal([{('a',):F(1)}],{('a',):F(1)},[('a',)],(0,0),0,{'G':1},deadline=time.monotonic()+10)
        self.assertIsNone(vector);self.assertEqual(d['solver_error'],'calibration failure')
        self.assertEqual(len(d['attempts']),1)

if __name__=='__main__':unittest.main()
