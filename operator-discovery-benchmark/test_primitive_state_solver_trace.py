import time
import unittest
from fractions import Fraction as F
import primitive_state_solver_trace as t

class TraceTests(unittest.TestCase):
    def test_support(self):
        x=t.trace_support([{('x',):F(1)}],{('x',):F(-1)},[('x',)],[0],[],deadline=time.monotonic()+10,max_rows=10,max_variables=10,max_work=1000)
        self.assertEqual(x['termination_status'],0)
        self.assertLess(x['diagnostics']['equality_max_abs'],1e-8)
        self.assertEqual(len(x['original_vector']),3)
    def test_primal(self):
        x=t.trace_primal([{('x',):F(1)}],{('x',):F(2)},[('x',)],(0,0),0,{'gram':1},deadline=time.monotonic()+10)
        self.assertEqual(x['termination_status'],'Solved')
        self.assertAlmostEqual(x['original_vector'][0],2)
        self.assertGreater(x['diagnostics']['psd_min_eigenvalues']['gram'],0)
    def test_log_overflow(self):
        import os
        with t.native_log(max_bytes=5) as log:os.write(1,b'0123456789')
        self.assertEqual(log['overflow_bytes'],5)
        self.assertEqual(log['text'],'01234')
    def test_unknown(self):
        A,b,x=t.prepare([{0:F(1)}],[F(1)],1,[1.],[0],[],time.monotonic()+10,{})
        t.evaluate(x)
        self.assertIsNone(x['diagnostics']['equality_max_abs'])
    def test_partial_nonfinite_iterate_remains_unavailable(self):
        A,b,x=t.prepare([{0:F(1)}],[F(1)],2,[1.,1.],[0,1],[],time.monotonic()+10,{})
        x['original_vector']=[1.,None]
        result=t.finish(x)
        self.assertEqual(result['vector_role'],'unavailable')
        self.assertIsNone(result['original_vector'])
        self.assertEqual(result['raw_partial_original_vector'],[1.,None])

if __name__=='__main__':unittest.main()
