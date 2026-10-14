from fractions import Fraction as F
import hashlib
import json
import math
import tempfile
import time
import unittest
from unittest.mock import patch
import primitive_state_basis_primal as B
import check_primitive_state_basis_primal as C

class PrimalTests(unittest.TestCase):
    def test_direct_assembly_independent_hash(self):
        columns=[{'a':F(2)},{'a':F(-2)},{'a':F(4)},{'b':F(1)},{'b':F(2)},{'b':F(3)}]
        args=(columns,{'a':F(8),'b':F(6)},['a','b'],[0,1],3,{'gram':2},[1,0])
        data,receipt=B.assemble(*args,deadline=time.monotonic()+10)
        rebuilt=C.reconstruct(*args)
        for key,value in rebuilt['receipt'].items():self.assertEqual(receipt[key],value)
        self.assertEqual(receipt['selected_row_scales'],['6','8']);self.assertEqual(receipt['layout']['objective'],[1.,1.,0.,1.,0.,1.])
        self.assertEqual(receipt['cones'],[['Zero',2],['Nonnegative',3],['PSDTriangle',2]])
        A=data['A'].toarray();self.assertEqual(A[-3,3],-1.);self.assertEqual(A[-2,4],-math.sqrt(2));self.assertEqual(A[-1,5],-1.)
    def test_tiny_native_solution_original_coordinates(self):
        args=([{'a':F(1)}],{'a':F(2)},['a'],[0,0],0,{'gram':1},[0])
        trace=B.solve_trace(*args,deadline=time.monotonic()+10)
        self.assertEqual(trace['termination_status'],'Solved');self.assertEqual(trace['raw_solution']['x'],trace['original_vector'])
        self.assertAlmostEqual(trace['original_vector'][0],2);self.assertFalse(trace['certified'])
        check=C.verify_trace(trace,*args);self.assertTrue(check['canonical_system_independently_rebuilt'])
    def test_failed_raw_negative_scalars_never_clipped(self):
        args=([{'a':F(1)},{'a':F(1)}],{'a':F(-1)},['a'],[1,0],1,{'gram':1},[0])
        from types import SimpleNamespace
        solution=SimpleNamespace(x=[-.5,-.5],status='NumericalError',iterations=1)
        class Solver:
            def __init__(self,*a):pass
            def set_termination_callback(self,*a):pass
            def solve(self):pass
            def get_solution(self):return solution
            def get_info(self):return SimpleNamespace(status='NumericalError',iterations=1)
        with patch('clarabel.DefaultSolver',Solver):trace=B.solve_trace(*args,deadline=time.monotonic()+10)
        self.assertEqual(trace['original_vector'],[-.5,-.5]);self.assertEqual(trace['diagnostics']['nonnegative_min'],-.5)
        self.assertEqual(trace['vector_role'],'raw_failed_last_iterate');C.verify_trace(trace,*args)
    def test_log_path_retains_verifiable_text(self):
        from pathlib import Path
        args=([{'a':F(1)}],{'a':F(2)},['a'],[0,0],0,{'gram':1},[0])
        with tempfile.TemporaryDirectory() as d:
            trace=B.solve_trace(*args,deadline=time.monotonic()+10,log_path=str(Path(d)/'native.log'))
            self.assertIsInstance(trace['retained_log']['text'],str);C.verify_trace(trace,*args)
    def test_limits_and_bad_selection(self):
        args=([{'a':F(1)}],{'a':F(2)},['a'],[0,0],0,{'gram':1},[0])
        with self.assertRaises(OverflowError):B.assemble(*args,deadline=time.monotonic()+10,max_operations=1)
        with self.assertRaises(TimeoutError):B.assemble(*args,deadline=time.monotonic()-1)
        with self.assertRaises(ValueError):B.assemble(*args[:-1],[True],deadline=time.monotonic()+10)
        with self.assertRaises(ValueError):B.assemble([{'a':F(0)}],{},['a'],[0,0],0,{'gram':1},[0],deadline=time.monotonic()+10)

if __name__=='__main__':unittest.main()
