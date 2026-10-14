from fractions import Fraction as F
import copy
import tempfile
import time
import unittest
from unittest.mock import patch
from types import SimpleNamespace
from pathlib import Path
import primitive_state_cached_primal_variants as P
import check_primitive_state_cached_primal_variants as C


def fixture():
    args=([{(0,):F(1)}],{(0,):F(2)},[(0,)],[0,0],0,{'gram':1},[0]);data,assembly=P.P.assemble(*args,deadline=time.monotonic()+20)
    cache,counts=P.encode_cache(data,assembly,*args,parent_bindings=dict(publication_report_hash='a',parent_trace_hash='b',parent_review_hash='c'),deadline=time.monotonic()+20)
    return args,cache

class CacheTests(unittest.TestCase):
    def test_exact_roundtrip_independent_canonical(self):
        args,cache=fixture();decoded,counts=P.decode_cache(cache,deadline=time.monotonic()+20)
        self.assertEqual(decoded['columns'],args[0]);self.assertEqual(decoded['data']['A'].toarray().tolist(),[[.5],[-1.]])
        check=C.verify_cache(cache);self.assertTrue(check['verified']);self.assertFalse(cache['certified'])
    def test_actual_native_options_and_raw_xyz(self):
        args,cache=fixture();decoded,_=P.decode_cache(cache,deadline=time.monotonic()+20)
        for variant in P.VARIANTS:
            binding=dict(cache_file_hash=P.P.digest(cache),**{k:cache[k] for k in ['original_source_hash','canonical_cache_hash','assembly_hash']})
            trace=P.solve_cached(decoded,cache,binding,variant['id'],deadline=time.monotonic()+20)
            self.assertEqual(trace['termination_status'],'Solved');self.assertEqual(trace['original_vector'],trace['raw_solution']['x']);self.assertIn('z',trace['raw_solution']);self.assertIn('s',trace['raw_solution'])
            self.assertTrue(C.verify_variant_trace(trace,cache,variant['id'])['verified'])
    def test_cache_file_bounds_and_hash(self):
        _,cache=fixture()
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'cache.json';path.write_bytes(P.P.encoded(cache));self.assertEqual(P.read_cache(path,expected_sha256=P.P.digest(cache))[0],cache)
            with self.assertRaises(OverflowError):P.read_cache(path,max_cache_bytes=1)
            with self.assertRaises(ValueError):P.read_cache(path,expected_sha256='0'*64)
    def test_tamper_and_limits(self):
        _,cache=fixture();bad=copy.deepcopy(cache);bad['canonical']['values'][0]='0x1.0p+0'
        with self.assertRaises(ValueError):P.decode_cache(bad,deadline=time.monotonic()+20)
        with self.assertRaises(OverflowError):P.decode_cache(cache,deadline=time.monotonic()+20,max_operations=1)
        with self.assertRaises(TimeoutError):P.decode_cache(cache,deadline=time.monotonic()-1)
        with self.assertRaises(ValueError):P.variant_spec('auto')
        with self.assertRaises(ValueError):P.settings('qdldl_default',901)

    def test_failed_native_keeps_unclipped_last_iterate(self):
        _,cache=fixture();decoded,_=P.decode_cache(cache,deadline=time.monotonic()+20)
        class Solver:
            def __init__(self,*a):pass
            def set_termination_callback(self,*a):pass
            def solve(self):raise RuntimeError('synthetic native failure')
            def get_solution(self):return SimpleNamespace(x=[-0.5],s=[0.,0.],z=[0.,0.],status='NumericalError',iterations=1)
            def get_info(self):return SimpleNamespace(status='NumericalError',iterations=1)
        binding=dict(cache_file_hash=P.P.digest(cache),**{k:cache[k] for k in ['original_source_hash','canonical_cache_hash','assembly_hash']})
        with patch('clarabel.DefaultSolver',Solver):trace=P.solve_cached(decoded,cache,binding,'qdldl_default',deadline=time.monotonic()+20)
        self.assertEqual(trace['original_vector'],[-0.5]);self.assertEqual(trace['vector_role'],'raw_failed_last_iterate');self.assertEqual(trace['error']['type'],'RuntimeError')
        self.assertTrue(C.verify_variant_trace(trace,cache,'qdldl_default')['verified'])
