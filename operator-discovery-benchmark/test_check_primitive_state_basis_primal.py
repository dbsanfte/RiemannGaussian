import copy
from fractions import Fraction as F
import hashlib
import math
import time
import unittest
import check_primitive_state_basis_primal as I


class NativeAuditTests(unittest.TestCase):
    def fixture(self):
        columns=[{'a':F(2)},{'b':F(1)},{'b':F(2)},{'a':F(4)},{'c':F(1)}]
        source=(columns,{'a':F(6),'b':F(3)},['a','b','c'],[1,0],2,{'gram':2},[0,1])
        assembly=I.reconstruct(*source)['receipt'];assembly['limits']=dict(max_operations=50000000,max_cells=4000000,max_coefficient_bits=4096)
        x=[1.,-1.,2.,1.,3.];options=dict(max_threads=1,time_limit=5.)
        trace=dict(schema='primitive-state-basis-primal-v1',assembly=assembly,source_hashes={'source.py':'bound'},solver=dict(name='clarabel-native',versions={'clarabel':'synthetic'},versions_hash=I.digest({'clarabel':'synthetic'}),options=options,options_hash=I.digest(options)),
            raw_solution=dict(x=x,status='MaxIterations'),termination_status='MaxIterations',original_vector=x,vector_role='raw_failed_last_iterate',
            retained_log=dict(text='iteration\n',encoding='utf-8',retained_bytes=10,total_bytes=10,truncated=False,sha256=hashlib.sha256(b'iteration\n').hexdigest()),**I.FLAGS)
        return source,trace

    def test_canonical_independent_full_coordinate_assembly(self):
        source,trace=self.fixture();r=I.reconstruct(*source)
        expected=dict(variables=5,rows=[[[0,(1/3).hex()],[3,(2/3).hex()]],[[1,(1/3).hex()],[2,(2/3).hex()]],[[0,(-1.).hex()]],[[1,(-1.).hex()]],[[2,(-1.).hex()]],[[3,(-math.sqrt(2.)).hex()]],[[4,(-1.).hex()]]],rhs=[1..hex(),1..hex()]+[0..hex()]*5,objective=[1..hex(),0..hex(),1..hex(),0..hex(),1..hex()],cones=[['Zero',2],['Nonnegative',2],['PSDTriangle',2]])
        self.assertEqual(r['canonical_system'],expected);self.assertEqual(trace['assembly']['canonical_system_hash'],I.digest(expected))
        result=I.verify_trace(trace,*source);self.assertTrue(result['canonical_system_independently_rebuilt'])
        self.assertEqual(result['diagnostics']['equality_max_abs'],3.);self.assertEqual(result['diagnostics']['negative_scalar_count'],1)
        self.assertEqual(result['diagnostics']['objective'],6.);self.assertFalse(result['certified'])

    def test_psd_column_major_svec_order(self):
        source=([{'a':F(1)}]+[{} for _ in range(6)],{},['a'],[1,0],1,{'gram':3},[0])
        rows=I.reconstruct(*source)['canonical_system']['rows'][2:]
        self.assertEqual([row[0][0] for row in rows],[1,2,4,3,5,6])
        self.assertEqual([row[0][1] for row in rows],[(-1.).hex(),(-math.sqrt(2)).hex(),(-1.).hex(),(-math.sqrt(2)).hex(),(-math.sqrt(2)).hex(),(-1.).hex()])

    def test_assembly_tampering(self):
        source,trace=self.fixture()
        for key in ('original_system_hash','canonical_system_hash','layout_hash','selected_row_scales','selected_original_indices'):
            changed=copy.deepcopy(trace);changed['assembly'][key]='tampered'
            with self.subTest(key=key),self.assertRaises(ValueError):I.verify_trace(changed,*source)

    def test_complete_native_vector_no_clipping_or_missing_zeros(self):
        source,trace=self.fixture()
        for mode in ('clipped','missing','nan','bool','accepted'):
            changed=copy.deepcopy(trace)
            if mode=='clipped':changed['original_vector']=list(changed['original_vector']);changed['original_vector'][1]=0.
            elif mode=='missing':changed['original_vector'].pop()
            elif mode=='nan':changed['original_vector'][0]=float('nan')
            elif mode=='bool':changed['original_vector'][0]=True
            else:changed['vector_role']='accepted_proposal'
            with self.subTest(mode=mode),self.assertRaises(ValueError):I.verify_trace(changed,*source)

    def test_unavailable_vector_is_unknown(self):
        source,trace=self.fixture();trace.update(original_vector=None,vector_role='unavailable',raw_solution=None)
        result=I.verify_trace(trace,*source);self.assertIsNone(result['diagnostics']);self.assertEqual(result['mathematical_feasibility'],'UNKNOWN')

    def test_solver_status_options_versions_and_source_bindings(self):
        source,trace=self.fixture()
        for mode in ('status','threads','optionshash','versionshash','source'):
            changed=copy.deepcopy(trace);kwargs={}
            if mode=='status':changed['termination_status']='Solved'
            elif mode=='threads':changed['solver']['options']['max_threads']=2
            elif mode=='optionshash':changed['solver']['options_hash']='bad'
            elif mode=='versionshash':changed['solver']['versions_hash']='bad'
            else:kwargs['expected_source_hashes']={'other.py':'bound'}
            with self.subTest(mode=mode),self.assertRaises(ValueError):I.verify_trace(changed,*source,**kwargs)

    def test_logs_and_proof_flags(self):
        source,trace=self.fixture()
        for mode in ('bytes','hash','truncation','proof'):
            changed=copy.deepcopy(trace)
            if mode=='bytes':changed['retained_log']['retained_bytes']=9
            elif mode=='hash':changed['retained_log']['sha256']='bad'
            elif mode=='truncation':changed['retained_log']['truncated']=True
            else:changed['certified']=True
            with self.subTest(mode=mode),self.assertRaises(ValueError):I.verify_trace(changed,*source)

    def test_finite_failed_iterate_metric_overflow_remains_unknown(self):
        source,trace=self.fixture();x=[1e308]*5;trace.update(original_vector=x,raw_solution=dict(x=x,status='MaxIterations'))
        result=I.verify_trace(trace,*source)
        self.assertTrue(result['verified']);self.assertIsNone(result['diagnostics']['equality_max_abs']);self.assertEqual(result['diagnostics']['unknown_original_residual_count'],2)
        self.assertIsNone(result['diagnostics']['objective']);self.assertFalse(result['certified'])

    def test_resources_deadline_exact_domain(self):
        source,trace=self.fixture()
        for kwargs in [dict(max_operations=1),dict(max_cells=1),dict(max_coefficient_bits=1)]:
            with self.assertRaises(OverflowError):I.verify_trace(trace,*source,**kwargs)
        with self.assertRaises(TimeoutError):I.verify_trace(trace,*source,deadline=time.monotonic()-1)
        bad=list(source);bad[0]=copy.deepcopy(source[0]);bad[0][0]['outside']=F(1)
        with self.assertRaises(ValueError):I.verify_trace(trace,*bad)


if __name__=='__main__':unittest.main()
