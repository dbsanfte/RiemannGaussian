import copy
import hashlib
import unittest
import time
from fractions import Fraction as F
import check_primitive_state_solver_trace as C
import test_check_primitive_state_numerical_proposals as existing

class TraceTests(unittest.TestCase):
    def fixture(self):
        rows,rhs,width,_,_,receipt=existing.IndependentNumericalAuditTests().fixture()
        system=dict(rows=[[[j,str(q)] for j,q in sorted(r.items())] for r in rows],rhs=list(map(str,rhs)),variables=width,
                    nonnegative_indices=[0],psd_blocks=[dict(name='one',size=1,indices=[1])],objective=[0.,0.])
        trace=dict(schema='primitive-state-solver-trace-v1',kind='primal',original_system=system,original_system_hash=C.digest(system),transformation_receipt=receipt,
                   original_vector=[2.,-1.],vector_role='raw_failed_last_iterate',solver=dict(name='synthetic',versions={'synthetic':'1'},versions_hash=C.digest({'synthetic':'1'}),options={'max_threads':1},options_hash=C.digest({'max_threads':1})),termination_status='failed',
                   retained_log=dict(text='fail\n',encoding='utf-8',retained_bytes=5,total_bytes=5,truncated=False,sha256=hashlib.sha256(b'fail\n').hexdigest()))
        scaled=dict(rows=[[[j,float(q/F(receipt['row_scales'][k]))] for j,q in sorted(rows[i].items())] for k,i in enumerate(receipt['retained_indices'])],rhs=[float(rhs[i]/F(receipt['row_scales'][k])) for k,i in enumerate(receipt['retained_indices'])],variables=width,objective=system['objective'])
        trace['scaled_original_system_hash']=C.digest(scaled)
        return trace,dict(rows=rows,rhs=rhs,n_variables=width)

    def test_recompute_failed_iterate(self):
        trace,args=self.fixture(); out=C.verify_trace(trace,**args)
        self.assertEqual(out['diagnostics']['equality_max_abs'],5.)
        self.assertEqual(out['diagnostics']['nonnegative_min'],2.)
        self.assertEqual(out['diagnostics']['psd_gershgorin'][0]['gershgorin_lower'],-1.)
        self.assertFalse(out['certified'])

    def test_missing_coordinates_and_failed_acceptance(self):
        for vector in ([2.],{0:2.},[2.,None],[2.,float('inf')]):
            trace,args=self.fixture();trace['original_vector']=vector
            with self.assertRaises((ValueError,TypeError)):C.verify_trace(trace,**args)
        trace,args=self.fixture();trace['vector_role']='accepted_proposal'
        with self.assertRaises(ValueError):C.verify_trace(trace,**args)

    def test_trusted_system_required(self):
        trace,_=self.fixture()
        with self.assertRaises(ValueError):C.verify_trace(trace)
        trace,args=self.fixture();args['rhs']=list(args['rhs']);args['rhs'][0]=F(9)
        with self.assertRaises(ValueError):C.verify_trace(trace,**args)

    def test_bindings_log_and_limits(self):
        for key,value in [('certified',True),('original_system_hash','bad'),('status',None)]:
            trace,args=self.fixture();trace[key]=value
            if key=='status':continue
            with self.assertRaises(ValueError):C.verify_trace(trace,**args)
        for key,value in [('retained_bytes',4),('total_bytes',4),('truncated',True),('sha256','bad')]:
            trace,args=self.fixture();trace['retained_log'][key]=value
            with self.assertRaises(ValueError):C.verify_trace(trace,**args)
        trace,args=self.fixture()
        with self.assertRaises(OverflowError):C.verify_trace(trace,**args,max_metric_cells=1)
        with self.assertRaises(ValueError):C.verify_trace(trace,**args,expected_options={'threads':2})

    def test_synthetic_compact_solver_integration(self):
        # Producer imports are restricted to this calibration test, never auditor.
        import primitive_state_solver_trace as producer
        columns=[{('x',):F(1)}]; monomials=[('x',)]
        trace=producer.trace_support(columns,{('x',):F(-1)},monomials,[0],[],
            deadline=time.monotonic()+10,max_rows=10,max_variables=10,max_work=450000000)
        out=C.verify_system_trace('support',columns,{('x',):F(-1)},monomials,trace,nonnegative=[0],relations=[])
        self.assertEqual(out['diagnostics']['equality_max_abs'],0.)
        self.assertTrue(out['canonical_system_independently_rebuilt'])
        trace=producer.trace_primal(columns,{('x',):F(2)},monomials,(0,0),0,{'gram':1},deadline=time.monotonic()+10)
        out=C.verify_system_trace('primal',columns,{('x',):F(2)},monomials,trace,shape=(0,0),offset=0,specs={'gram':1})
        self.assertEqual(out['diagnostics']['equality_max_abs'],0.)
        self.assertFalse(out['canonical_system_independently_rebuilt'])
        self.assertFalse(out['certified'])

    def test_compact_metadata_rebuild(self):
        trace,args=self.fixture();system=trace.pop('original_system')
        trace['original_system_metadata']={k:v for k,v in system.items() if k not in ('rows','rhs')}
        trace['original_system_metadata']['rows_count']=len(system['rows'])
        self.assertTrue(C.verify_trace(trace,**args)['verified'])
        trace['scaled_original_system_hash']='bad'
        with self.assertRaises(ValueError):C.verify_trace(trace,**args)

    def test_no_vector_is_explicit(self):
        trace,args=self.fixture();trace['original_vector']=None;trace['vector_role']='unavailable'
        self.assertIsNone(C.verify_trace(trace,**args)['diagnostics'])

if __name__=='__main__':unittest.main()
