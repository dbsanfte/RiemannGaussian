import copy
import json
from fractions import Fraction as F
from pathlib import Path
import time
import unittest
from unittest.mock import patch
import check_primitive_state_cone_jacobi_search as C
import test_check_primitive_state_free_cone_search as FIX


def fixture():
    old,seed=FIX.EndpointTests().fixture()
    seed.update(schema='primitive-state-free-cone-endpoint-v1',complete=True)
    summary=dict(old.summary,publication='publication-018',sparse_map_entries=1,parent_projected_hash=C.digest(seed['final_projected_vector']),parent_free_hash=C.digest(seed['final_free_vector']))
    lic=C._EndpointLicense(C._TOKEN,old,summary,old.parent_vector,{},seed)
    return lic,seed


def norms_fixture(lic,g='1',k=0):
    records=[dict(index=index,free_index=i,norm=g,exponent=k,scale=str(F(2**(-k))if k<=0 else F(1,2**k)),response_max_bits=1,norm_max_bits=max(F(g).numerator.bit_length(),F(g).denominator.bit_length())) for index,i in enumerate(lic.free)]
    return dict(schema='primitive-state-cone-jacobi-norms-v1',complete=True,status='scaled',normalized_basis_hash=lic.summary['normalized_basis_hash'],seed_endpoint_hash=C.digest(lic.parent_endpoint),scaling=C.SCALING,records=records,records_hash=C.digest(records),counts=dict(operations=1,peak_live_cells=1,fill_cells=1),**C.FLAGS)


class JacobiChecks(unittest.TestCase):
    def test_exact_dyadic_policy_boundary_and_zero(self):
        lic,_=fixture()
        for g,k in [('1',0),('1/4',-1),('4',1),('0',0),('5/4',1)]:
            out=C.verify_scaling(lic,norms_fixture(lic,g,k));self.assertTrue(out['positive_invertible_coordinate_change']);self.assertFalse(out['column_norms_independently_verified']);self.assertFalse(out['scaled_trace_bound_certified'])
        with self.assertRaises(ValueError):C.verify_scaling(lic,norms_fixture(lic,'1/4',0))
        with self.assertRaises(ValueError):C.verify_scaling(lic,norms_fixture(lic,'0',1))
    def test_scale_norm_bindings_caps_and_false_certification(self):
        lic,_=fixture();norm=norms_fixture(lic)
        for field,value in [('scale','0'),('scale','-1'),('exponent',True),('exponent',901),('norm','-1'),('free_index',-1),('norm','1/1')]:
            bad=copy.deepcopy(norm);bad['records'][0][field]=value;bad['records_hash']=C.digest(bad['records'])
            with self.assertRaises(ValueError):C.verify_scaling(lic,bad)
        for field in ('column_norms_independently_verified','scaled_trace_bound_certified','certified'):
            bad=copy.deepcopy(norm);bad[field]=True
            with self.assertRaises(ValueError):C.verify_scaling(lic,bad)
        bad=copy.deepcopy(norm);bad['records'].pop()
        with self.assertRaises(ValueError):C.verify_scaling(lic,bad)
        with self.assertRaises(OverflowError):C.verify_scaling(lic,norm,max_operations=1)
    def test_unknown_norm_prefix_nonadmission(self):
        lic,_=fixture();norm=norms_fixture(lic);norm.update(status='unknown',complete=False,reason='coefficient bit cap');norm['records']=norm['records'][:2];norm.pop('records_hash')
        out=C.verify_scaling(lic,norm);self.assertFalse(out['complete']);self.assertFalse(out['positive_invertible_coordinate_change'])
    def test_aggregate_diagnostic_can_be_limited_without_rejecting_scales(self):
        lic,_=fixture();norm=norms_fixture(lic)
        for i,d in enumerate(((1<<8190)+1,(1<<8190)+3)):
            q=F(d-1,d);norm['records'][i].update(norm=str(q),norm_max_bits=max(q.numerator.bit_length(),q.denominator.bit_length()))
        norm['records_hash']=C.digest(norm['records'])
        out=C.verify_scaling(lic,norm);self.assertTrue(out['complete']);self.assertIsNone(out['reported_scaled_diagonal_trace']);self.assertIn('8192',out['reported_trace_diagnostic_limit_reason'])
    def test_no_trust_boolean_endpoint_or_license(self):
        with self.assertRaises(ValueError):C.load_verified_license('.',{})
        with self.assertRaises(ValueError):C.verify_endpoint({'trusted':True},{})
    def test_exact018_seed_actual_binding_without_research(self):
        import check_primitive_state_free_cone_search_run as R
        names=set(R.INPUTS)|{C.MANIFEST,C.REPORT,C.PARENT+'/independent_verification.json',C.PARENT+'/receipt.json',C.PARENT+'/jobs/endpoint.json',C.PARENT+'/jobs/map.json',C.PARENT+'/jobs/check.json',C.PARENT+'/jobs/search-job.json'}
        root=Path(C.__file__).resolve().parent;bindings={n:R.sha(root/n)for n in names}
        with patch.object(C.EXACT,'replay_normalized_rows',side_effect=AssertionError('forbidden new elimination')):
            lic=C.load_verified_license(root,bindings,deadline=time.monotonic()+60)
        self.assertEqual((lic.summary['rank'],lic.summary['free_count']),(779,445));self.assertEqual(lic.summary['publication'],'publication-018');self.assertNotEqual(lic.summary['parent_candidate_hash'],lic.old.summary['parent_candidate_hash'])
        metadata=json.loads((root/(C.PARENT+'/jobs/map.json')).read_text())
        metadata.update(schema='primitive-state-cone-jacobi-map-v1',initial_free_vector=[str(lic.parent_vector[i])for i in lic.free],precision=C.PRECISION,seed_rule=C.SEED,seed_endpoint_hash=C.digest(lic.parent_endpoint),initial_projected_hash=C.digest(list(map(str,lic.parent_vector))),**C.FLAGS)
        self.assertGreater(len(C.encoded(metadata)),65536);self.assertLess(len(C.encoded(metadata)),131072)
        self.assertTrue(C.verify_map_receipt(lic,metadata)['published_chart_license_match'])
        bindings[C.PARENT+'/jobs/endpoint.json']='0'*64
        with self.assertRaises(ValueError):C.load_verified_license(root,bindings)

class ProducerIntegration(unittest.TestCase):
    def fixture(self):
        import primitive_state_cone_jacobi_search as P
        import test_check_primitive_state_triangular_restoration as T
        cache,trace,basis,projection,parent=T.FullRestorationTests().fixture()
        lic,seed=fixture()
        mapping,mapreceipt=P.materialize(cache,basis,projection,parent,seed,deadline=time.monotonic()+60)
        lic.summary['sparse_map_entries']=mapreceipt['sparse_map_entries']
        norms=P.cone_column_norms(mapping,deadline=time.monotonic()+60);P.install_scales(mapping,norms)
        proposal=P.propose(mapping,deadline=time.monotonic()+60,max_operations=80000000)
        endpoint=P.exact_endpoint(mapping,proposal,deadline=time.monotonic()+60)
        return lic,mapreceipt,norms,proposal,endpoint
    def test_complete_centered_trace_exact_endpoint(self):
        lic,m,n,p,e=self.fixture();out=C.verify_search(lic,m,n,p,e)
        self.assertTrue(out['endpoint_verified']);self.assertTrue(out['finite_candidate_feasible']);self.assertFalse(out['column_norms_independently_verified'])
        self.assertEqual(p['stop_reason'],'zero_gradient')
    def test_seed_coordinate_and_scale_trace_tampering(self):
        lic,m,n,p,e=self.fixture()
        for field,value in [('initial_z_mp',[[0,'1',0]]*len(lic.free)),('norm_records_hash','0'*64),('scale_vector',['0']*len(lic.free)),('final_free_vector',['1']*len(lic.free)),('seed_endpoint_hash','0'*64)]:
            bad=copy.deepcopy(p);bad[field]=value
            with self.assertRaises(ValueError):C.verify_search(lic,m,n,bad,e)
    def test_exact_centered_sum_can_exceed269bits(self):
        lic,_=fixture();lic.parent_vector[lic.free[0]]=F(1,2**1000)
        # The endpoint arithmetic is exact, not a new MP export. This explicit
        # sum needs1001 numerator bits even though both inputs need one bit.
        q=lic.parent_vector[lic.free[0]]+F(1)
        self.assertGreater(q.numerator.bit_length(),269)
        b=C.EXACT.EXACT._Budget(None,10000,10000,4096)
        self.assertEqual(C.EXACT.rational(str(q),b),q)
