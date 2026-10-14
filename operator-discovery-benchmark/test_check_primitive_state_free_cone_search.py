import copy
from fractions import Fraction as F
import time
import unittest
import check_primitive_state_free_cone_search as C
import test_check_primitive_state_triangular_restoration as FIXTURE


class EndpointTests(unittest.TestCase):
    def fixture(self,negative=False):
        cache,trace,basis,projection,receipt=FIXTURE.FullRestorationTests().fixture(negative)
        b=C.EXACT.EXACT._Budget(None,10000000,10000000,4096);source=C.CACHE_CHECK.decode_original(cache,b)
        pivots=basis['pivot_columns'];retained=projection['retained_indices'];free=[i for i in range(len(retained)) if i not in pivots]
        vec=list(map(F,receipt['restored_projected_vector']))
        summary=dict(normalized_basis_hash=receipt['normalized_basis_hash'],rank=len(pivots),free_count=len(free),retained_indices=retained)
        license=C._EndpointLicense(C._TOKEN,source,summary,vec,pivots,free,{})
        proposal=dict(normalized_basis_hash=receipt['normalized_basis_hash'],free_indices=free,candidate_hash=receipt['candidate_hash'],diagnostics=receipt['diagnostics'],final_free_vector=[str(vec[i]) for i in free],final_projected_vector=list(map(str,vec)),candidate_original_vector=receipt['candidate_original_vector'],**C.FLAGS)
        return license,proposal
    def test_endpoint_without_elimination(self):
        out=C.verify_endpoint(*self.fixture());self.assertTrue(out['endpoint_verified']);self.assertTrue(out['finite_candidate_feasible'])
        self.assertFalse(out['full_elimination_replayed']);self.assertTrue(out['licensed_affine_uniqueness'])
    def test_negative_cone_endpoint_affine_verified(self):
        out=C.verify_endpoint(*self.fixture(True));self.assertTrue(out['endpoint_verified']);self.assertFalse(out['finite_candidate_feasible'])
        self.assertFalse(out['infeasibility_proved']);self.assertFalse(out['exact_admission'])
    def test_original_equality_and_free_endpoint_tampering(self):
        license,proposal=self.fixture()
        for coordinate in (0,10):
            bad=copy.deepcopy(proposal);bad['candidate_original_vector'][coordinate]='1'
            if coordinate==0:bad['candidate_original_vector'][coordinate]='2'
            with self.assertRaises(ValueError):C.verify_endpoint(license,bad)
        bad=copy.deepcopy(proposal);bad['final_free_vector'][0]='2'
        with self.assertRaises(ValueError):C.verify_endpoint(license,bad)
    def test_no_missing_or_float_exact_coordinates(self):
        license,proposal=self.fixture()
        for key in ('candidate_original_vector','final_free_vector'):
            bad=copy.deepcopy(proposal);bad[key].pop()
            with self.assertRaises(ValueError):C.verify_endpoint(license,bad)
        bad=copy.deepcopy(proposal);bad['candidate_original_vector'][0]=1.0
        with self.assertRaises(ValueError):C.verify_endpoint(license,bad)
    def test_no_unbound_trust_shortcut(self):
        license,proposal=self.fixture()
        with self.assertRaises(ValueError):C.verify_endpoint({'trusted':True},proposal)
        with self.assertRaises(ValueError):C._EndpointLicense(None,None,None,None,None,None,None)
        with self.assertRaises(ValueError):C.load_verified_license('.',{})
    def test_actual_published_license_stem_bindings_without_elimination(self):
        from pathlib import Path
        from unittest.mock import patch
        root=Path(C.__file__).resolve().parent
        paths=[C.MANIFEST,C.REPORT,C.CACHE,C.BASIS,C.PROJECTION,*[C.PARENT+'/'+name for name in ('jobs/restoration.json','jobs/check.json','jobs/restoration-job.json','independent_verification.json','receipt.json')]]
        budget=C.EXACT.EXACT._Budget(None,10000000,10000000,4096)
        bindings={name:C._sha(root,name,budget) for name in paths}
        with patch.object(C.EXACT,'replay_normalized_rows',side_effect=AssertionError('forbidden repeat elimination')):
            license=C.load_verified_license(root,bindings,deadline=time.monotonic()+60)
        self.assertEqual((license.summary['rank'],license.summary['free_count']),(779,445))
        self.assertEqual((license.summary['original_rows'],license.summary['original_variables']),(5641,1957))
        self.assertIsNotNone(license.cache);self.assertIsNotNone(license.basis)
    def test_proof_claim_resource_and_noncanonical_rational(self):
        license,proposal=self.fixture();bad=copy.deepcopy(proposal);bad['certified']=True
        with self.assertRaises(ValueError):C.verify_endpoint(license,bad)
        bad=copy.deepcopy(proposal);bad['final_free_vector'][0]='0/2'
        with self.assertRaises(ValueError):C.verify_endpoint(license,bad)
        with self.assertRaises(TimeoutError):C.verify_endpoint(license,proposal,deadline=time.monotonic()-1)
        with self.assertRaises(OverflowError):C.verify_endpoint(license,proposal,max_operations=1)

class ProposalHistoryTests(unittest.TestCase):
    def fixture(self):
        import primitive_state_free_cone_search as P
        cache,trace,basis,projection,parent=FIXTURE.FullRestorationTests().fixture()
        mapping,mapreceipt=P.materialize(cache,basis,projection,parent,deadline=time.monotonic()+30)
        proposal=P.propose(mapping,deadline=time.monotonic()+30)
        license,_=EndpointTests().fixture()
        return license,proposal
    def test_bounded_complete_mixed_precision_history(self):
        license,proposal=self.fixture();out=C.verify_proposal_trace(license,proposal)
        self.assertTrue(out['complete']);self.assertTrue(out['proposal_history_only']);self.assertFalse(out['gradient_or_merit_certified'])
        self.assertEqual(out['native_PSD_projection_precision'],'binary64')
    def test_combined_map_proposal_endpoint_and_unknown(self):
        import primitive_state_free_cone_search as P
        cache,trace,basis,projection,parent=FIXTURE.FullRestorationTests().fixture()
        mapping,mapreceipt=P.materialize(cache,basis,projection,parent,deadline=time.monotonic()+30)
        proposal=P.propose(mapping,deadline=time.monotonic()+30);endpoint=P.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30)
        license,_=EndpointTests().fixture()
        out=C.verify_search(license,mapreceipt,proposal,endpoint)
        self.assertTrue(out['endpoint_verified']);self.assertTrue(out['finite_candidate_feasible']);self.assertFalse(out['full_elimination_replayed'])
        proposal.update(status='unknown',complete=False,reason='iteration cap')
        out=C.verify_search(license,mapreceipt,proposal,None);self.assertFalse(out['endpoint_verified']);self.assertIsNone(out['finite_candidate_feasible'])
        with self.assertRaises(ValueError):C.verify_search(license,mapreceipt,proposal,endpoint)
    def test_exact_initial_drift_tampering(self):
        license,proposal=self.fixture();proposal['calibration']['initial_forward_mp'][0]=[0,'3',0]
        with self.assertRaises(ValueError):C.verify_proposal_trace(license,proposal)
    def test_rehashed_protocol_mp_seed_and_decision_tampering(self):
        license,proposal=self.fixture()
        for kind in ('precision','seed','count','norm'):
            bad=copy.deepcopy(proposal)
            if kind=='precision':bad['precision']['decimal_digits']=40
            elif kind=='seed':bad['initial_free_mp'][0]=[0,'1',0]
            elif kind=='count':bad['counts']['operations']=0
            else:bad['iterations'][0]['gradient_squared_norm']=[0,'1',0]
            with self.assertRaises(ValueError):C.verify_proposal_trace(license,bad)
    def test_serialized_mp_limit_before_shift(self):
        budget=C.EXACT.EXACT._Budget(None,1000,1000,4096)
        for record in ([0,'1',1000000000],[0,'2',0],[True,'1',0],[1,'0',0],[0,'01',0]):
            with self.assertRaises(ValueError):C.mp_fraction(record,budget)
    def test_partial_proposal_never_endpoint_proof(self):
        license,proposal=self.fixture();proposal.update(status='unknown',complete=False,reason='proposalworkcap')
        proposal['iterations']=[];proposal['final_free_vector']=None
        out=C.verify_proposal_trace(license,proposal);self.assertFalse(out['complete']);self.assertFalse(out['exact_admission'])

if __name__=='__main__':unittest.main()
