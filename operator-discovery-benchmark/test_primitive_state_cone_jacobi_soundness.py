"""Independent synthetic soundness calibrations; no research-source replay."""
from fractions import Fraction as F
import time
import copy
from unittest.mock import patch
import unittest
import primitive_state_free_cone_search as BASE
import primitive_state_cone_jacobi_search as J
import check_primitive_state_cone_jacobi_search as AUDIT

class ConeJacobiSoundnessTests(unittest.TestCase):
    def budget(self):return BASE.EXACT.Budget(time.monotonic()+30,25000000,4000000,20000000,4096)
    def tiny(self):
        c=BASE.context()
        return dict(ctx=c,width=4,free=[1,3],pivots=[0,2],converted={0:{0:c.one,1:c.mpf(2),4:c.mpf(99)},2:{2:c.one,3:c.mpf(-1),4:c.mpf(-7)}})
    def test_homogeneous_rhs_omission_and_affine_difference(self):
        m=self.tiny();c=m['ctx'];d=list(map(c.mpf,[2,3]));zero=[c.zero,c.zero]
        linear,_=BASE.forward(m,d,self.budget(),linear=True)
        affine,_=BASE.forward(m,d,self.budget());center,_=BASE.forward(m,zero,self.budget())
        self.assertEqual(linear,list(map(c.mpf,[-4,2,3,3])))
        self.assertEqual(linear,[a-b for a,b in zip(affine,center)])
    def test_scaled_forward_adjoint_pairing(self):
        m=self.tiny();c=m['ctx'];D=[c.mpf(1)/8,c.mpf(16)];z=list(map(c.mpf,[2,3]));g=list(map(c.mpf,[5,7,11,13]))
        Nz,_=BASE.forward(m,[d*v for d,v in zip(D,z)],self.budget(),linear=True)
        NT=BASE.adjoint(m,g,self.budget());scaled=[d*v for d,v in zip(D,NT)]
        self.assertEqual(BASE.dot(c,Nz,g,self.budget()),BASE.dot(c,z,scaled,self.budget()))
        self.assertNotEqual(scaled,NT)
    def test_full_frobenius_offdiagonal_gradient_factor2(self):
        c=BASE.context();m=dict(ctx=c,width=2,scalar_indices=[],gram_pairs=[(0,1)],C_indices=[0],P_indices=[1])
        C=[[c.zero]*15 for _ in range(15)];H=[[c.zero]*15 for _ in range(15)]
        C[0][1]=C[1][0]=c.mpf(3);H[0][1]=H[1][0]=c.mpf(5)
        out=BASE.coordinate_gradient(m,[c.zero]*2,C,H,self.budget(),scalar_negative=False)
        self.assertEqual(out,[c.mpf(46),c.mpf(10)])
    def test_exact_center_plus_scaled_increment_exceeds269bits(self):
        c=BASE.context();center=BASE.record_fraction(BASE.mp_record(c.one));z=BASE.record_fraction(BASE.mp_record(c.power(2,-1000)))
        endpoint=center+z
        self.assertEqual(endpoint,F((1<<1000)+1,1<<1000));self.assertGreater(endpoint.numerator.bit_length(),269)
        self.assertNotEqual(BASE.record_fraction(BASE.mp_record(c.mpf(endpoint.numerator)/endpoint.denominator)),endpoint)
    def test_armijo_requires_scaled_coordinate_metric(self):
        # F(f)=f²/2, f=1, D=2; z-gradient=2, f-gradient=1.
        # alpha=1/2 gives f'=-1 and no improvement; neither norm admits it.
        # A synthetic merit0.85 exposes the different acceptance thresholds.
        alpha=F(1,2);before=F(1);after=F(17,20)
        proper=before-alpha*F(4)/8;wrong=before-alpha*F(1)/8
        self.assertFalse(after<=proper);self.assertTrue(after<=wrong)
    def test_actual_exact_scale_boundaries_and_zero(self):
        self.assertEqual(J.dyadic_scale(F(0)),(0,F(1)))
        for k in (-900,-3,-1,0,1,3,900):
            g=F(1<<(2*k)) if k>=0 else F(1,1<<(-2*k))
            expected=F(1,1<<k) if k>=0 else F(1<<(-k))
            self.assertEqual(J.dyadic_scale(g),(k,expected))
            if k<900:self.assertEqual(J.dyadic_scale(g+g/F(1000))[0],k+1)
        with self.assertRaises(ValueError):J.dyadic_scale(F(-1))
        with self.assertRaises(OverflowError):J.dyadic_scale(F(1<<1801))
        with self.assertRaises(OverflowError):J.dyadic_scale(F(1,1<<1802))
    def test_actual_exact_column_rhs_omission_and_norm_factor(self):
        m=dict(width=3,free=[1,2],pivots=[0],normalized={0:{0:F(1),1:F(2),3:F(999)}},scalar_indices=[0],gram_pairs=[(0,1)],C_indices=[1],P_indices=[2])
        x=J.homogeneous_response(m,1,self.budget())
        self.assertEqual(x,[F(-2),F(1),F(0)])
        # Scalar4 + offdiagonal C2 + H32 =38, not21 (missing duplication).
        norm,_=J.cone_norm(m,x,self.budget());self.assertEqual(norm,F(38))
        with self.assertRaises(OverflowError):J.homogeneous_response(m,1,BASE.EXACT.Budget(time.monotonic()+30,1,4000000,20000000,4096))
    def test_actual_scaled_actions_are_center_free_when_linear(self):
        m=self.tiny();c=m['ctx'];m.update(center_mp=[c.mpf(123),c.mpf(-321)],scale_mp=[c.mpf(1)/8,c.mpf(16)])
        z=list(map(c.mpf,[2,3]));g=list(map(c.mpf,[5,7,11,13]))
        x,_,_=J.scaled_forward(m,z,self.budget(),linear=True);adj=J.scaled_adjoint(m,g,self.budget())
        self.assertEqual(BASE.dot(c,x,g,self.budget()),BASE.dot(c,z,adj,self.budget()))
        self.assertEqual(x,list(map(c.mpf,['-0.5','0.25','48','48'])))
    def test_actual_scaled_power_operator_exact_curvature(self):
        m=self.tiny();c=m['ctx'];m.update(center_mp=[c.mpf(99),c.mpf(-77)],scale_mp=[c.mpf(1)/8,c.mpf(16)],scalar_indices=[1,3],gram_pairs=[(0,0)],C_indices=[0],P_indices=[2])
        value=J.power_operator(m,list(map(c.mpf,[2,3])),self.budget())
        self.assertEqual(value,[c.mpf(-1467)/32,c.mpf(1504)])
    def synthetic_scaling_license(self):
        old=AUDIT.OLD._EndpointLicense(AUDIT.OLD._TOKEN,None,dict(normalized_basis_hash='synthetic'),[F(1),F(-2)],[],[0,1],{})
        license=AUDIT._EndpointLicense(AUDIT._TOKEN,old,old.summary,old.parent_vector,{},dict(seed='synthetic018'))
        records=[]
        for i,g in enumerate((F(0),F(4))):
            k,d=J.dyadic_scale(g)
            records.append(dict(index=i,free_index=i,norm=str(g),exponent=k,scale=str(d),response_max_bits=3,norm_max_bits=max(g.numerator.bit_length(),g.denominator.bit_length())))
        receipt=dict(schema='primitive-state-cone-jacobi-norms-v1',status='scaled',complete=True,normalized_basis_hash='synthetic',seed_endpoint_hash=J.digest(license.parent_endpoint),scaling=J.SCALING,records=records,records_hash=J.digest(records),counts=dict(operations=100,peak_live_cells=10,fill_cells=10),**J.FLAGS)
        return license,receipt
    def test_independent_scale_flags_and_zero_negative_tampering(self):
        license,receipt=self.synthetic_scaling_license()
        result=AUDIT.verify_scaling(license,receipt)
        self.assertTrue(result['positive_invertible_coordinate_change'])
        self.assertFalse(result['column_norms_independently_verified'])
        self.assertFalse(result['scaled_trace_bound_certified'])
        for badscale in ('0','-1','1/4'):
            bad=copy.deepcopy(receipt);bad['records'][1]['scale']=badscale;bad['records_hash']=J.digest(bad['records'])
            with self.assertRaises(ValueError):AUDIT.verify_scaling(license,bad)
        for flag in ('column_norms_independently_verified','scaled_trace_bound_certified','exact_admission'):
            bad=copy.deepcopy(receipt);bad[flag]=True
            with self.assertRaises(ValueError):AUDIT.verify_scaling(license,bad)
        bad=copy.deepcopy(receipt);bad['records'][0]['exponent']=1;bad['records'][0]['scale']='1/2';bad['records_hash']=J.digest(bad['records'])
        with self.assertRaises(ValueError):AUDIT.verify_scaling(license,bad)
        bad=copy.deepcopy(receipt);bad['seed_endpoint_hash']='wrong017'
        with self.assertRaises(ValueError):AUDIT.verify_scaling(license,bad)
        with self.assertRaises(OverflowError):AUDIT.verify_scaling(license,receipt,max_operations=1)
    def synthetic_proposal(self):
        license,norm=self.synthetic_scaling_license();c=BASE.context();pairs=[(a,b) for a in range(15) for b in range(a,15)]
        free=[0,120];pivots=[i for i in range(240) if i not in free];parent=[F(0)]*240;parent[0]=F(1);parent[120]=F(-2)
        license.free=free;license.pivots=pivots;license.parent_vector=parent;license.source=dict(shape=[0,0],offset=0);license.summary['sparse_map_entries']=len(pivots)
        for item,j in zip(norm['records'],free):item['free_index']=j
        norm['records_hash']=J.digest(norm['records'])
        normalized={p:{p:F(1)} for p in pivots};converted={p:{p:c.one} for p in pivots}
        mapping=dict(ctx=c,width=240,free=free,pivots=pivots,normalized=normalized,converted=converted,scalar_indices=[],gram_pairs=pairs,C_indices=list(range(120)),P_indices=list(range(120,240)),initial=[F(1),F(-2)],parent_projected=parent,center_mp=[c.mpf(1),c.mpf(-2)],scales=[F(1),F(1,2)],scale_mp=[c.one,c.mpf(1)/2],normalized_basis_hash='synthetic',seed_endpoint_hash=J.digest(license.parent_endpoint),norm_records_hash=norm['records_hash'])
        mapping['norm_setup_counts']=dict(norm['counts'])
        proposal=J.propose(mapping,deadline=time.monotonic()+30,max_operations=80000000)
        return license,norm,mapping,proposal
    def test_actual_trace_false_flags_metric_center_and_final_tampering(self):
        license,norm,mapping,proposal=self.synthetic_proposal()
        self.assertTrue(proposal['complete'])
        out=AUDIT.verify_proposal_trace(license,norm,proposal)
        self.assertTrue(out['complete']);self.assertFalse(out['gradient_or_merit_certified'])
        for key,value in (('exact_admission',True),('column_norms_independently_verified',True),('initial_free_vector',['0','0']),('scale_vector',['1','0']),('final_free_vector',['2','-2'])):
            bad=copy.deepcopy(proposal);bad[key]=value
            with self.assertRaises(ValueError):AUDIT.verify_proposal_trace(license,norm,bad)
        bad=copy.deepcopy(proposal);bad['iterations'][0]['gradient_squared_norm']=[0,'1',0]
        with self.assertRaises(ValueError):AUDIT.verify_proposal_trace(license,norm,bad)
        with self.assertRaises(OverflowError):J.propose(mapping,deadline=time.monotonic()+30,max_operations=1)
    def test_nonzero_step_unscaled_trial_export_and_budget_stop_tampering(self):
        license,norm,mapping,_=self.synthetic_proposal();c=mapping['ctx']
        license.parent_vector=list(license.parent_vector);license.parent_vector[0]=F(-1);license.parent_vector[120]=F(2);mapping.update(initial=[F(-1),F(2)],parent_projected=license.parent_vector,center_mp=[c.mpf(-1),c.mpf(2)])
        proposal=J.propose(mapping,deadline=time.monotonic()+30,max_operations=80000000,max_trace_bytes=49152)
        self.assertTrue(proposal['complete']);self.assertEqual(proposal['stop_reason'],'budget_stop')
        self.assertTrue(proposal['iterations'])
        AUDIT.verify_proposal_trace(license,norm,proposal,max_trace_bytes=49152)
        bad=copy.deepcopy(proposal);bad['iterations'][0]['trials'][0]['approximate_free_mp'][0]=[0,'1',0]
        with self.assertRaises(ValueError):AUDIT.verify_proposal_trace(license,norm,bad,max_trace_bytes=49152)
        bad=copy.deepcopy(proposal);bad['budget_stop']['worst_iteration_work_reserve']=1
        with self.assertRaises(ValueError):AUDIT.verify_proposal_trace(license,norm,bad,max_trace_bytes=49152)
    def test_actual_endpoint_exact_sum_not_requantized(self):
        c=BASE.context();z=BASE.mp_record(c.power(2,-1000));free=F(1)+F(1,1<<1000)
        mapping=dict(width=1,free=[0],pivots=[],normalized={},initial=[F(1)],scales=[F(1)],seed_endpoint_hash='seed',norm_records_hash='norm',normalized_basis_hash='map',retained=[0],shape=[0,0],offset=0,specs={},n_variables=1,rows=[],rhs=[])
        proposal=dict(complete=True,status='proposed',seed_endpoint_hash='seed',norm_records_hash='norm',final_z_mp=[z],final_free_vector=[str(free)])
        # Isolate exact endpoint arithmetic; no mocked result counts as cone admission.
        with patch.object(J.EXACT,'canonical_lift',side_effect=lambda x,*args:list(x)),patch.object(J.EXACT,'candidate_diagnostics',return_value={}):
            endpoint=J.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30)
            self.assertEqual(endpoint['final_free_vector'],[str(free)])
            self.assertEqual(endpoint['final_projected_vector'],[str(free)])
            bad=copy.deepcopy(proposal);bad['final_free_vector']=['1']
            with self.assertRaises(ValueError):J.exact_endpoint(mapping,bad,deadline=time.monotonic()+30)
            with self.assertRaises(OverflowError):J.exact_endpoint(mapping,proposal,deadline=time.monotonic()+30,max_bits=999)
    def test_preallocation_operand_caps_reject_even_zero_product(self):
        m=dict(width=2,free=[1],pivots=[0],normalized={0:{0:F(1),1:F(1<<5000)}})
        with self.assertRaises(OverflowError):J.homogeneous_response(m,1,self.budget())
        cone=dict(scalar_indices=[0],gram_pairs=[],C_indices=[],P_indices=[])
        with self.assertRaises(OverflowError):J.cone_norm(cone,[F(1<<5000)],self.budget())
        with self.assertRaises(ValueError):J.cone_norm(cone,[F(1)],self.budget(),norm_bits=10**12)
    def test_actual_exponent_cap_parameter_prevalidation(self):
        for cap in (-1,0,901,10**12,True):
            with self.assertRaises(ValueError):J.dyadic_scale(F(1),exponent_abs_cap=cap)
    def test_record_caps_checked_before_extreme_exponent_shift(self):
        for exponent in (10**12,-10**12):
            with self.assertRaises(OverflowError):BASE.record_fraction([0,'1',exponent])

if __name__=='__main__':unittest.main()
